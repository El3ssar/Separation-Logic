/* M14 — Optional — allocation
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m14",
  "num": "M14",
  "phase": "Phase 3 · Advanced separation logic",
  "title": "Optional — allocation",
  "blurb": "Adding malloc without destroying the frame rule.",

  "orient": {
    "youWill": [
      `Write the <code>alloc</code> constructor and point at the single implicit binder that makes execution nondeterministic.`,
      `Read the eight-line proof that under M6's triple you can specify <i>which</i> location the allocator returns — and replace that triple with one nobody can game.`,
      `Prove the small-footprint allocation rule, with the existential in the place the semantics forces it to be.`,
      `Refute <code>HeapLocal (.alloc x e)</code> with a two-cell heap, and prove the <b>frame property</b> — the same condition with the quantification reversed — instead.`,
      `Verify <code>alloc; write; load; free</code> against every run the allocator could have chosen, and watch the proof split into “pick a run” and “invert every run”.`
    ],
    "needs": [
      `M8's <code>HeapLocal</code> and <code>Preserves</code>, and the shape of <code>hoare_frame</code>'s proof. Most of this chapter is about how that one definition has to change.`,
      `M6's <code>Hoare</code>, and <code>exec_deterministic</code> — the theorem that dies first.`,
      `<code>union_eq_none</code>. The entire locality argument is one application of it.`,
      `M13's address-expression refactor, folded in here without further comment: <code>load : Var → Atom → Cmd</code>, <code>write : Atom → Atom → Cmd</code>, <code>free : Atom → Cmd</code>.`
    ],
    "payoff": `Every separation logic you will meet has an allocation rule with an existentially quantified pointer, and almost none of them say why. After this you can derive that design from the failure of one proof obligation, and name which half of locality your heap representation was quietly buying you.`
  },

  "blocks": [

    {
      "t": "note",
      "kind": "warn",
      "title": "This chapter changes the language, so it cannot quote the corpus",
      "h": `Lean's inductive types are closed: there is no <code>extend</code>, and no way to bolt a constructor onto <code>Cmd</code> after the fact. So everything below lives in <code>namespace M14</code>, where <code>Cmd</code>, <code>Exec</code>, <code>Hoare</code>, <code>HeapLocal</code> and <code>wp</code> are <i>redeclared</i> and shadow the M0–M13 versions. Heaps, assertions, <code>∗</code>, <code>emp</code>, <code>↦</code> — the whole of Phase 1 — are untouched and still in scope, which is a fair practical demonstration of M2's claim that the heap algebra does not know what a program is. Complete snippets below are tagged <b>illustration</b> and were checked under Lean 4.32.2 against everything through M13; fragments of a larger declaration are <b>sketch</b>; the one <b>verified</b> block is a quotation from the corpus, put there for comparison. If you reproduce this yourself, cut the last two blocks of <code>site/lean/prelude/m13.lean</code> first — they are M13's unproved address-expression sketch, and they will collide with what you write.`
    },

    {
      "t": "h3",
      "s": "One binder that nothing determines"
    },
    {
      "t": "p",
      "h": `<code>alloc x e</code> takes a cell that was not there before, puts the value of <code>e</code> in it, and tells you where through the variable <code>x</code>. The <i>where</i> is the entire difficulty. If the rule names the location, M8's refutation applies unchanged: framing alters which locations are already taken, so a command pinned to a named location is a command whose behaviour depends on memory it does not own.`
    },
    {
      "t": "p",
      "h": `Not naming it, in an inductive rule, means exactly one thing — leaving it as a binder that nothing outside the constructor constrains.`
    },
    {
      "t": "anat",
      "src": `  | alloc {s x e l} (hfresh : s.heap l = none) :
      Exec (.alloc x e) s ⟨Store.set s.store x l, Heap.write s.heap l (e.eval s.store)⟩`,
      "tag": "sketch",
      "cap": "One constructor lifted out of the <code>Exec</code> declaration; it is printed whole under exercise 1.",
      "parts": [
        {
          "m": "{s x e l}",
          "h": `Three of the four — <code>s</code>, <code>x</code>, <code>e</code> — are fixed the moment you know the starting state and the command. <code>l</code> is not. It occurs in the conclusion and nothing outside this constructor pins it. That one binder <i>is</i> the nondeterminism.`
        },
        {
          "m": "(hfresh : s.heap l = none)",
          "h": `The only constraint on <code>l</code>. Note what is absent: no “least such <code>l</code>”, no allocator state, no bump pointer. Any of those would make <code>Exec</code> a function again and hand back the counterexample this design exists to avoid.`
        },
        {
          "m": "Store.set s.store x l",
          "h": `The chosen location comes back through the store. Allocation is the one heap primitive that also writes a variable.`
        },
        {
          "m": "Heap.write s.heap l (e.eval s.store)",
          "h": `The heap grows by a cell. <code>Heap.write</code> is total and does not care whether the cell existed, which is precisely why freshness has to arrive as a separate hypothesis. On paper you say “extend the heap”; in Lean extension and overwrite are one operation, and the difference between them is <code>hfresh</code>.`
        }
      ]
    },
    {
      "t": "cmp",
      "left": {
        "t": "Every other constructor",
        "kind": "good",
        "h": `The final state is a <i>function</i> of the command and the starting state. <code>old</code> appears in the premise and never in the conclusion, so the outcome cannot depend on it. <code>load</code> looks like an exception — its implicit <code>v</code> does reach the conclusion — but its premise <code>s.heap (a.eval s.store) = some v</code> pins <code>v</code> to one value.`,
        "src": `  | write {s a e old} (hl : s.heap (a.eval s.store) = some old) :
      Exec (.write a e) s ⟨s.store, Heap.write s.heap (a.eval s.store) (e.eval s.store)⟩`,
        "tag": "sketch"
      },
      "right": {
        "t": "The alloc constructor",
        "h": `<code>l</code> reaches the conclusion and is constrained only by <code>hfresh</code>. Two applications with different <code>l</code> give two final states from one starting state. That is the whole disproof of <code>exec_deterministic</code>; everything else is bookkeeping around it.`,
        "src": `  | alloc {s x e l} (hfresh : s.heap l = none) :
      Exec (.alloc x e) s ⟨Store.set s.store x l, Heap.write s.heap l (e.eval s.store)⟩`,
        "tag": "sketch"
      }
    },

    {
      "t": "ex",
      "id": "m14-1",
      "name": "add nondeterministic allocation",
      "hard": false,
      "why": `Adding the constructor is one line. Writing the disproof is what makes the consequence concrete, and the disproof is the smallest object showing why a definition you wrote in M6 has quietly changed meaning.`,
      "setup": `Redeclare <code>Cmd</code> in a fresh <code>namespace</code> with the extra case, taking M13's address-expression refactor at the same time — you will need it, because after <code>alloc x e</code> the only handle on the new cell is the variable <code>x</code>. Then state and prove that <code>Exec</code> is no longer deterministic.`,
      "hints": [
        `Go through every existing constructor of <code>Exec</code> asking whether the final state is a function of the command and the starting state. Then write the alloc rule so that the answer becomes no, and identify the single binder responsible.`,
        `Do not try to negate <code>exec_deterministic</code> in place — negate its statement: <code>¬ ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂</code>.`,
        `For the witness take the empty heap, where every location is fresh, and run <code>alloc x (.const 0)</code> twice, choosing <code>0</code> once and <code>1</code> once. Lean cannot guess which you mean: write <code>Exec.alloc (l := 0) rfl</code>.`,
        `From the two states being equal, <code>congrArg (fun s => s.store x)</code> gives <code>Store.set … x 0 x = Store.set … x 1 x</code>, and <code>simp [Store.set]</code> takes it to <code>0 = 1</code>.`
      ],
      "expl": `The content is not the constructor but the refutation. Two derivations of the same command from the same state, differing in one named argument, ending in states that differ at a variable you can read.`,
      "walk": [
        {
          "tac": "intro hdet",
          "h": `Names the determinism assumption and leaves <code>⊢ False</code>.`
        },
        {
          "tac": "have h : (⟨Store.set (fun _ => 0) x 0, Heap.write Heap.empty 0 0⟩ : State) = …",
          "h": `Instantiate <code>hdet</code> at the empty heap with two runs of one command. The type ascription is not decoration: without it Lean displays the hypothesis as an unreduced pile of <code>{ store := … }.store</code> projections. Writing the type you want makes Lean check it up to definitional equality and then show you the readable form.`
        },
        {
          "tac": "  hdet (.alloc x (.const 0)) ⟨fun _ => 0, Heap.empty⟩ _ _",
          "h": `The two final states go in as <code>_ _</code>; the two <code>Exec</code> proofs that follow determine them.`
        },
        {
          "tac": "    (Exec.alloc (l := 0) rfl) (Exec.alloc (l := 1) rfl)",
          "h": `The same constructor twice, differing only in <code>l</code>. Freshness is <code>rfl</code> both times, since <code>Heap.empty l = none</code> holds by unfolding.`
        },
        {
          "tac": "have h01 := congrArg (fun s => s.store x) h",
          "h": `<code>congrArg f h</code> turns <code>a = b</code> into <code>f a = f b</code> — the companion of <code>congrFun</code>, applying one function to both sides of an equation rather than one equation at both sides of a point. Here <code>f</code> reads the store at <code>x</code>.`
        },
        {
          "tac": "simp [Store.set] at h01",
          "h": `Unfolds <code>Store.set</code>, evaluates both <code>if x = x</code> tests, lands on <code>(0 : Nat) = 1</code>, and recognises it as impossible.`
        }
      ],
      "deep": [
        {
          "t": "p",
          "h": `The language, with the alloc case and M13's address expressions folded in:`
        },
        {
          "t": "code",
          "src": `inductive Cmd where
  | skip
  | assign : Var  → Atom → Cmd
  | load   : Var  → Atom → Cmd
  | write  : Atom → Atom → Cmd
  | free   : Atom → Cmd
  | alloc  : Var  → Atom → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : BExpr → Cmd → Cmd → Cmd
  | loop   : BExpr → Cmd → Cmd`,
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": `inductive Exec : Cmd → State → State → Prop where
  | skip {s} : Exec .skip s s
  | assign {s x e} :
      Exec (.assign x e) s ⟨Store.set s.store x (e.eval s.store), s.heap⟩
  | load {s x a v} (hl : s.heap (a.eval s.store) = some v) :
      Exec (.load x a) s ⟨Store.set s.store x v, s.heap⟩
  | write {s a e old} (hl : s.heap (a.eval s.store) = some old) :
      Exec (.write a e) s ⟨s.store, Heap.write s.heap (a.eval s.store) (e.eval s.store)⟩
  | free {s a v} (hl : s.heap (a.eval s.store) = some v) :
      Exec (.free a) s ⟨s.store, Heap.erase s.heap (a.eval s.store)⟩
  | alloc {s x e l} (hfresh : s.heap l = none) :
      Exec (.alloc x e) s ⟨Store.set s.store x l, Heap.write s.heap l (e.eval s.store)⟩
  | seq {s s' s'' c₁ c₂} (h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'') :
      Exec (.seq c₁ c₂) s s''
  | iteTrue {s s' b c₁ c₂} (hb : b.eval s.store = true) (h : Exec c₁ s s') :
      Exec (.ite b c₁ c₂) s s'
  | iteFalse {s s' b c₁ c₂} (hb : b.eval s.store = false) (h : Exec c₂ s s') :
      Exec (.ite b c₁ c₂) s s'
  | loopFalse {s b c} (hb : b.eval s.store = false) :
      Exec (.loop b c) s s
  | loopTrue {s s' s'' b c} (hb : b.eval s.store = true)
      (hbody : Exec c s s') (hrest : Exec (.loop b c) s' s'') :
      Exec (.loop b c) s s''`,
          "tag": "illustration",
          "cap": "Ten constructors copied from M5, three addresses turned into <code>Atom</code>s, one new rule."
        },
        {
          "t": "code",
          "src": `theorem alloc_nondeterministic (x : Var) :
    ¬ ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂ := by
  intro hdet
  have h : (⟨Store.set (fun _ => 0) x 0, Heap.write Heap.empty 0 0⟩ : State)
         = ⟨Store.set (fun _ => 0) x 1, Heap.write Heap.empty 1 0⟩ :=
    hdet (.alloc x (.const 0)) ⟨fun _ => 0, Heap.empty⟩ _ _
      (Exec.alloc (l := 0) rfl) (Exec.alloc (l := 1) rfl)
  have h01 := congrArg (fun s => s.store x) h
  simp [Store.set] at h01`,
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "alloc_nondeterministic, tactic by tactic",
          "start": `x : Var
⊢ ¬∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂`,
          "steps": [
            {
              "tac": "intro hdet",
              "state": `x : Var
hdet : ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂
⊢ False`,
              "h": `Lean prints <code>¬∀</code> with no space.`
            },
            {
              "tac": "have h : … := hdet … (Exec.alloc (l := 0) rfl) (Exec.alloc (l := 1) rfl)",
              "state": `x : Var
hdet : ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂
h :
  { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 0 } =
    { store := Store.set (fun x => 0) x 1, heap := Heap.empty.write 1 0 }
⊢ False`,
              "h": `The whole theorem, visible: one command, one starting state, two different final states.`
            },
            {
              "tac": "have h01 := congrArg (fun s => s.store x) h",
              "state": `x : Var
hdet : ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂
h :
  { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 0 } =
    { store := Store.set (fun x => 0) x 1, heap := Heap.empty.write 1 0 }
h01 :
  { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 0 }.store x =
    { store := Store.set (fun x => 0) x 1, heap := Heap.empty.write 1 0 }.store x
⊢ False`,
              "h": `Lean has <i>not</i> performed <code>{ … }.store</code>. Projection out of a structure literal is left standing by the pretty-printer, and it is the single most common reason a goal in this chapter looks worse than it is. Drop the type ascription on <code>h</code> and it gets worse: the state literals themselves come back unreduced, and <code>h</code> is eight lines of <code>{ store := { store := fun x => 0, heap := Heap.empty }.store.set x 0, … }</code>.`
            },
            {
              "tac": "simp [Store.set] at h01",
              "state": `No goals.`,
              "h": `<code>simp</code> does perform the projection, and lands on <code>0 = 1</code>.`
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "The one casualty of working inside a namespace",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `In your own copy of the development you would edit the M5 definition and let the later files break — that is the exercise. Here M0–M13 have to keep compiling in the same file, so the new language is declared inside <code>namespace M14</code>, where <code>Cmd</code> means <code>M14.Cmd</code> and <code>_root_.Cmd</code> means the old one.`
            },
            {
              "t": "p",
              "h": `The casualty: <code>;;</code> is notation for <code>_root_.Cmd.seq</code>, so every snippet below writes <code>.seq</code> out longhand.`
            }
          ]
        }
      ],
      "pitfall": `<code>Exec.alloc rfl</code> on its own fails. Offer <code>refine ⟨_, Exec.alloc rfl⟩</code> against a <code>Safe</code> goal and you get three errors at once, one per unknown: “don't know how to synthesize implicit argument <code>l</code>” with <code>⊢ Val</code>; “don't know how to synthesize implicit argument <code>a</code>” with <code>⊢ Option Val</code>, which is <code>rfl</code>'s own implicit — Lean cannot tell you <i>what</i> is equal to <i>what</i>; and “don't know how to synthesize placeholder for argument <code>w</code>” with <code>⊢ State</code>, the <code>_</code> you wrote for the final state. Implicits come from the expected type, and the expected type here is an existential whose witness is itself a metavariable, so the three unknowns hold each other up. Name one and the deadlock breaks: <code>Exec.alloc (l := 0) rfl</code>. <code>Exec.load</code> and <code>Exec.free</code> bite the same way — supply <code>(v := w)</code>.`,
      "variants": `Constrain the choice and determinism comes back. Add <code>(hleast : ∀ k, k &lt; l → s.heap k ≠ none)</code> to the constructor and <code>exec_deterministic</code> is provable again: invert both runs, take <code>Nat.lt_trichotomy l₁ l₂</code>, and in each strict branch one run's <code>hleast</code> contradicts the other's <code>hfresh</code>. Nothing else needs touching, since every other constructor was already a function of its input. And the frame rule dies on the spot, because the least free location of <code>h</code> and the least free location of <code>h ∪ hFrame</code> need not be the same. That is the trade at its sharpest: determinism and locality are not both available. Real allocators <i>are</i> deterministic; separation logic keeps the frame rule by refusing to expose that determinism — the pointer is existentially quantified and the allocator's state never appears in an assertion.`
    },

    {
      "t": "h3",
      "s": "What ∃ s' means once there is more than one s'"
    },
    {
      "t": "p",
      "h": `M6 read <code>Hoare P c Q</code> as “from any <code>P</code>-state there <i>exists</i> a final state, and it satisfies <code>Q</code>”. While <code>Exec</code> was a partial function, “there is a good outcome” and “all outcomes are good” were the same sentence, and M6 never had to choose between them. They are not the same sentence any more, and M6 picked the wrong one.`
    },
    {
      "t": "p",
      "h": `Splitting them needs a name for “does not get stuck”, which the old <code>∃ s'</code> was carrying as a side effect. Give it one:`
    },
    {
      "t": "code",
      "src": `def Safe (c : Cmd) (s : State) : Prop := ∃ s', Exec c s s'`,
      "tag": "illustration",
      "cap": "There is at least one run. Nothing about where it ends."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Angelic — M6's definition, unchanged",
        "kind": "bad",
        "h": `“There is a run that lands in <code>Q</code>.” The prover chooses the run, so the prover chooses the location.`,
        "src": `def AngelicHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap`,
        "tag": "illustration"
      },
      "right": {
        "t": "Demonic — safety plus universal correctness",
        "kind": "good",
        "h": `“At least one run exists, and <i>every</i> run lands in <code>Q</code>.” The second conjunct is M13's <code>PartialHoare</code> up to the order of binders — there <code>s'</code> arrives before the proof of <code>P</code>, here after.`,
        "src": `def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h, P σ h →
    Safe c ⟨σ, h⟩ ∧ ∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap`,
        "tag": "illustration"
      }
    },
    {
      "t": "p",
      "h": `The angelic reading is not weaker only in principle. It lets you specify <i>which</i> location the allocator returns — the one thing the free binder was put there to prevent — and the proof is eight lines, none of them clever:`
    },
    {
      "t": "code",
      "src": `theorem angelic_alloc_names_zero (x : Var) (v : Val) :
    AngelicHoare emp (.alloc x (.const v)) (pure (fun σ => σ x = 0) ∗ (0 ↦ v)) := by
  intro σ h he
  subst he
  refine ⟨⟨Store.set σ x 0, Heap.write Heap.empty 0 v⟩, Exec.alloc (l := 0) rfl, ?_⟩
  refine ⟨Heap.empty, Heap.singleton 0 v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩
  · show Heap.write Heap.empty 0 v = Heap.union Heap.empty (Heap.singleton 0 v)
    rw [union_empty_left, write_empty]
  · show Store.set σ x 0 x = 0
    simp [Store.set]`,
      "tag": "illustration",
      "cap": "True, and useless. Nothing is wrong with the proof; what is wrong is the definition it satisfies."
    },
    {
      "t": "p",
      "h": `A specification provable because the prover picks the run is not a specification of the program. Switch to the demonic reading and the two conjuncts pull in opposite directions: <code>Safe</code> lets you name a location, <code>∀ s'</code> takes the naming away again, and the existential in the postcondition stops being a matter of taste.`
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "One thing you get back for free",
      "h": `M13 promised that <code>partial_of_total</code> would not survive this chapter. It does not need to: under the demonic definition, partial correctness <i>is</i> the second conjunct, so the theorem is <code>fun σ hh s' hp hex => (h σ hh hp).2 s' hex</code> — reorder the binders and project. The workbook's only use of <code>exec_deterministic</code> is gone, and what replaces it is shorter than what it replaces.`
    },

    {
      "t": "ex",
      "id": "m14-2",
      "name": "small-footprint alloc rule",
      "hard": false,
      "why": `Twelve lines, nine of them plumbing. What matters is the two obligations the demonic triple splits into, and the fact that the existential in the postcondition is not a stylistic choice — it is the only thing the second obligation will let you write.`,
      "setup": `Adopt the demonic <code>Hoare</code>, then state and prove the small-footprint rule for allocation. First prove <code>Heap.write Heap.empty l v = Heap.singleton l v</code>: allocation makes its cell with <code>write</code>, <code>↦</code> is defined with <code>singleton</code>, and nothing in the library yet bridges the two.`,
      "hints": [
        `Write the demonic definition out. Two conjuncts: the command is not stuck, and every run lands in <code>Q</code>. Now look at the postcondition you were going to write and ask which conjunct forbids naming the location.`,
        `Safety on <code>emp</code> is trivial — in the empty heap every location is free, so any witness will do: <code>⟨_, Exec.alloc (l := 0) rfl⟩</code>.`,
        `For the correctness half, <code>intro s' hex</code> then <code>cases hex</code>. Inversion introduces the allocator's choice as a fresh variable — name it with <code>| @alloc _ _ _ l hfresh =></code> — and that variable is the witness you feed to <code>aExists</code>.`,
        `What remains is a <code>∗</code>, so supply the six-tuple, splitting the heap as <code>Heap.empty ∪ Heap.singleton l v</code>. The <code>pure</code> conjunct is <code>⟨_, rfl⟩</code>.`
      ],
      "expl": `Precondition <code>emp</code>, postcondition owning exactly one cell: the smallest footprint there is, which is what makes the rule composable. The existential is forced by <code>∀ s'</code> — you must satisfy the postcondition for the location the allocator chose, not for one you chose — and the <code>pure</code> conjunct is how the caller connects that location back to <code>x</code>.`,
      "walk": [
        {
          "tac": "intro σ h hpre",
          "h": `The goal becomes the conjunction <code>Safe … ∧ ∀ s' …</code>.`
        },
        {
          "tac": "obtain ⟨hv, he⟩ := hpre",
          "h": `The precondition is <code>aAnd (fact …) emp</code>: <code>hv</code> pins the value, <code>he</code> pins the heap.`
        },
        {
          "tac": "subst he",
          "h": `<code>emp</code> is an equation with a bare variable on one side, so <code>h</code> goes. Everything now mentions <code>Heap.empty</code> literally, which is what makes the freshness proof <code>rfl</code>.`
        },
        {
          "tac": "refine ⟨⟨_, Exec.alloc (l := 0) rfl⟩, ?_⟩",
          "h": `Discharges safety. The outer pair is the conjunction, the inner one the existential inside <code>Safe</code>; the final state is <code>_</code> because <code>Exec.alloc</code> determines it.`
        },
        {
          "tac": "intro s' hex",
          "h": `The universal half. <code>s'</code> is <i>any</i> final state. You are no longer allowed to choose.`
        },
        {
          "tac": "cases hex with",
          "h": `Only one constructor can produce an execution of <code>.alloc x e</code>, so there is a single branch — and that branch comes with the allocator's choice as a new variable.`
        },
        {
          "tac": "| @alloc _ _ _ l hfresh =>",
          "h": `The three underscores are <code>s</code>, <code>x</code>, <code>e</code>, already determined. <code>l</code> is the one you need a name for; without <code>@</code> it arrives inaccessible and you cannot write the witness.`
        },
        {
          "tac": "refine ⟨l, Heap.empty, Heap.singleton l v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩",
          "h": `Seven components: the existential witness <code>l</code>, then the star's six slots. The <code>pure</code> proof is itself a pair, hence the nested <code>⟨?_, rfl⟩</code>.`
        },
        {
          "tac": "· show Heap.write Heap.empty l (e.eval σ) = Heap.union Heap.empty (Heap.singleton l v)",
          "h": `The same proposition with the state projections performed.`
        },
        {
          "tac": "  rw [union_empty_left, write_empty, show e.eval σ = v from hv]",
          "h": `Kill the union with <code>emp</code>, turn the write on the empty heap into a singleton, replace the evaluated expression by the value the precondition pinned. The inline <code>show … from hv</code> is how you use <code>hv</code> as a rewrite rule when its type is stated through <code>fact</code>.`
        },
        {
          "tac": "· show Store.set σ x l x = l",
          "h": `The remaining <code>pure</code> fact: the variable now holds the location.`
        },
        {
          "tac": "  simp [Store.set]",
          "h": `Unfolds the update and evaluates <code>if x = x</code>.`
        }
      ],
      "deep": [
        {
          "t": "p",
          "h": `The heap lemma first. Without it every alloc proof stalls where a <code>write</code> has to become a <code>↦</code>:`
        },
        {
          "t": "code",
          "src": `theorem write_empty (l : Loc) (v : Val) :
    Heap.write Heap.empty l v = Heap.singleton l v := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.empty, Heap.singleton, hx]`,
          "tag": "illustration"
        },
        {
          "t": "p",
          "h": `Unfolding <code>Heap.write</code> and <code>Heap.singleton</code> leaves an <code>if x = l</code> on each side. In the positive branch <code>hx</code> is in the simp set, both tests reduce to true, and the goal becomes <code>some v = some v</code>; in the negative branch both reduce to false, <code>Heap.empty</code> unfolds, and the goal becomes <code>none = none</code>. M1 observed that these two heaps coincide on unfolding. This is the lemma that lets you say so inside a <code>rw</code>.`
        },
        {
          "t": "code",
          "src": `def Safe (c : Cmd) (s : State) : Prop := ∃ s', Exec c s s'

def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h, P σ h →
    Safe c ⟨σ, h⟩ ∧ ∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap`,
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": `theorem hoare_alloc (x : Var) (e : Atom) (v : Val) :
    Hoare (aAnd (fact (fun σ => e.eval σ = v)) emp) (.alloc x e)
      (aExists fun l => pure (fun σ => σ x = l) ∗ (l ↦ v)) := by
  intro σ h hpre
  obtain ⟨hv, he⟩ := hpre
  subst he
  refine ⟨⟨_, Exec.alloc (l := 0) rfl⟩, ?_⟩
  intro s' hex
  cases hex with
  | @alloc _ _ _ l hfresh =>
      refine ⟨l, Heap.empty, Heap.singleton l v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩
      · show Heap.write Heap.empty l (e.eval σ) = Heap.union Heap.empty (Heap.singleton l v)
        rw [union_empty_left, write_empty, show e.eval σ = v from hv]
      · show Store.set σ x l x = l
        simp [Store.set]`,
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "hoare_alloc, tactic by tactic",
          "start": `x : Var
e : Atom
v : Val
⊢ Hoare (aAnd (fact fun σ => Atom.eval σ e = v) emp) (Cmd.alloc x e)
    (aExists fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v)`,
          "steps": [
            {
              "tac": "intro σ h hpre",
              "state": `x : Var
e : Atom
v : Val
σ : Store
h : Heap
hpre : aAnd (fact fun σ => Atom.eval σ e = v) emp σ h
⊢ Safe (Cmd.alloc x e) { store := σ, heap := h } ∧
    ∀ (s' : State),
      Exec (Cmd.alloc x e) { store := σ, heap := h } s' →
        aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap`,
              "h": `The two obligations, side by side.`
            },
            {
              "tac": "obtain ⟨hv, he⟩ := hpre",
              "state": `x : Var
e : Atom
v : Val
σ : Store
h : Heap
hv : fact (fun σ => Atom.eval σ e = v) σ h
he : emp σ h
⊢ Safe (Cmd.alloc x e) { store := σ, heap := h } ∧
    ∀ (s' : State),
      Exec (Cmd.alloc x e) { store := σ, heap := h } s' →
        aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap`,
              "h": `<code>he</code> displays as <code>emp σ h</code>, not as <code>h = Heap.empty</code>. <code>subst</code> sees through the definition anyway.`
            },
            {
              "tac": "subst he",
              "state": `x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
⊢ Safe (Cmd.alloc x e) { store := σ, heap := Heap.empty } ∧
    ∀ (s' : State),
      Exec (Cmd.alloc x e) { store := σ, heap := Heap.empty } s' →
        aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap`,
              "h": `<code>h</code> has left the context entirely.`
            },
            {
              "tac": "refine ⟨⟨_, Exec.alloc (l := 0) rfl⟩, ?_⟩",
              "state": `x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
⊢ ∀ (s' : State),
    Exec (Cmd.alloc x e) { store := σ, heap := Heap.empty } s' →
      aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap`,
              "h": `Safety discharged. What is left is exactly <code>PartialHoare</code>.`
            },
            {
              "tac": "intro s' hex",
              "state": `x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
s' : State
hex : Exec (Cmd.alloc x e) { store := σ, heap := Heap.empty } s'
⊢ aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap`,
              "h": `The moment the existential becomes unavoidable: you have no idea which location is in <code>s'</code>.`
            },
            {
              "tac": "cases hex with | @alloc _ _ _ l hfresh =>",
              "state": `case alloc
x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
l : Val
hfresh : { store := σ, heap := Heap.empty }.heap l = none
⊢ aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v)
    { store := { store := σ, heap := Heap.empty }.store.set x l,
        heap :=
          { store := σ, heap := Heap.empty }.heap.write l (Atom.eval { store := σ, heap := Heap.empty }.store e) }.store
    { store := { store := σ, heap := Heap.empty }.store.set x l,
        heap :=
          { store := σ, heap := Heap.empty }.heap.write l (Atom.eval { store := σ, heap := Heap.empty }.store e) }.heap`,
              "h": `There is <code>l</code>, the allocator's choice. It is displayed at type <code>Val</code> though it is being used as an address — the printer picks either name freely, and nothing turns on it. The goal is unreadable for one reason: <code>{ store := … }.store</code> has not been performed.`
            },
            {
              "tac": "refine ⟨l, Heap.empty, Heap.singleton l v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩",
              "state": `case alloc.refine_1
x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
l : Val
hfresh : { store := σ, heap := Heap.empty }.heap l = none
⊢ { store := { store := σ, heap := Heap.empty }.store.set x l,
        heap :=
          { store := σ, heap := Heap.empty }.heap.write l
            (Atom.eval { store := σ, heap := Heap.empty }.store e) }.heap =
    Heap.empty.union (Heap.singleton l v)`,
              "h": `Four of the seven went in without leaving a hole: <code>l</code>, the two heaps, and the disjointness. This is the union equation.`
            },
            {
              "tac": "show Heap.write Heap.empty l (e.eval σ) = Heap.union Heap.empty (Heap.singleton l v)",
              "state": `case alloc.refine_1
x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
l : Val
hfresh : { store := σ, heap := Heap.empty }.heap l = none
⊢ Heap.empty.write l (Atom.eval σ e) = Heap.empty.union (Heap.singleton l v)`,
              "h": `Same proposition, one line instead of five. Whenever inversion leaves you staring at record projections, this is the tool: projection out of a literal is a definitional step, so the <code>show</code> always succeeds — it simply never happens on its own.`
            },
            {
              "tac": "rw [union_empty_left, write_empty, show e.eval σ = v from hv]",
              "state": `case alloc.refine_2
x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
l : Val
hfresh : { store := σ, heap := Heap.empty }.heap l = none
⊢ fact (fun σ => σ x = l)
    { store := { store := σ, heap := Heap.empty }.store.set x l,
        heap :=
          { store := σ, heap := Heap.empty }.heap.write l (Atom.eval { store := σ, heap := Heap.empty }.store e) }.store
    Heap.empty`,
              "h": `First goal closed. The second is the <code>pure</code> fact, in the same projected shape. <code>fact φ σ h</code> ignores its heap argument, which is why <code>Heap.empty</code> is sitting there doing nothing.`
            },
            {
              "tac": "show Store.set σ x l x = l",
              "state": `case alloc.refine_2
x : Var
e : Atom
v : Val
σ : Store
hv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty
l : Val
hfresh : { store := σ, heap := Heap.empty }.heap l = none
⊢ σ.set x l x = l`,
              "h": `Three reductions in one step — unfold <code>fact</code>, perform the projection, drop the heap argument — none of which any tactic was asked to do.`
            },
            {
              "tac": "simp [Store.set]",
              "state": `No goals.`,
              "h": `Ask <code>simp?</code> and it reports <code>simp only [Store.set, ↓reduceIte]</code>.`
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why the postcondition names a <code>Val</code> and not an expression",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `The obvious statement writes the postcondition as <code>aExists fun l => pure (fun σ => σ x = l) ∗ (l ↦ e.eval σ)</code>. Look at the two <code>σ</code>s. The inner <code>fun σ</code> binds only the body of <code>pure</code>; the <code>σ</code> in <code>e.eval σ</code> is bound by nothing. Lean accepts it anyway, because auto-bound implicits quietly close it up — <code>#check</code> then reports <code>∀ {x : Var} {e : Atom} {σ : Store}, Hoare emp (Cmd.alloc x e) …</code>. That <code>σ</code> is fixed before the command runs, so the postcondition describes the new cell in a store nobody was ever in.`
            },
            {
              "t": "p",
              "h": `Bind it the way you meant — make <code>σ</code> the assertion's own store argument — and it is still wrong, now for a reason about the language. An assertion is a function of the <i>final</i> store, so <code>e.eval σ</code> means “evaluate <code>e</code> after the allocation”, and allocation writes <code>x</code>. Take <code>e = .var x</code>: the specification asks for a cell holding the final value of <code>x</code>, which is the location; the semantics wrote <code>e.eval s.store</code> in the state before the update, which is the old <code>σ x</code>. Run <code>alloc x (.var x)</code> from the everywhere-zero store and let the allocator pick <code>1</code>: the heap ends as <code>1 ↦ 0</code> and the postcondition demands <code>1 ↦ 1</code>. Not merely unprovable — false, and the demonic reading is what lets you say so.`
            },
            {
              "t": "p",
              "h": `The repair is M9's: pin the value with a pure side condition in the precondition, so the postcondition mentions a <code>Val</code> and never re-evaluates an expression. That is where <code>aAnd (fact (fun σ => e.eval σ = v)) emp</code> comes from. The other repair — add a substitution operator to the assertion language — is what real developments do, and it costs a chapter.`
            },
            {
              "t": "code",
              "src": `theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :
    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v)`,
              "tag": "verified",
              "cap": "The same trick, five chapters earlier."
            }
          ]
        }
      ],
      "pitfall": `Proving the triple with the location named — postcondition <code>pure (fun σ => σ x = 0) ∗ (0 ↦ v)</code> — and finding that it <i>works</i>. It works under the angelic definition, and the fact that it works is the bug. If your alloc rule went through without your ever writing <code>aExists</code>, check which <code>Hoare</code> is in scope before you celebrate.`,
      "variants": `Drop the existential and the theorem is demonically false: fix the location to <code>0</code>, take the run in which the allocator picks <code>1</code>, and the postcondition fails. Drop the <code>fact</code> guard on the value and you are back to the statement the aside above dismantles. Strengthen the precondition from <code>emp</code> to <code>l₀ ↦ u</code> and the rule survives, but neither for free nor unchanged: the postcondition has to grow the cell back — <code>aExists fun l => (pure (fun σ => σ x = l) ∗ (l ↦ v)) ∗ (l₀ ↦ u)</code> — and to build that star you must first derive <code>l ≠ l₀</code> out of <code>hfresh</code>, since <code>l = l₀</code> would make <code>Heap.singleton l₀ u l = none</code> contradict <code>singleton_same</code>. Safety stops being free too, because <code>l₀</code> may be <code>0</code>: you exhibit <code>l₀ + 1</code> and discharge freshness with <code>singleton_other</code>. It all goes through, and it is all the frame rule being re-derived by hand for one particular frame.`
    },

    {
      "t": "h3",
      "s": "Locality was two conditions all along"
    },
    {
      "t": "p",
      "h": `M8's <code>HeapLocal</code> hands you a run on the small heap and asks for the matching run on the big one. For allocation the <i>first</i> conjunct is already false, before the big heap is mentioned at all: the small run may have taken a cell the frame owns, and then its result is disjoint from nothing. Give the small heap <code>Heap.empty</code>, the frame <code>Heap.singleton 0 w</code>, and let the allocator choose <code>0</code>.`
    },
    {
      "t": "p",
      "h": `The repair is not to weaken the condition but to reverse the arrow.`
    },
    {
      "t": "cmp",
      "left": {
        "t": "Small → big (M8's <code>HeapLocal</code>)",
        "kind": "bad",
        "h": `You are handed a run on <code>h</code> and must produce a matching run on <code>h ∪ hFrame</code>. For <code>alloc</code> there is nothing to produce.`,
        "src": `    Exec c ⟨σ, h⟩ s' →
    Heap.disjoint s'.heap hFrame ∧
    ∃ r, Exec c ⟨σ, Heap.union h hFrame⟩ r ∧ …`,
        "tag": "sketch"
      },
      "right": {
        "t": "Big → small (the <b>frame property</b>)",
        "kind": "good",
        "h": `You are handed a run on <code>h ∪ hFrame</code> and must produce the matching run on <code>h</code>. Now it works: a location fresh in the union is fresh in <code>h</code>, so the small heap can make the same choice.`,
        "src": `    Exec c ⟨σ, Heap.union h hFrame⟩ r →
    ∃ s', Exec c ⟨σ, h⟩ s' ∧
      Heap.disjoint s'.heap hFrame ∧ …`,
        "tag": "sketch"
      }
    },
    {
      "t": "p",
      "h": `Reversing it costs nothing, because M8 was only ever using it in one direction. Its <code>hoare_frame</code> was <i>handed</i> a small run by the small triple and had to <i>produce</i> the big one, which is small → big and nothing else. The demonic triple turns that around for the correctness half — you are handed an arbitrary big run and must relate it to a small one — and leaves a second, much weaker demand behind for the safety half: some big run has to exist. Existence only, no shape. That deserves its own name.`
    },
    {
      "t": "code",
      "src": `def SafetyMonotone (c : Cmd) : Prop :=
  ∀ σ h hFrame, Heap.disjoint h hFrame → Safe c ⟨σ, h⟩ → Safe c ⟨σ, Heap.union h hFrame⟩

theorem alloc_not_safetyMonotone (x : Var) (v : Val) :
    ¬ SafetyMonotone (.alloc x (.const v)) := by
  intro hmono
  obtain ⟨r, hex⟩ :=
    hmono (fun _ => 0) Heap.empty (fun _ => some 0)
      (disjoint_empty_left _) ⟨_, Exec.alloc (l := 0) rfl⟩
  cases hex with
  | @alloc _ _ _ l hfresh =>
      have hf : Heap.union Heap.empty (fun _ => some 0) l = none := hfresh
      rw [union_empty_left] at hf
      exact absurd hf (by simp)`,
      "tag": "illustration",
      "cap": "The small heap is empty; the frame is the totally allocated heap."
    },
    {
      "t": "p",
      "h": `Look at where that counterexample lives. Nothing in <code>Exec.alloc</code> is at fault. The frame is <code>fun _ => some 0</code>, and <code>Heap := Loc → Option Val</code> makes a heap an arbitrary function, so that is a legal heap with no free location anywhere in it. Nothing before this chapter ever needed a fresh location to exist, so nothing ever noticed.`
    },
    {
      "t": "code",
      "src": `abbrev Heap := List (Loc × Val)   -- with a no-duplicate-keys invariant`,
      "tag": "sketch",
      "cap": "The repair, and the bill: every M1–M2 lemma redone."
    },
    {
      "t": "p",
      "h": `Over finite heaps a fresh location provably exists — take one past the largest key — and safety monotonicity comes back. M1 named finite maps as the rejected alternative and priced them there: extensionality stops being <code>funext</code>, and union needs a canonical form before it is even well defined. This is where that bill arrives.`
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "The frame property",
          "h": `Big → small, about the shape of every run. Discharges the <code>∀ s'</code> obligation: any big run comes from a small run plus an untouched frame. <b>Holds for alloc</b>, over functional heaps, proved below.`
        },
        {
          "k": "Safety monotonicity",
          "h": `Small → big, about existence only. Discharges the <code>Safe</code> obligation. <b>Fails for alloc</b> over functional heaps, and is the one thing finiteness buys.`
        },
        {
          "k": "<code>Preserves c R</code>",
          "h": `Unchanged from M8, and it could not have broken: the definition quantifies over runs and never inspects the heap, so a new heap primitive cannot reach it. <code>preserves_of_heapOnly</code> still discharges it for free whenever <code>R</code> is <code>HeapOnly</code> — its proof never mentions <code>Exec</code> — which covers <code>↦</code>, <code>emp</code> and any <code>∗</code> of them. The frames it does not cover are the ones that talk about the store, such as <code>pure (fun σ => σ x = 7)</code>, and those are exactly the ones <code>alloc x e</code> can falsify.`
        }
      ]
    },

    {
      "t": "ex",
      "id": "m14-3",
      "name": "locality of alloc under framing",
      "hard": false,
      "why": `This is where the existential earns its keep, and it earns it by failing. Attempt <code>HeapLocal (.alloc x e)</code>, watch the first conjunct refuse to close, build the counterexample, then prove the condition that survives. That sequence is the exercise.`,
      "setup": `Prove <code>alloc_not_heapLocal</code>, state the frame property, prove it for allocation, and then prove the demonic frame rule from the frame property plus safety monotonicity plus <code>Preserves</code>. Then notice which of the three hypotheses <code>alloc</code> cannot supply.`,
      "hints": [
        `Read the first conjunct of <code>HeapLocal</code> on its own: <code>Heap.disjoint s'.heap hFrame</code>. The small run produced <code>s'</code>. What did it put in the heap, and what was stopping it from putting it where the frame already is?`,
        `Counterexample: <code>h = Heap.empty</code>, <code>hFrame = Heap.singleton 0 w</code>, disjoint. Run <code>alloc</code> on the empty heap, let it choose <code>0</code>, and instantiate <code>hloc</code> at exactly that.`,
        `For the repair, swap which run you are given and which you must produce. If the <i>big</i> run chose <code>l</code> then <code>Heap.union h hFrame l = none</code>, and <code>union_eq_none</code> splits that into <code>h l = none</code> and <code>hFrame l = none</code> — the first lets the small heap replay the choice, the second hands you disjointness.`,
        `The heap equation is <code>Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame</code>, which is M8's <code>write_union_no_disjointness</code>. It never became a corpus theorem, so restate it: <code>funext x</code>, <code>by_cases hxl : x = l</code>, and in the negative branch <code>cases hx : h x</code> — the colon form, because <code>union_of_none</code> and <code>union_of_some</code> want the equation as an argument.`,
        `When you instantiate <code>hfresh</code>, Lean hands it to you at the type <code>{ store := σ, heap := h.union hFrame }.heap l = none</code>. Restate it: <code>have hfresh' : Heap.union h hFrame l = none := hfresh</code>.`
      ],
      "expl": `M8 could conflate the two halves of locality because none of its commands could fail on a bigger heap or behave differently on one. Allocation separates them. It has the frame property and lacks safety monotonicity, and those two facts together are the content of “allocation is local, but only over finite heaps”.`,
      "walk": [
        {
          "tac": "intro σ h hFrame r hd hex",
          "h": `Six binders. Note <code>r</code>: this is the run on the <i>big</i> heap, and it is given to you.`
        },
        {
          "tac": "cases hex with | @alloc _ _ _ l hfresh =>",
          "h": `<code>l</code> is the location the big run chose; <code>hfresh</code> says it was free in <code>h ∪ hFrame</code>. Everything below squeezes those two facts.`
        },
        {
          "tac": "have hfresh' : Heap.union h hFrame l = none := hfresh",
          "h": `The same proof term at the type you can read; the projection is a reduction, not a proof step. Strictly optional here — <code>union_eq_none.mp hfresh</code> elaborates too, because unification unfolds the projection on its own. It stops being optional the moment you want to <code>rw</code>. See the pitfall.`
        },
        {
          "tac": "obtain ⟨hh, hf⟩ := union_eq_none.mp hfresh'",
          "h": `The heart of it. Freshness in the union is freshness in <i>both</i> parts: <code>hh</code> lets the small heap replay the same choice, <code>hf</code> is what makes the result disjoint from the frame. In the small-to-big direction you would have to <i>conclude</i> <code>hf</code>, and there is no way to.`
        },
        {
          "tac": "refine ⟨⟨Store.set σ x l, Heap.write h l (e.eval σ)⟩, Exec.alloc hh, ?_, rfl, ?_⟩",
          "h": `Supply the small run — same variable, same location, same value. The store equation falls out as <code>rfl</code>, because allocation does not consult the heap when updating the store.`
        },
        {
          "tac": "· intro y",
          "h": `First hole: disjointness of the small result from the frame.`
        },
        {
          "tac": "  by_cases hyl : y = l",
          "h": `Two cases, answered by the two halves of <code>union_eq_none</code>.`
        },
        {
          "tac": "  · subst hyl; exact Or.inr hf",
          "h": `At the new cell: the frame does not own it. This is the case that is unprovable in the other direction.`
        },
        {
          "tac": "  · rcases hd y with hy | hy",
          "h": `Away from the new cell nothing changed, so the old disjointness answers it.`
        },
        {
          "tac": "    · left; show Heap.write h l (e.eval σ) y = none",
          "h": `<code>write_other</code> will not match a goal stated through a state projection.`
        },
        {
          "tac": "      rw [write_other h l y (e.eval σ) hyl]; exact hy",
          "h": `<code>write_other</code> wants <code>y ≠ l</code>, which is the negative branch.`
        },
        {
          "tac": "    · exact Or.inr hy",
          "h": `The frame was already free at <code>y</code>.`
        },
        {
          "tac": "· exact write_union h hFrame l (e.eval σ)",
          "h": `Second hole: the heap equation. It needs no hypotheses — writing a cell into a union is writing it into the left part, whatever the two heaps are.`
        }
      ],
      "deep": [
        {
          "t": "p",
          "h": `First, the theorem that ought to be true and is not:`
        },
        {
          "t": "code",
          "src": `def HeapLocal (c : Cmd) : Prop :=
  ∀ σ h hFrame s',
    Heap.disjoint h hFrame →
    Exec c ⟨σ, h⟩ s' →
    Heap.disjoint s'.heap hFrame ∧
    ∃ r : State,
      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧
      r.store = s'.store ∧
      r.heap = Heap.union s'.heap hFrame`,
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": `theorem alloc_not_heapLocal (x : Var) (v w : Val) :
    ¬ HeapLocal (.alloc x (.const v)) := by
  intro hloc
  obtain ⟨hdEnd, -⟩ :=
    hloc (fun _ => 0) Heap.empty (Heap.singleton 0 w)
      ⟨Store.set (fun _ => 0) x 0, Heap.write Heap.empty 0 v⟩
      (disjoint_empty_left _) (Exec.alloc (l := 0) rfl)
  rcases hdEnd 0 with h0 | h0
  · have h0' : Heap.write Heap.empty 0 v 0 = none := h0
    rw [write_same] at h0'
    exact absurd h0' (by simp)
  · rw [singleton_same] at h0
    exact absurd h0 (by simp)`,
          "tag": "illustration",
          "cap": "Small heap empty, frame owning cell 0, allocator picks cell 0."
        },
        {
          "t": "trace",
          "title": "alloc_not_heapLocal, tactic by tactic",
          "start": `x : Var
v w : Val
⊢ ¬HeapLocal (Cmd.alloc x (Atom.const v))`,
          "steps": [
            {
              "tac": "intro hloc",
              "state": `x : Var
v w : Val
hloc : HeapLocal (Cmd.alloc x (Atom.const v))
⊢ False`,
              "h": ``
            },
            {
              "tac": "obtain ⟨hdEnd, -⟩ := hloc (fun _ => 0) Heap.empty (Heap.singleton 0 w) …",
              "state": `x : Var
v w : Val
hloc : HeapLocal (Cmd.alloc x (Atom.const v))
hdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)
⊢ False`,
              "h": `The second component — the existential over the big run — is discarded outright, because the contradiction is already in the first. <code>hdEnd</code> claims a heap holding cell <code>0</code> is disjoint from a heap holding cell <code>0</code>.`
            },
            {
              "tac": "rcases hdEnd 0 with h0 | h0",
              "state": `case inl
x : Var
v w : Val
hloc : HeapLocal (Cmd.alloc x (Atom.const v))
hdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)
h0 : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap 0 = none
⊢ False`,
              "h": `Both branches are absurd, for mirror-image reasons.`
            },
            {
              "tac": "· have h0' : Heap.write Heap.empty 0 v 0 = none := h0",
              "state": `case inl
x : Var
v w : Val
hloc : HeapLocal (Cmd.alloc x (Atom.const v))
hdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)
h0 : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap 0 = none
h0' : Heap.empty.write 0 v 0 = none
⊢ False`,
              "h": `Restated through the projection so that <code>write_same</code> can match.`
            },
            {
              "tac": "  rw [write_same] at h0'; exact absurd h0' (by simp)",
              "state": `case inr
x : Var
v w : Val
hloc : HeapLocal (Cmd.alloc x (Atom.const v))
hdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)
h0 : Heap.singleton 0 w 0 = none
⊢ False`,
              "h": `<code>write_same</code> turns <code>h0'</code> into <code>some v = none</code>, and <code>by simp</code> supplies the negation.`
            },
            {
              "tac": "· rw [singleton_same] at h0; exact absurd h0 (by simp)",
              "state": `No goals.`,
              "h": ``
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": `Now the condition that survives — the same relation with the two runs swapped:`
        },
        {
          "t": "code",
          "src": `def FrameProperty (c : Cmd) : Prop :=
  ∀ σ h hFrame r,
    Heap.disjoint h hFrame →
    Exec c ⟨σ, Heap.union h hFrame⟩ r →
    ∃ s' : State,
      Exec c ⟨σ, h⟩ s' ∧
      Heap.disjoint s'.heap hFrame ∧
      r.store = s'.store ∧
      r.heap = Heap.union s'.heap hFrame`,
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": `theorem write_union (h hFrame : Heap) (l : Loc) (v : Val) :
    Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame := by
  funext x
  by_cases hxl : x = l
  · subst hxl
    rw [write_same, union_of_some hFrame (write_same h x v)]
  · rw [write_other _ l x v hxl]
    have hwx : Heap.write h l v x = h x := write_other h l x v hxl
    cases hx : h x with
    | none   => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]
    | some u => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]`,
          "tag": "illustration",
          "cap": "M8's <code>write_union_no_disjointness</code>, restated and renamed. There it sat inline in the tail of <code>heapLocal_write</code>; here it is load-bearing."
        },
        {
          "t": "code",
          "src": `theorem frameProperty_alloc (x : Var) (e : Atom) : FrameProperty (.alloc x e) := by
  intro σ h hFrame r hd hex
  cases hex with
  | @alloc _ _ _ l hfresh =>
      have hfresh' : Heap.union h hFrame l = none := hfresh
      obtain ⟨hh, hf⟩ := union_eq_none.mp hfresh'
      refine ⟨⟨Store.set σ x l, Heap.write h l (e.eval σ)⟩, Exec.alloc hh, ?_, rfl, ?_⟩
      · intro y
        by_cases hyl : y = l
        · subst hyl; exact Or.inr hf
        · rcases hd y with hy | hy
          · left
            show Heap.write h l (e.eval σ) y = none
            rw [write_other h l y (e.eval σ) hyl]; exact hy
          · exact Or.inr hy
      · exact write_union h hFrame l (e.eval σ)`,
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "frameProperty_alloc, tactic by tactic",
          "start": `x : Var
e : Atom
⊢ FrameProperty (Cmd.alloc x e)`,
          "steps": [
            {
              "tac": "intro σ h hFrame r hd hex",
              "state": `x : Var
e : Atom
σ : Store
h hFrame : Heap
r : State
hd : h.disjoint hFrame
hex : Exec (Cmd.alloc x e) { store := σ, heap := h.union hFrame } r
⊢ ∃ s',
    Exec (Cmd.alloc x e) { store := σ, heap := h } s' ∧
      s'.heap.disjoint hFrame ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame`,
              "h": `Compare with <code>HeapLocal</code>: there the hypothesis was the small run and the existential was the big one.`
            },
            {
              "tac": "cases hex with | @alloc _ _ _ l hfresh =>",
              "state": `case alloc
x : Var
e : Atom
σ : Store
h hFrame : Heap
hd : h.disjoint hFrame
l : Val
hfresh : { store := σ, heap := h.union hFrame }.heap l = none
⊢ ∃ s',
    Exec (Cmd.alloc x e) { store := σ, heap := h } s' ∧
      s'.heap.disjoint hFrame ∧
        { store := { store := σ, heap := h.union hFrame }.store.set x l,
                heap :=
                  { store := σ, heap := h.union hFrame }.heap.write l
                    (Atom.eval { store := σ, heap := h.union hFrame }.store e) }.store =
            s'.store ∧
          { store := { store := σ, heap := h.union hFrame }.store.set x l,
                heap :=
                  { store := σ, heap := h.union hFrame }.heap.write l
                    (Atom.eval { store := σ, heap := h.union hFrame }.store e) }.heap =
            s'.heap.union hFrame`,
              "h": `<code>r</code> has been replaced by the state the constructor produces, and <code>l</code> is the big run's choice.`
            },
            {
              "tac": "obtain ⟨hh, hf⟩ := union_eq_none.mp hfresh'",
              "state": `case alloc
x : Var
e : Atom
σ : Store
h hFrame : Heap
hd : h.disjoint hFrame
l : Val
hfresh : { store := σ, heap := h.union hFrame }.heap l = none
hfresh' : h.union hFrame l = none
hh : h l = none
hf : hFrame l = none
⊢ ∃ s', …`,
              "h": `The goal is untouched — still the thirteen-line display above, elided here — and the whole mathematical content of the theorem is in the three new lines.`
            },
            {
              "tac": "refine ⟨⟨Store.set σ x l, Heap.write h l (e.eval σ)⟩, Exec.alloc hh, ?_, rfl, ?_⟩",
              "state": `case alloc.refine_1
x : Var
e : Atom
σ : Store
h hFrame : Heap
hd : h.disjoint hFrame
l : Val
hfresh : { store := σ, heap := h.union hFrame }.heap l = none
hfresh' : h.union hFrame l = none
hh : h l = none
hf : hFrame l = none
⊢ { store := σ.set x l, heap := h.write l (Atom.eval σ e) }.heap.disjoint hFrame`,
              "h": `The store equation went through as <code>rfl</code>; two goals remain.`
            },
            {
              "tac": "· intro y … (the disjointness case split)",
              "state": `case alloc.refine_2
x : Var
e : Atom
σ : Store
h hFrame : Heap
hd : h.disjoint hFrame
l : Val
hfresh : { store := σ, heap := h.union hFrame }.heap l = none
hfresh' : h.union hFrame l = none
hh : h l = none
hf : hFrame l = none
⊢ { store := { store := σ, heap := h.union hFrame }.store.set x l,
        heap :=
          { store := σ, heap := h.union hFrame }.heap.write l
            (Atom.eval { store := σ, heap := h.union hFrame }.store e) }.heap =
    { store := σ.set x l, heap := h.write l (Atom.eval σ e) }.heap.union hFrame`,
              "h": `The last goal, once the projections are performed, is precisely <code>write_union</code>.`
            },
            {
              "tac": "· exact write_union h hFrame l (e.eval σ)",
              "state": `No goals.`,
              "h": ``
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": `The payoff: M8's frame theorem, restated for the demonic triple, with locality split into its two halves.`
        },
        {
          "t": "code",
          "src": `def Preserves (c : Cmd) (R : Assertion) : Prop :=
  ∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame

theorem hoare_frame {P Q R : Assertion} {c : Cmd}
    (hc : Hoare P c Q) (hfp : FrameProperty c) (hsm : SafetyMonotone c)
    (hpres : Preserves c R) : Hoare (P ∗ R) c (Q ∗ R) := by
  intro σ h hstar
  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar
  subst hu
  refine ⟨hsm σ hP hR hd (hc σ hP hp).1, ?_⟩
  intro r hex
  obtain ⟨s', hex', hdEnd, hst, hhp⟩ := hfp σ hP hR r hd hex
  refine ⟨s'.heap, hR, hdEnd, hhp, ?_, ?_⟩
  · rw [hst]; exact (hc σ hP hp).2 s' hex'
  · exact hpres ⟨σ, Heap.union hP hR⟩ r hex hR hr`,
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "hoare_frame, tactic by tactic",
          "start": `P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
⊢ Hoare (P ∗ R) c (Q ∗ R)`,
          "steps": [
            {
              "tac": "intro σ h hstar",
              "state": `P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
σ : Store
h : Heap
hstar : (P ∗ R) σ h
⊢ Safe c { store := σ, heap := h } ∧ ∀ (s' : State), Exec c { store := σ, heap := h } s' → (Q ∗ R) s'.store s'.heap`,
              "h": `Two obligations, discharged below by two different hypotheses. The six lines above <code>σ</code> are the statement's own binders and are reprinted at every step; watch only what changes underneath.`
            },
            {
              "tac": "obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar",
              "state": `P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
σ : Store
h hP hR : Heap
hd : hP.disjoint hR
hu : h = hP.union hR
hp : P σ hP
hr : R σ hR
⊢ Safe c { store := σ, heap := h } ∧ ∀ (s' : State), Exec c { store := σ, heap := h } s' → (Q ∗ R) s'.store s'.heap`,
              "h": `The M4 six-tuple, unchanged from Phase 1. Nothing about <code>∗</code> had to be revisited for allocation.`
            },
            {
              "tac": "subst hu",
              "state": `P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
σ : Store
hP hR : Heap
hd : hP.disjoint hR
hp : P σ hP
hr : R σ hR
⊢ Safe c { store := σ, heap := hP.union hR } ∧
    ∀ (s' : State), Exec c { store := σ, heap := hP.union hR } s' → (Q ∗ R) s'.store s'.heap`,
              "h": `The goal is now stated entirely in terms of the two pieces.`
            },
            {
              "tac": "refine ⟨hsm σ hP hR hd (hc σ hP hp).1, ?_⟩",
              "state": `P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
σ : Store
hP hR : Heap
hd : hP.disjoint hR
hp : P σ hP
hr : R σ hR
⊢ ∀ (s' : State), Exec c { store := σ, heap := hP.union hR } s' → (Q ∗ R) s'.store s'.heap`,
              "h": `Safety monotonicity, applied to the safety half of the small triple. This is the <i>only</i> place <code>hsm</code> appears, and it is why allocation over functional heaps does not get the frame rule.`
            },
            {
              "tac": "intro r hex ; obtain ⟨s', hex', hdEnd, hst, hhp⟩ := hfp σ hP hR r hd hex",
              "state": `P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
σ : Store
hP hR : Heap
hd : hP.disjoint hR
hp : P σ hP
hr : R σ hR
r : State
hex : Exec c { store := σ, heap := hP.union hR } r
s' : State
hex' : Exec c { store := σ, heap := hP } s'
hdEnd : s'.heap.disjoint hR
hst : r.store = s'.store
hhp : r.heap = s'.heap.union hR
⊢ (Q ∗ R) r.store r.heap`,
              "h": `The frame property, applied once, turning an arbitrary big run into a small run plus an untouched frame. Everything below is bookkeeping on the four facts it returned.`
            },
            {
              "tac": "refine ⟨s'.heap, hR, hdEnd, hhp, ?_, ?_⟩",
              "state": `case refine_1
P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
σ : Store
hP hR : Heap
hd : hP.disjoint hR
hp : P σ hP
hr : R σ hR
r : State
hex : Exec c { store := σ, heap := hP.union hR } r
s' : State
hex' : Exec c { store := σ, heap := hP } s'
hdEnd : s'.heap.disjoint hR
hst : r.store = s'.store
hhp : r.heap = s'.heap.union hR
⊢ Q r.store s'.heap`,
              "h": `Two heaps, their disjointness, the union equation — which is exactly why the frame property was made to return those four things in that order.`
            },
            {
              "tac": "· rw [hst]; exact (hc σ hP hp).2 s' hex'",
              "state": `case refine_2
P Q R : Assertion
c : Cmd
hc : Hoare P c Q
hfp : FrameProperty c
hsm : SafetyMonotone c
hpres : Preserves c R
σ : Store
hP hR : Heap
hd : hP.disjoint hR
hp : P σ hP
hr : R σ hR
r : State
hex : Exec c { store := σ, heap := hP.union hR } r
s' : State
hex' : Exec c { store := σ, heap := hP } s'
hdEnd : s'.heap.disjoint hR
hst : r.store = s'.store
hhp : r.heap = s'.heap.union hR
⊢ R r.store hR`,
              "h": `<code>hst</code> replaces the big store by the small one, and the universal half of the small triple applies to <code>s'</code>.`
            },
            {
              "tac": "· exact hpres ⟨σ, Heap.union hP hR⟩ r hex hR hr",
              "state": `No goals.`,
              "h": `The frame assertion survives because the command preserves it. For <code>alloc x e</code> this is where you must know that <code>R</code> does not mention <code>x</code>.`
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Reading the result honestly",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `Three results side by side: <code>frameProperty_alloc</code> proved, <code>Preserves</code> available for any store-independent <code>R</code>, <code>SafetyMonotone</code> disproved. Be careful about what the last one buys, because the obvious inference is invalid — refuting a <i>sufficient</i> condition does not refute the conclusion, and “<code>hoare_frame</code>'s proof breaks” is not “the frame rule is false”.`
            },
            {
              "t": "p",
              "h": `Here it happens to be false, and the same heap does it. Take the frame assertion to be “the heap is totally allocated”. The framed precondition is satisfiable — <code>Heap.empty</code> for the small part, <code>fun _ => some 0</code> for the frame — and the framed triple then asserts <code>Safe</code> on a heap with no free cell:`
            },
            {
              "t": "code",
              "src": `def full : Assertion := fun _ h => h = fun _ => some 0

theorem alloc_frame_rule_false (x : Var) (v : Val) :
    ¬ Hoare (aAnd (fact (fun σ => (Atom.const v).eval σ = v)) emp ∗ full)
        (.alloc x (.const v))
        ((aExists fun l => pure (fun σ => σ x = l) ∗ (l ↦ v)) ∗ full) := by
  intro hfr
  obtain ⟨⟨r, hex⟩, -⟩ :=
    hfr (fun _ => 0) (Heap.union Heap.empty (fun _ => some 0))
      ⟨Heap.empty, (fun _ => some 0), disjoint_empty_left _, rfl, ⟨rfl, rfl⟩, rfl⟩
  cases hex with
  | @alloc _ _ _ l hfresh =>
      have hf : Heap.union Heap.empty (fun _ => some 0) l = none := hfresh
      rw [union_empty_left] at hf
      exact absurd hf (by simp)`,
              "tag": "illustration",
              "cap": "Not “unprovable by this route” — false. The unframed premise is <code>hoare_alloc x (.const v) v</code> exactly; <code>full</code> is store-independent so <code>Preserves</code> holds; and <code>frameProperty_alloc</code> holds. Only <code>SafetyMonotone</code> is missing."
            },
            {
              "t": "p",
              "h": `So the frame rule for <code>alloc</code> is not a theorem of this development. It is a theorem of the development you get after replacing <code>Heap</code> with a finite map, where no heap is totally allocated and this counterexample has nowhere to live. Which is a more useful state of affairs than a chapter that had assumed finiteness quietly from the start — the gap is now a named hypothesis with a witness, rather than an assumption nobody wrote down.`
            }
          ]
        }
      ],
      "pitfall": `<code>rw</code> at anything inversion produced. Everything inversion produces is phrased through <code>{ store := …, heap := … }.heap</code>: given <code>h0 : { store := …, heap := Heap.empty.write 0 v }.heap 0 = none</code>, the tactic <code>rw [write_same] at h0</code> fails with “Did not find an occurrence of the pattern <code>Heap.write ?h ?l ?v ?l</code>”, because the projection is standing between the pattern and the term. The asymmetry will confuse you if you do not expect it: <code>union_eq_none.mp hfresh</code> succeeds on exactly the hypothesis <code>rw</code> refuses. The fix is one line and you will need it repeatedly — <code>have hf' : Heap.union h hFrame l = none := hfresh</code>.`,
      "variants": `Drop <code>hd : Heap.disjoint h hFrame</code> from the frame property and the heap equation still holds — <code>write_union</code> needs no hypotheses — but the disjointness conjunct fails, and it fails <i>away</i> from the new cell, where the only thing separating <code>h</code> from <code>hFrame</code> was <code>hd</code> itself. Reverse the direction back to small → big and you have <code>HeapLocal</code>, refuted above. Weaken <code>HeapLocal</code>'s conclusion to let the big run end with a <i>different</i> store — tempting, since you would then re-choose the location — and <code>hoare_frame</code> breaks instead, at <code>rw [hst]</code>, because <code>Q</code> is then asserted about a store that never occurred.`
    },

    {
      "t": "h3",
      "s": "A program whose proof cannot pick the run"
    },
    {
      "t": "p",
      "h": `Four commands: allocate a cell, write to it, read it back, free it. The value comes back in <code>y</code>, and the heap ends empty — a no-leak claim about a location the specification never names.`
    },

    {
      "t": "ex",
      "id": "m14-4",
      "name": "alloc, initialise, free",
      "hard": false,
      "why": `The first program in this course whose correctness proof has to consider a run you did not pick — and the proof splits, visibly, into one argument that chooses a run and one that inverts every run.`,
      "setup": `Write <code>alloc x v ; [x] := w ; y := [x] ; free x</code> in the extended language and prove <code>Hoare emp … (pure (fun σ => σ y = w))</code>, demonic reading. You will need <code>x ≠ y</code>. Prove it straight from the semantics rather than through a rule algebra — with four commands, the existential in the alloc postcondition makes rule-based composition more painful than it is worth.`,
      "hints": [
        `For safety you get to choose, so choose <code>l = 0</code>: in the empty heap it is free. Build the run with nested <code>Exec.seq</code> and let <code>refine</code> leave the three “address is allocated” side conditions as holes.`,
        `Those three holes are enormous when printed and trivial in content. <code>simp [Atom.eval, Store.set, Heap.write]</code> closes the first two; the third needs <code>hne</code> as well, because the address of the <code>free</code> is read out of a store into which <code>y</code> has just been written.`,
        `For correctness, invert seven times, alternating <code>.seq</code> and command. Use <code>| @seq _ s1 _ _ _ ha hrest =></code> to name the intermediate states and <code>| @alloc _ _ _ l hfresh =></code> to name the allocator's choice.`,
        `After the inversions the context is unusable. Extract the two facts you need — <code>Store.set σ x l x = l</code>, and the load's value — restate the load hypothesis at a readable type, then <code>clear</code> the four monsters.`,
        `The final heap is <code>Heap.erase (Heap.write (Heap.write Heap.empty l v) l w) l</code>. Collapse it with <code>write_shadow</code>, then <code>write_empty</code>, then <code>erase_singleton</code>.`
      ],
      "expl": `The program is trivial and the proof is not, for one reason: the postcondition has to hold for every location the allocator might have returned. That is the whole difference between verifying a program in a deterministic language and verifying one with <code>malloc</code>, and in the script it is the split between the two obligations.`,
      "walk": [
        {
          "tac": "intro σ h he ; subst he",
          "h": `Fix the state and use <code>emp</code> to replace the heap by <code>Heap.empty</code>.`
        },
        {
          "tac": "constructor",
          "h": `Split the demonic triple. From here the proof is two unrelated arguments.`
        },
        {
          "tac": "refine ⟨_, Exec.seq (Exec.alloc (l := 0) rfl) (Exec.seq (Exec.write (old := v) ?_) …)⟩",
          "h": `Safety: build one complete run, nesting <code>Exec.seq</code> to match the nesting of <code>.seq</code> in the program. <code>(old := v)</code> and <code>(v := w)</code> are supplied because the goal is only <code>∃ s'</code> and determines nothing.`
        },
        {
          "tac": "· simp [Atom.eval, Store.set, Heap.write]",
          "h": `Side condition for the write: the address <code>σ[x↦0] x = 0</code> is allocated, holding <code>v</code>.`
        },
        {
          "tac": "· simp [Atom.eval, Store.set, Heap.write]",
          "h": `Same, for the load.`
        },
        {
          "tac": "· simp [Atom.eval, Store.set, Heap.write, hne]",
          "h": `Same, for the free — but now the store has <code>y</code> written into it, so reading <code>x</code> out of it needs <code>x ≠ y</code>. Remove <code>hne</code> and this is the goal that fails.`
        },
        {
          "tac": "intro s' hex ; cases hex with | @seq _ s1 _ _ _ ha hrest =>",
          "h": `Correctness. Peel the first <code>.seq</code>, naming the state after the allocation.`
        },
        {
          "tac": "cases ha with | @alloc _ _ _ l hfresh =>",
          "h": `Name the allocator's choice. From here nothing may depend on <code>l</code> being <code>0</code>.`
        },
        {
          "tac": "cases hrest with | @seq … => cases hw with | @write _ _ _ old hl =>",
          "h": `Peel and invert the write. <code>old</code> is what was there before; the proof never uses it, which is a small confirmation that the write rule really is agnostic about the old contents.`
        },
        {
          "tac": "cases hrest2 with | @seq … => cases hld with | @load _ _ _ u hl2 =>",
          "h": `Peel and invert the load. <code>u</code> is the value the load actually saw. It is <i>not</i> definitionally <code>w</code>; you have to derive that.`
        },
        {
          "tac": "cases hfr with | @free _ _ u2 hl3 =>",
          "h": `<code>u2</code> is never used — <code>free</code> does not care what was in the cell.`
        },
        {
          "tac": "have hx1 : Store.set σ x l x = l := by simp [Store.set]",
          "h": `The address fact, isolated once so it can be rewritten with repeatedly.`
        },
        {
          "tac": "have hl2' : Heap.write (Heap.write Heap.empty l v) (Store.set σ x l x) w (Store.set σ x l x) = some u := hl2",
          "h": `The load hypothesis at a readable type. Same proof term; only the display changes.`
        },
        {
          "tac": "clear hl hl2 hl3 hfresh",
          "h": `<code>clear</code> deletes hypotheses from the context. It proves nothing and it is not hygiene here — it is the difference between a legible goal and an illegible one. Each of these four is stated about the state the <i>previous</i> command produced, so the state literals nest one inside the next: <code>hfresh</code> is one line, the write's <code>hl</code> twelve, the load's <code>hl2</code> fifty, the free's <code>hl3</code> a hundred and four.`
        },
        {
          "tac": "rw [hx1, write_same] at hl2'",
          "h": `Reduce the address to <code>l</code>, then look up the cell: <code>hl2' : some w = some u</code>.`
        },
        {
          "tac": "have hu : w = u := by injection hl2'",
          "h": `The step connecting the value the program read to the value the specification promises.`
        },
        {
          "tac": "have hx3 : Store.set (Store.set σ x l) y u x = l := by simp [Store.set, hne]",
          "h": `The address of the <code>free</code>, read out of the post-load store. <code>hne</code> is what stops <code>y</code>'s value coming back instead.`
        },
        {
          "tac": "refine ⟨?_, ?_⟩",
          "h": `<code>pure φ</code> is a fact about the store and a claim that the heap is empty.`
        },
        {
          "tac": "· show Store.set (Store.set σ x l) y u y = w ; simp [Store.set, hu]",
          "h": `<code>y</code> holds <code>u</code>, and <code>hu</code> says that is <code>w</code>.`
        },
        {
          "tac": "· show Heap.erase (Heap.write (Heap.write Heap.empty l v) (Store.set σ x l x) w) (…) = Heap.empty",
          "h": `The heap obligation, restated readably.`
        },
        {
          "tac": "  rw [hx1, hx3, write_shadow, write_empty, erase_singleton]",
          "h": `Fix both addresses to <code>l</code>, collapse the double write, turn the write on the empty heap into a singleton, erase it. The heap is empty again — no leak.`
        }
      ],
      "deep": [
        {
          "t": "code",
          "src": `def allocInitFree (x y : Var) (v w : Val) : Cmd :=
  .seq (.alloc x (.const v))
    (.seq (.write (.var x) (.const w))
      (.seq (.load y (.var x)) (.free (.var x))))`,
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": `theorem allocInitFree_spec (x y : Var) (v w : Val) (hne : x ≠ y) :
    Hoare emp (allocInitFree x y v w) (pure (fun σ => σ y = w)) := by
  intro σ h he
  subst he
  constructor
  · refine ⟨_, Exec.seq (Exec.alloc (l := 0) rfl)
              (Exec.seq (Exec.write (old := v) ?_)
                (Exec.seq (Exec.load (v := w) ?_) (Exec.free (v := w) ?_)))⟩
    · simp [Atom.eval, Store.set, Heap.write]
    · simp [Atom.eval, Store.set, Heap.write]
    · simp [Atom.eval, Store.set, Heap.write, hne]
  · intro s' hex
    cases hex with
    | @seq _ s1 _ _ _ ha hrest =>
      cases ha with
      | @alloc _ _ _ l hfresh =>
        cases hrest with
        | @seq _ s2 _ _ _ hw hrest2 =>
          cases hw with
          | @write _ _ _ old hl =>
            cases hrest2 with
            | @seq _ s3 _ _ _ hld hfr =>
              cases hld with
              | @load _ _ _ u hl2 =>
                cases hfr with
                | @free _ _ u2 hl3 =>
                  have hx1 : Store.set σ x l x = l := by simp [Store.set]
                  have hl2' : Heap.write (Heap.write Heap.empty l v)
                                (Store.set σ x l x) w (Store.set σ x l x) = some u := hl2
                  clear hl hl2 hl3 hfresh
                  rw [hx1, write_same] at hl2'
                  have hu : w = u := by injection hl2'
                  have hx3 : Store.set (Store.set σ x l) y u x = l := by
                    simp [Store.set, hne]
                  refine ⟨?_, ?_⟩
                  · show Store.set (Store.set σ x l) y u y = w
                    simp [Store.set, hu]
                  · show Heap.erase (Heap.write (Heap.write Heap.empty l v)
                            (Store.set σ x l x) w)
                          (Store.set (Store.set σ x l) y u x) = Heap.empty
                    rw [hx1, hx3, write_shadow, write_empty, erase_singleton]`,
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "allocInitFree_spec — the two obligations",
          "start": `x y : Var
v w : Val
hne : x ≠ y
⊢ Hoare emp (allocInitFree x y v w) (_root_.pure fun σ => σ y = w)`,
          "steps": [
            {
              "tac": "intro σ h he",
              "state": `x y : Var
v w : Val
hne : x ≠ y
σ : Store
h : Heap
he : emp σ h
⊢ Safe (allocInitFree x y v w) { store := σ, heap := h } ∧
    ∀ (s' : State),
      Exec (allocInitFree x y v w) { store := σ, heap := h } s' → _root_.pure (fun σ => σ y = w) s'.store s'.heap`,
              "h": `Everything after this is one half or the other.`
            },
            {
              "tac": "subst he ; constructor",
              "state": `case left
x y : Var
v w : Val
hne : x ≠ y
σ : Store
⊢ Safe (allocInitFree x y v w) { store := σ, heap := Heap.empty }`,
              "h": `The half where you are allowed to choose the allocator's answer.`
            },
            {
              "tac": "refine ⟨_, Exec.seq (Exec.alloc (l := 0) rfl) …⟩",
              "state": `case left.refine_1
x y : Var
v w : Val
hne : x ≠ y
σ : Store
⊢ { store := { store := σ, heap := Heap.empty }.store.set x 0,
          heap :=
            { store := σ, heap := Heap.empty }.heap.write 0
              (Atom.eval { store := σ, heap := Heap.empty }.store (Atom.const v)) }.heap
      (Atom.eval
        { store := { store := σ, heap := Heap.empty }.store.set x 0,
            heap :=
              { store := σ, heap := Heap.empty }.heap.write 0
                (Atom.eval { store := σ, heap := Heap.empty }.store (Atom.const v)) }.store
        (Atom.var x)) =
    some v`,
              "h": `The first side condition, printed in full so you know what you are in for. It says: after allocating cell <code>0</code> holding <code>v</code>, the address <code>x</code> denotes an allocated cell holding <code>v</code>. Eleven lines; the second is forty-nine and the third a hundred and three. None of it is hard — it is all projection noise, and <code>simp</code> eats it.`
            },
            {
              "tac": "· simp [Atom.eval, Store.set, Heap.write] (×3, last with hne)",
              "state": `case right
x y : Var
v w : Val
hne : x ≠ y
σ : Store
⊢ ∀ (s' : State),
    Exec (allocInitFree x y v w) { store := σ, heap := Heap.empty } s' → _root_.pure (fun σ => σ y = w) s'.store s'.heap`,
              "h": `Safety done. Now the half that has to hold for every run.`
            },
            {
              "tac": "cases × 7, then have hx1 / have hl2' / clear hl hl2 hl3 hfresh",
              "state": `case right.seq.alloc.seq.write.seq.load.free
x y : Var
v w : Val
hne : x ≠ y
σ : Store
l old u u2 : Val
hx1 : σ.set x l x = l
hl2' : (Heap.empty.write l v).write (σ.set x l x) w (σ.set x l x) = some u
⊢ _root_.pure (fun σ => σ y = w) …`,
              "h": `The context <i>after</i> <code>clear</code>; before it, about 170 lines in four hypotheses. The case name records the whole inversion path. Three unknowns survive: <code>l</code>, what the allocator chose; <code>u</code>, what the load saw; and <code>old</code>/<code>u2</code>, what was in the cell before the write and the free, never used.`
            },
            {
              "tac": "refine ⟨?_, ?_⟩ ; show Store.set (Store.set σ x l) y u y = w",
              "state": `case right.seq.alloc.seq.write.seq.load.free.refine_1
x y : Var
v w : Val
hne : x ≠ y
σ : Store
l old u u2 : Val
hx1 : σ.set x l x = l
hl2' : some w = some u
hu : w = u
hx3 : (σ.set x l).set y u x = l
⊢ (σ.set x l).set y u y = w`,
              "h": `Readable at last, and true by <code>hu</code>.`
            },
            {
              "tac": "· simp [Store.set, hu] ; · show Heap.erase … = Heap.empty",
              "state": `case right.seq.alloc.seq.write.seq.load.free.refine_2
x y : Var
v w : Val
hne : x ≠ y
σ : Store
l old u u2 : Val
hx1 : σ.set x l x = l
hl2' : some w = some u
hu : w = u
hx3 : (σ.set x l).set y u x = l
⊢ ((Heap.empty.write l v).write (σ.set x l x) w).erase ((σ.set x l).set y u x) = Heap.empty`,
              "h": `The whole heap history in one term: empty, write <code>v</code>, write <code>w</code>, erase. Both addresses reduce to <code>l</code>, and then three heap lemmas finish it.`
            },
            {
              "tac": "rw [hx1, hx3, write_shadow, write_empty, erase_singleton]",
              "state": `No goals.`,
              "h": ``
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why not build this out of the rules",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `M9 verified <code>copyCell</code> and <code>moveCell</code> through <code>hoare_seq</code>, <code>hoare_frame</code> and <code>hoare_consequence</code>, and that is the way to scale. Here it is more work, for one reason: the postcondition of <code>hoare_alloc</code> is an <code>aExists</code>, so the intermediate assertion fed to <code>hoare_seq</code> has to carry the existential through three more commands, and each small-footprint rule would have to be lifted over it first.`
            },
            {
              "t": "p",
              "h": `The standard fix is an existential-elimination rule for triples — <code>(∀ a, Hoare (P a) c Q) → Hoare (aExists P) c Q</code> — three lines under the demonic definition, and it turns the rule-based route back into the shorter one. Proving it and redoing this exercise through the rules is a good fifth exercise if you want one.`
            }
          ]
        }
      ],
      "pitfall": `Forgetting <code>x ≠ y</code>. The program reads the cell into <code>y</code> and then frees the cell whose address is in <code>x</code>; if they are the same variable the <code>free</code> addresses <code>w</code>, not <code>l</code>, and the program is not even safe. It shows up as an unsolved <code>simp</code> goal of the form <code>x = y → ¬w = 0 → (if x = y → w = 0 then some v else Heap.empty (if x = y then w else 0)) = some w</code> — which is <code>simp</code> telling you, in its own way, that you have an aliasing bug.`,
      "variants": `Drop the <code>free</code> and the postcondition becomes <code>∃ l, pure (σ y = w) ∗ l ↦ w</code>: still true, no longer <code>emp</code>, and the leaked cell is the caller's obligation forever. Swap the load and the free and the program is unsafe — the second obligation would still be provable, vacuously, because no run exists, which is why <code>Safe</code> has to be there. Replace <code>.const v</code> by <code>.var x</code> and the specification stops meaning what you think: <code>alloc</code> evaluates its argument in the store <i>before</i> writing <code>x</code>, so the cell holds the old <code>σ x</code>.`
    },

    {
      "t": "h3",
      "s": "One hypothesis short, and it is not about allocation"
    },
    {
      "t": "p",
      "h": `Allocation is the only construct in this course that forces a <i>definition</i> to change rather than a rule to be added. The wand, weakest preconditions and loops were all built on top of M6's triple without touching it. Here the triple was wrong, the locality condition was wrong, and the heap type is wrong — and each of the three was found by trying to prove something and failing at a nameable line.`
    },
    {
      "t": "p",
      "h": `Two of the three are paid for. The third is not, and it is worth being precise about what is owed. <code>FrameProperty</code> is a statement about what runs do, and allocation satisfies it over heaps that are arbitrary functions. <code>SafetyMonotone</code> is a statement about which runs exist, and allocation fails it — not because of anything in <code>Exec.alloc</code>, but because <code>Loc → Option Val</code> admits a heap with no free cell. Change the type and the counterexample has nowhere to live.`
    },
    {
      "t": "p",
      "h": `Which is one line to say and expensive to do, because it is the type every proof in Phase 1 was written against. Most of those proofs never looked at it; some did, and you cannot tell which by reading them one at a time. The way to find out is to name what Phase 1 actually assumed about heaps and check that nothing else was ever used.`
    },
    {
      "t": "dod",
      "h": `You can add allocation to the language, say why the small-footprint rule must quantify existentially over the returned location, distinguish the angelic and demonic readings of a triple and explain why nondeterminism forces the second, exhibit the heap on which <code>HeapLocal</code> fails for <code>alloc</code>, and name which half of locality survives functional heaps and which half needs finite ones.`
    }
  ]
});
