/* M8 — Locality and the frame rule
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m8",
  "num": "M8",
  "phase": "Phase 2 · Program logic",
  "title": "Locality and the frame rule",
  "blurb": "The defining theorem of the subject — proved from the semantics, not assumed.",

  "orient": {
    "youWill": [
      "Write down the two facts about <code>Exec</code> that M7 left open — <code>HeapLocal</code> for the heap, <code>Preserves</code> for the store — and find the third conjunct neither of them obviously needs.",
      "Prove locality for every command in the language, including the two that change the heap.",
      "Prove <code>hoare_frame</code>: eight lines, no axiom, no <code>sorry</code>.",
      "Discharge a <code>Preserves</code> obligation for a spatial frame, and see the exact assertion at which that route stops.",
      "Verify a two-cell program in four lines whose length does not depend on the frame."
    ],
    "needs": [
      "<code>Heap.disjoint</code> and <code>Heap.union</code>, with <code>union_of_none</code>, <code>union_of_some</code>, <code>write_other</code>, <code>erase_other</code>.",
      "The six-slot <code>∗</code> pattern <code>⟨h₁, h₂, hd, hu, hp, hq⟩</code>, opened and rebuilt by hand.",
      "<code>Exec</code>’s constructors with their side conditions, and <code>Hoare</code>."
    ],
    "payoff": "From M9 on, every verification is <code>hoare_seq</code> + <code>hoare_frame</code> + a small rule, and <code>Exec</code> does not appear again."
  },

  "blocks": [

    { "t": "p",
      "h": "A run in a small heap, replayed in a larger one, ending in the same place with the extra part untouched. That is the first of the two missing facts, and it is short enough to write out." },

    { "t": "code", "tag": "illustration",
      "src": "def HeapLocalWeak (c : Cmd) : Prop :=\n  ∀ σ h hFrame s',\n    Heap.disjoint h hFrame →\n    Exec c ⟨σ, h⟩ s' →\n    ∃ r : State,\n      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧\n      r.store = s'.store ∧\n      r.heap = Heap.union s'.heap hFrame",
      "cap": "the statement the textbooks make, and the one you would write first" },

    { "t": "p",
      "h": "<code>hFrame</code> is any heap whatever, constrained only by that disjointness — on paper, “let <code>h ⊎ hFrame</code> be defined”. <code>Exec c ⟨σ, h⟩ s'</code> is the small run you already have, because it came out of a triple. The conclusion is existential rather than an equation because <code>Exec</code> is a relation: there is no final state to compute, so you must exhibit one. And the last conjunct is the whole content — the big run’s heap is the small run’s heap with the frame glued back on, equal <i>as a function</i>, not merely agreeing on the frame’s domain." },

    { "t": "p",
      "h": "Read the last two conjuncts as a square. Extend by <code>hFrame</code>, then run; or run, then extend by <code>hFrame</code>. Locality says the two land in the same place." },

    { "t": "svg",
      "src": "\n<svg viewBox=\"0 0 560 196\" role=\"img\" aria-label=\"Locality as a commuting square\">\n  <g class=\"dg\">\n    <rect x=\"14\" y=\"26\" width=\"164\" height=\"36\" rx=\"7\" class=\"dg-box a\"/>\n    <text x=\"96\" y=\"49\" text-anchor=\"middle\" class=\"dg-t\">⟨σ, h⟩</text>\n    <path class=\"dg-arr\" d=\"M186 44 L 336 44\"/>\n    <text x=\"261\" y=\"34\" text-anchor=\"middle\" class=\"dg-note\">c</text>\n    <rect x=\"344\" y=\"26\" width=\"164\" height=\"36\" rx=\"7\" class=\"dg-box b\"/>\n    <text x=\"426\" y=\"49\" text-anchor=\"middle\" class=\"dg-t\">s'</text>\n\n    <path class=\"dg-arr\" d=\"M96 68 L 96 118\"/>\n    <text x=\"106\" y=\"98\" class=\"dg-note\">∪ hFrame</text>\n    <path class=\"dg-arr thin\" d=\"M426 68 L 426 118\"/>\n    <text x=\"436\" y=\"98\" class=\"dg-note\">∪ hFrame</text>\n\n    <rect x=\"14\" y=\"124\" width=\"164\" height=\"36\" rx=\"7\" class=\"dg-box c\"/>\n    <text x=\"96\" y=\"147\" text-anchor=\"middle\" class=\"dg-t sm\">⟨σ, h ∪ hFrame⟩</text>\n    <path class=\"dg-arr thin\" d=\"M186 142 L 336 142\"/>\n    <text x=\"261\" y=\"132\" text-anchor=\"middle\" class=\"dg-note\">c</text>\n    <rect x=\"344\" y=\"124\" width=\"164\" height=\"36\" rx=\"7\" class=\"dg-box c\"/>\n    <text x=\"426\" y=\"147\" text-anchor=\"middle\" class=\"dg-t\">r</text>\n\n    <text x=\"14\" y=\"184\" class=\"dg-note\">solid: what the triple hands you.   dashed: what locality promises exists.</text>\n  </g>\n</svg>",
      "cap": "The two dashed edges are the existential: <code>r</code> has to be produced, and it has to be the old final heap plus the frame." },

    { "t": "p",
      "h": "So this is a simulation statement about the operational semantics, and whether it holds depends entirely on which commands the language has. Nothing about the assertion language enters it." },

    { "t": "p",
      "h": "It is also one conjunct short, and you find out at the very last step of the frame proof. To conclude <code>Q ∗ R</code> of the final heap you must exhibit a split of it; the cut is <code>s'.heap</code> and <code>hR</code>; so you owe <code>Heap.disjoint s'.heap hR</code>. The disjointness you were handed is about the heap <i>before</i> the command. The equation about <code>r.heap</code> says nothing about <code>s'.heap</code> against <code>hR</code>. There is no route, the missing fact is a fact about the command, and so it belongs in the definition of local." },

    { "t": "code",
      "src": "def HeapLocal (c : Cmd) : Prop :=\n  ∀ σ h hFrame s',\n    Heap.disjoint h hFrame →\n    Exec c ⟨σ, h⟩ s' →\n    Heap.disjoint s'.heap hFrame ∧\n    ∃ r : State,\n      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧\n      r.store = s'.store ∧\n      r.heap = Heap.union s'.heap hFrame",
      "cap": "the definition used from here on: the command did not annex any of the frame’s territory" },

    { "t": "quote",
      "h": "Adding disjoint memory before execution does not change what the command does, and that memory is still there, unchanged, afterwards." },

    { "t": "p",
      "h": "The extra conjunct costs nothing to prove: <code>write</code> preserves the domain, <code>free</code> shrinks it, and the other commands do not touch the heap at all. It costs one line in each of four exercises and buys the reassembly step twice — once in <code>hoare_frame</code>, once in the middle of a sequence." },

    { "t": "h3", "s": "The store half" },

    { "t": "p",
      "h": "The second gap needs no heaps to break it. Three lines:" },

    { "t": "txt",
      "src": "  valid:    { x = 0 }  x := 1  { x = 1 }\n  framing \"x = 0\" gives\n  invalid:  { x = 0 ∗ x = 0 }  x := 1  { x = 1 ∗ x = 0 }     ← false" },

    { "t": "p",
      "h": "The frame simply talked about a variable the command overwrote. So the repair is a second side condition, and it has no spatial content at all:" },

    { "t": "code",
      "src": "def Preserves (c : Cmd) (R : Assertion) : Prop :=\n  ∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame" },

    { "t": "p",
      "h": "It pins the heap and lets only the store move: <code>R s.store hFrame → R s'.store hFrame</code>. That is the right shape precisely because the frame’s heap is untouched by hypothesis — <code>HeapLocal</code>’s job — leaving the store as the only thing that can still break <code>R</code>." },

    { "t": "cmp",
      "left": {
        "t": "The syntactic side condition in the textbooks",
        "kind": "bad",
        "h": "<code>modifies(c) ∩ freeVars(R) = ∅</code>. Stating it needs a syntactic <code>modifies</code> on commands and a <code>freeVars</code> on assertions — and an <code>Assertion</code> here is an arbitrary <code>Store → Heap → Prop</code>, which has no syntax to take the free variables of. It is not merely inconvenient in this development; it is unstatable."
      },
      "right": {
        "t": "The semantic side condition we use",
        "kind": "good",
        "h": "<code>Preserves c R</code> says the same thing where it matters and is strictly weaker: it also accepts an <code>R</code> that mentions a variable the command writes, provided the write does not disturb it. Every instance in this chapter is discharged by one helper."
      } },

    { "t": "detail", "title": "The counterexample, in Lean", "tag": "aside", "open": false,
      "blocks": [
        { "t": "p", "h": "The <code>x := 1</code> line above is a theorem, not folklore. Both halves: the small triple holds, the framed triple is refutable." },
        { "t": "code", "tag": "illustration",
          "src": "theorem frame_without_preserves_is_false (x : Var) :\n    Hoare (pure (fun σ => σ x = 0)) (.assign x (.const 1)) (pure (fun σ => σ x = 1))\n    ∧ ¬ Hoare (pure (fun σ => σ x = 0) ∗ fact (fun σ => σ x = 0))\n              (.assign x (.const 1))\n              (pure (fun σ => σ x = 1) ∗ fact (fun σ => σ x = 0)) := by\n  constructor\n  · intro σ h hp\n    obtain ⟨hx, he⟩ := hp\n    refine ⟨⟨Store.set σ x 1, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ x 1 x = 1\n    simp [Store.set]\n  · intro hcontra\n    obtain ⟨s', hex, hq⟩ :=\n      hcontra (fun _ => 0) Heap.empty\n        ⟨Heap.empty, Heap.empty, disjoint_empty_left _,\n         (union_empty_left _).symm, ⟨rfl, rfl⟩, rfl⟩\n    cases hex\n    obtain ⟨h₁, h₂, hd, hu, hq1, hr1⟩ := hq\n    have hbad : Store.set (fun _ => 0) x 1 x = 0 := hr1\n    simp [Store.set] at hbad",
          "cap": "not in the corpus — compiles against prelude/m8.lean" },
        { "t": "p", "h": "The witness is as small as it gets: store <code>fun _ => 0</code>, heap <code>Heap.empty</code>, cut into empty and empty. After <code>cases hex</code> the final store is <code>Store.set (fun _ => 0) x 1</code>, and the framed conjunct demands its value at <code>x</code> be <code>0</code>. The heap never enters the argument, which is the point." },
        { "t": "p", "h": "Two choices in there are deliberate. The frame is <code>fact</code>, not <code>pure</code>, so the framed assertion imposes nothing spatial and the refutation cannot be blamed on a bad split. And <code>⟨rfl, rfl⟩</code> inside the big anonymous constructor builds a <code>pure</code> the other way round — <code>rfl</code> for <code>(fun _ => 0) x = 0</code>, <code>rfl</code> for <code>Heap.empty = Heap.empty</code>. Expect one display quirk on the way through: the goal prints our assertion as <code>_root_.pure</code>." } ] },

    { "t": "p",
      "h": "For a spatial <code>R</code> the obligation is free, and there is a name for why:" },

    { "t": "code",
      "src": "def HeapOnly (R : Assertion) : Prop := ∀ σ σ' h, R σ h → R σ' h\n\ntheorem preserves_of_heapOnly {R : Assertion} (c : Cmd) (h : HeapOnly R) : Preserves c R :=\n  fun s s' _ hFrame hr => h s.store s'.store hFrame hr\n\ntheorem heapOnly_pointsTo (l : Loc) (v : Val) : HeapOnly (l ↦ v) :=\n  fun _ _ _ hr => hr\n\ntheorem heapOnly_emp : HeapOnly emp := fun _ _ _ hr => hr\n\ntheorem heapOnly_star {P Q : Assertion} (hp : HeapOnly P) (hq : HeapOnly Q) :\n    HeapOnly (P ∗ Q) := by\n  intro σ σ' h ⟨h₁, h₂, hd, hu, h1, h2⟩\n  exact ⟨h₁, h₂, hd, hu, hp σ σ' h₁ h1, hq σ σ' h₂ h2⟩" },

    { "t": "dl", "items": [
      { "k": "<code>heapOnly_pointsTo</code>, <code>heapOnly_emp</code>",
        "h": "Both are <code>fun _ _ _ hr => hr</code>. The assertion does not look at its store argument, so the implication is the identity function. This is the dividend of having written <code>pointsTo</code> as an equation about the heap with the store ignored." },
      { "k": "<code>heapOnly_star</code>",
        "h": "Closure under <code>∗</code>: destructure, push each half through, rebuild. The heaps never move; only the store is swapped. So anything built from <code>↦</code>, <code>emp</code> and <code>∗</code> is covered, at any size." },
      { "k": "<code>preserves_of_heapOnly</code>",
        "h": "The bridge. Watch the argument order — <code>(c : Cmd)</code> comes first and explicitly, so a use site reads <code>preserves_of_heapOnly _ (…)</code> with the command left to unification." } ] },

    { "t": "p",
      "h": "Where this route stops is <code>fact</code> and <code>pure</code>. <code>HeapOnly (fact φ)</code> unfolds to <code>∀ σ σ', φ σ → φ σ'</code>, which says <code>φ</code> is constant — false for any <code>φ</code> that reads a variable, and those are the ones worth framing:" },

    { "t": "code", "tag": "illustration",
      "src": "theorem not_heapOnly_pure (x : Var) : ¬ HeapOnly (pure (fun σ => σ x = 0)) := by\n  intro hbad\n  have h := hbad (fun _ => 0) (fun _ => 1) Heap.empty ⟨rfl, rfl⟩\n  have hbad2 : (1 : Val) = 0 := h.1\n  simp at hbad2",
      "cap": "not in the corpus — two stores, one empty heap, and the fact does not survive the swap" },

    { "t": "p",
      "h": "<code>Exec</code>’s constructors are stated about a state <code>s</code> and its projections, and you always apply them to a state you wrote out yourself as <code>⟨σ, h⟩</code>, so the goals in the <code>write</code> and <code>free</code> cases arrive with projections nested two deep. Nothing is wrong and nothing needs computing; the two ways out are already in your hands — <code>have hl' : h l = _ := hl</code> for a hypothesis you want to <code>rw</code> with, and <code>show</code> for the goal." },

    { "t": "sec", "s": "Exercises · locality, command by command" },

    {
      "t": "ex",
      "id": "m8-1",
      "name": "heapLocal_skip / heapLocal_assign / heapLocal_load",
      "hard": false,

      "why": "The three commands that leave the heap alone. Locality is nearly definitional for the first two — but the load still has to show its side condition survives the extension, and that single line is the reason the small-footprint load rule scales. Do these first for a second reason: they are where you learn to read the five-slot anonymous constructor that every remaining proof in the chapter reuses.",
      "setup": "In scope: <code>HeapLocal</code>, all of <code>Exec</code>’s constructors, and <code>union_of_some : h₁ l = some v → Heap.union h₁ h₂ l = some v</code>, whose partner heap <code>h₂</code> is explicit and the rest implicit — so the call is <code>union_of_some hFrame hl</code>.",
      "goal": "theorem heapLocal_skip : HeapLocal .skip\ntheorem heapLocal_assign (x : Var) (e : Atom) : HeapLocal (.assign x e)\ntheorem heapLocal_load (x : Var) (l : Loc) : HeapLocal (.load x l)",

      "hints": [
        "All three have one skeleton. <code>intro</code> the six binders, then <code>cases hex</code> — the command’s own semantics tells you what <code>s'</code> is, and once you know that, the goal tells you which <code>r</code> to supply.",
        "After <code>cases</code> the goal is <code>… ∧ ∃ r, … ∧ … ∧ …</code>, which one anonymous constructor covers: <code>⟨disjointness, the state r, the Exec proof, rfl, rfl⟩</code>. None of these commands touches the heap, so the disjointness proof is <code>hd</code> itself and both equations are <code>rfl</code>.",
        "The state to supply is “what the command did, but starting from <code>Heap.union h hFrame</code>”. For <code>skip</code>, <code>⟨σ, Heap.union h hFrame⟩</code>; for <code>assign</code>, <code>⟨Store.set σ x (e.eval σ), Heap.union h hFrame⟩</code>.",
        "For <code>load</code> the <code>Exec</code> proof is not free: <code>Exec.load</code> wants <code>(h ∪ hFrame) l = some v</code> and you have <code>h l = some v</code>. Write <code>refine … Exec.load ?_ …</code> and close the hole with <code>union_of_some hFrame hl</code>. The value read is inaccessible, so write <code>Store.set σ x _</code> and let unification fill it."
      ],

      "sol": "theorem heapLocal_skip : HeapLocal .skip := by\n  intro σ h hFrame s' hd hex\n  cases hex\n  exact ⟨hd, ⟨σ, Heap.union h hFrame⟩, Exec.skip, rfl, rfl⟩\n\ntheorem heapLocal_assign (x : Var) (e : Atom) : HeapLocal (.assign x e) := by\n  intro σ h hFrame s' hd hex\n  cases hex\n  exact ⟨hd, ⟨Store.set σ x (e.eval σ), Heap.union h hFrame⟩, Exec.assign, rfl, rfl⟩\n\ntheorem heapLocal_load (x : Var) (l : Loc) : HeapLocal (.load x l) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | load hl =>\n      refine ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩, Exec.load ?_, rfl, rfl⟩\n      exact union_of_some hFrame hl",

      "expl": "<code>union_of_some</code> is the load case in one lemma: if the small heap has the cell, the left-biased union has it too, with the same value. The frame cannot change what a load reads — which <i>is</i> the locality property, at the one command where you can watch it happen.",

      "walk": [
        { "tac": "intro σ h hFrame s' hd hex",
          "h": "<code>HeapLocal .skip</code> is a <code>∀</code> under the hood, so this peels off all six binders: store, small heap, frame, the small run’s result, the disjointness, the execution." },
        { "tac": "cases hex",
          "h": "One constructor can produce <code>Exec .skip ⟨σ, h⟩ s'</code>, and it forces <code>s' = ⟨σ, h⟩</code>. So <code>cases</code> eliminates <code>s'</code> and restates the goal in terms of <code>⟨σ, h⟩</code>. The branch is labelled <code>case skip</code>." },
        { "tac": "exact ⟨hd, ⟨σ, Heap.union h hFrame⟩, Exec.skip, rfl, rfl⟩",
          "h": "Five slots for <code>A ∧ ∃ r, B ∧ C ∧ D</code> — flat, because the anonymous constructor re-nests to the right. <code>hd</code> proves the first conjunct because <code>skip</code> left the heap alone; the two <code>rfl</code>s work because the state you supplied is on the nose the right one." },
        { "tac": "theorem heapLocal_assign (x : Var) (e : Atom) : HeapLocal (.assign x e) := by",
          "h": "Second theorem, same shape. <code>x</code> and <code>e</code> are parameters of the command, not of the locality property." },
        { "tac": "intro σ h hFrame s' hd hex", "h": "Identical." },
        { "tac": "cases hex",
          "h": "<code>Exec.assign</code> fixes <code>s' = ⟨Store.set σ x (e.eval σ), h⟩</code>. The evaluation happens in the <i>initial</i> store, which is why the frame cannot reach it." },
        { "tac": "exact ⟨hd, ⟨Store.set σ x (e.eval σ), Heap.union h hFrame⟩, Exec.assign, rfl, rfl⟩",
          "h": "The witness is the assignment’s effect on the big heap: same store update, bigger heap. <code>rfl</code> closes <code>r.store = s'.store</code> because both sides are the same term." },
        { "tac": "theorem heapLocal_load (x : Var) (l : Loc) : HeapLocal (.load x l) := by",
          "h": "The one with content." },
        { "tac": "intro σ h hFrame s' hd hex", "h": "As before." },
        { "tac": "cases hex with",
          "h": "The named form, because <code>Exec.load</code> carries a side condition you want to keep." },
        { "tac": "| load hl =>",
          "h": "Names it <code>hl : { store := σ, heap := h }.heap l = some v✝</code>. The value stays inaccessible; you never named it and never need it." },
        { "tac": "refine ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩, Exec.load ?_, rfl, rfl⟩",
          "h": "<code>refine</code>, not <code>exact</code>, because one slot is not yet available. Two kinds of hole here: <code>_</code> in <code>Store.set σ x _</code> is one Lean fills by unification, <code>?_</code> in <code>Exec.load ?_</code> is one you promise to fill, and it becomes the next goal." },
        { "tac": "exact union_of_some hFrame hl",
          "h": "The goal is <code>{ store := σ, heap := h.union hFrame }.heap l = some v✝</code> — up to the projection, exactly <code>union_of_some</code>’s conclusion. This line is the whole mathematical content of the load case, and it works because the union is left-biased and the small heap already owns the cell." }
      ],

      "deep": [
        { "t": "trace", "title": "heapLocal_skip, tactic by tactic",
          "start": "⊢ HeapLocal Cmd.skip",
          "steps": [
            { "tac": "intro σ h hFrame s' hd hex",
              "state": "σ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nhex : Exec Cmd.skip { store := σ, heap := h } s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec Cmd.skip { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Read the goal: a conjunction whose second half is an existential over states. That shape is what the five-slot <code>⟨…⟩</code> matches." },
            { "tac": "cases hex",
              "state": "case skip\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\n⊢ { store := σ, heap := h }.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec Cmd.skip { store := σ, heap := h.union hFrame } r ∧\n        r.store = { store := σ, heap := h }.store ∧ r.heap = { store := σ, heap := h }.heap.union hFrame",
              "h": "<code>s'</code> and <code>hex</code> are gone: <code>cases</code> learned <code>s'</code> had to be <code>⟨σ, h⟩</code> and substituted it. The projections it left behind are cosmetic — <code>exact</code> checks up to definitional equality, so <code>hd</code> closes the first conjunct without complaint." },
            { "tac": "exact ⟨hd, ⟨σ, Heap.union h hFrame⟩, Exec.skip, rfl, rfl⟩",
              "state": "No goals.",
              "h": "The witness is “the same state, with the frame attached”." } ],
          "done": "No goals." },

        { "t": "trace", "title": "heapLocal_load, tactic by tactic",
          "start": "x : Var\nl : Loc\n⊢ HeapLocal (Cmd.load x l)",
          "steps": [
            { "tac": "intro σ h hFrame s' hd hex",
              "state": "x : Var\nl : Loc\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nhex : Exec (Cmd.load x l) { store := σ, heap := h } s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec (Cmd.load x l) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "The same six binders, with the command’s parameters also in scope." },
            { "tac": "cases hex with | load hl =>",
              "state": "case load\nx : Var\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\n⊢ { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec (Cmd.load x l) { store := σ, heap := h.union hFrame } r ∧\n        r.store = { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.store ∧\n          r.heap =\n            { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.heap.union\n              hFrame",
              "h": "<code>Exec.load</code> brought two things: an inaccessible value <code>v✝</code>, and the side condition. Note that <code>hl</code> is stated about <code>{ store := σ, heap := h }.heap l</code>, not <code>h l</code>. Harmless here, because <code>hl</code> is only ever passed to a lemma; it bites in the next exercise, where you want to <code>rw</code> with it." },
            { "tac": "refine ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩, Exec.load ?_, rfl, rfl⟩",
              "state": "case load\nx : Var\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\n⊢ { store := σ, heap := h.union hFrame }.heap l = some v✝",
              "h": "One goal: the side condition of the big run’s load. If reading from the extended heap could give a different answer, separation logic would not work." },
            { "tac": "exact union_of_some hFrame hl",
              "state": "No goals.",
              "h": "<code>union_of_some</code>’s conclusion with a <code>State.heap</code> projection wrapped around the left-hand side. <code>exact</code> sees through it." } ],
          "done": "No goals." }
      ],

      "pitfall": "You will try to name the value that was read: <code>cases hex with | load hl v</code>. Lean answers <code>Too many variable names provided at alternative `load`: 2 provided, but 1 expected</code>. <code>Exec.load</code>’s only <i>explicit</i> field is the side condition; the value is implicit, and <code>with | ctor a b</code> names explicit fields only. If you want the name anyway, <code>rename_i v</code> after the <code>cases</code> gets it. Usually you do not: <code>Store.set σ x _</code> lets unification supply it and the proof is shorter.",

      "variants": "Drop <code>Heap.disjoint h hFrame</code> from <code>HeapLocal</code> and all three become unprovable — for a stupid-sounding but instructive reason. The first conclusion is <code>Heap.disjoint s'.heap hFrame</code>, which for these three commands <i>is</i> <code>Heap.disjoint h hFrame</code>, and you would have nothing left to prove it with. Now instead replace <code>Heap.union h hFrame</code> by <code>Heap.union hFrame h</code> throughout: the statement stays true, but the load proof breaks, because a union that consults the frame first is not answered by <code>union_of_some hFrame hl</code>. You would route through <code>union_comm hd</code> — that is, spend the disjointness hypothesis to recover a fact left-biasedness gave you for nothing."
    },

    {
      "t": "ex",
      "id": "m8-2",
      "name": "heapLocal_write",
      "hard": true,

      "why": "The first case with content: writing into the union has to equal writing into the small heap and re-uniting. It is also where you find out how much of this chapter’s work is spent putting goals into a shape the M1 and M2 lemmas can match.",
      "setup": "In scope from M1/M2: <code>write_same : Heap.write h l v l = some v</code>, <code>write_other : x ≠ l → Heap.write h l v x = h x</code>, <code>union_of_none</code>, <code>union_of_some</code>. <code>Heap.disjoint h₁ h₂</code> is <code>∀ l, h₁ l = none ∨ h₂ l = none</code>, so proving one starts with <code>intro x</code> and using one is <code>hd x</code>.",
      "goal": "theorem heapLocal_write (l : Loc) (e : Atom) : HeapLocal (.write l e)",

      "hints": [
        "Two obligations. (a) Disjointness survives, because <code>write</code> does not change the domain. (b) The heap equation <code>write (h ∪ hFrame) l v = (write h l v) ∪ hFrame</code>, which is a <code>funext</code> and a split on <code>x = l</code>. Do (a) as a standalone <code>have</code> before touching the main goal.",
        "For (a): <code>intro x</code>, then <code>rcases hd x with hx | hx</code>. The right disjunct transfers unchanged. The left one (<code>h x = none</code>) needs a split on <code>x = l</code>: away from <code>l</code>, <code>write_other</code> says nothing changed; at <code>l</code> you have both <code>h l = none</code> and <code>h l = some old</code>, so the branch is vacuous.",
        "The <code>hl</code> that <code>cases</code> gave you is about <code>{ store := σ, heap := h }.heap l</code>, and <code>rw</code> will not use it against a goal mentioning <code>h l</code>. Restate it: <code>have hl' : h l = _ := hl</code>. The <code>_</code> stands for a right-hand side you cannot type.",
        "After the <code>refine</code> the last goal is the heap equation wrapped in <code>State.heap</code> projections, so <code>funext</code> works but every following <code>rw</code> fails. Put the goal in the shape you want first: <code>show Heap.write (Heap.union h hFrame) l (e.eval σ) = Heap.union (Heap.write h l (e.eval σ)) hFrame</code>, and only then <code>funext x</code>.",
        "In the <code>x ≠ l</code> branch both sides are unions, but you do not know whether <code>h x</code> is <code>none</code> or <code>some</code>. <code>cases hx : h x with | none => … | some w => …</code> splits it and records the equation, which is exactly the premise <code>union_of_none</code> and <code>union_of_some</code> want. Chain <code>hwx</code> and <code>hx</code> with <code>hwx.trans hx</code>."
      ],

      "sol": "theorem heapLocal_write (l : Loc) (e : Atom) : HeapLocal (.write l e) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | write hl =>\n      have hl' : h l = _ := hl\n      have hdw : Heap.disjoint (Heap.write h l (e.eval σ)) hFrame := by\n        intro x\n        rcases hd x with hx | hx\n        · by_cases hxl : x = l\n          · subst hxl; rw [hl'] at hx; exact absurd hx (by simp)\n          · left; rw [write_other h l x (e.eval σ) hxl]; exact hx\n        · exact Or.inr hx\n      refine ⟨hdw, ⟨σ, Heap.write (Heap.union h hFrame) l (e.eval σ)⟩,\n              Exec.write (union_of_some hFrame hl'), rfl, ?_⟩\n      show Heap.write (Heap.union h hFrame) l (e.eval σ)\n             = Heap.union (Heap.write h l (e.eval σ)) hFrame\n      funext x\n      by_cases hxl : x = l\n      · subst hxl\n        rw [write_same (Heap.union h hFrame) x (e.eval σ),\n            union_of_some hFrame (write_same h x (e.eval σ))]\n      · rw [write_other (Heap.union h hFrame) l x (e.eval σ) hxl]\n        have hwx : Heap.write h l (e.eval σ) x = h x := write_other h l x (e.eval σ) hxl\n        cases hx : h x with\n        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]\n        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]",

      "expl": "Read the disjointness argument for what it says about the frame. At <code>x = l</code> we know <code>h l = some old</code>, so <code>hd</code> must have chosen its <i>right</i> disjunct — <code>hFrame l = none</code> — and the write cannot collide. Everywhere else <code>write_other</code> says nothing changed. The heap equation then splits into “at <code>l</code>, both sides are <code>some (e.eval σ)</code>” and “elsewhere, both sides are <code>h x</code> or <code>hFrame x</code>”.",

      "walk": [
        { "tac": "intro σ h hFrame s' hd hex", "h": "The six binders." },
        { "tac": "cases hex with", "h": "Named form: <code>Exec.write</code>’s side condition is needed twice." },
        { "tac": "| write hl =>",
          "h": "Binds <code>hl : { store := σ, heap := h }.heap l = some old✝</code> and fixes <code>s' = ⟨σ, Heap.write h l (e.eval σ)⟩</code>. The goal explodes into projections; leave it." },
        { "tac": "have hl' : h l = _ := hl",
          "h": "Assert the type you want, with <code>_</code> for the part you cannot write — the value is called <code>old✝</code> and <code>✝</code> is not an input character — and prove it by <code>hl</code>, which typechecks because the two types are definitionally equal. Now <code>hl' : h l = some old✝</code> in a form <code>rw</code> can match." },
        { "tac": "have hdw : Heap.disjoint (Heap.write h l (e.eval σ)) hFrame := by",
          "h": "Obligation (a), split off so the main line stays readable. Stating its type also pins down which heap you mean, which is what keeps the projections out of the sub-proof." },
        { "tac": "intro x", "h": "<code>Heap.disjoint</code> is a <code>∀ l, … ∨ …</code>, so a proof starts by fixing a location." },
        { "tac": "rcases hd x with hx | hx",
          "h": "The assumption at <code>x</code>, split. First branch <code>hx : h x = none</code>, second <code>hx : hFrame x = none</code>." },
        { "tac": "· by_cases hxl : x = l",
          "h": "In the first branch the answer depends on whether <code>x</code> is the cell being written." },
        { "tac": "· subst hxl; rw [hl'] at hx; exact absurd hx (by simp)",
          "h": "The vacuous branch. <code>subst</code> eliminates <code>l</code> — Lean picks which variable goes, and here it is <code>l</code>, so every hypothesis is restated in terms of <code>x</code>. Then <code>rw [hl'] at hx</code> turns <code>hx</code> into <code>some old✝ = none</code>, and <code>absurd hx (by simp)</code> kills it." },
        { "tac": "· left; rw [write_other h l x (e.eval σ) hxl]; exact hx",
          "h": "<code>left</code> picks the first disjunct; <code>write_other</code>, whose last argument is exactly <code>hxl : x ≠ l</code>, rewrites the write away; <code>hx</code> finishes." },
        { "tac": "· exact Or.inr hx",
          "h": "Second <code>rcases</code> branch: the frame is empty at <code>x</code>, which is the right disjunct whatever we did to <code>h</code>." },
        { "tac": "refine ⟨hdw, ⟨σ, Heap.write (Heap.union h hFrame) l (e.eval σ)⟩,\n        Exec.write (union_of_some hFrame hl'), rfl, ?_⟩",
          "h": "Five slots: disjointness is <code>hdw</code>; the witness writes into the big heap; the execution needs the cell to exist there, which is <code>union_of_some hFrame hl'</code>; the store equation is <code>rfl</code> because a write does not touch the store; the heap equation is left open." },
        { "tac": "show Heap.write (Heap.union h hFrame) l (e.eval σ)\n       = Heap.union (Heap.write h l (e.eval σ)) hFrame",
          "h": "The same proposition with the projections stripped, so the rewriting lemmas match syntactically. Skipping this is the commonest way to get stuck here." },
        { "tac": "funext x",
          "h": "Both sides are functions <code>Loc → Option Val</code>; reduce to a pointwise statement at an arbitrary <code>x</code>." },
        { "tac": "by_cases hxl : x = l", "h": "The written cell versus everything else." },
        { "tac": "· subst hxl",
          "h": "<code>l</code> is replaced by <code>x</code> throughout, inside <code>hl'</code> and <code>hdw</code> as well — which is why the next line’s lemmas mention <code>x</code>." },
        { "tac": "rw [write_same (Heap.union h hFrame) x (e.eval σ),\n    union_of_some hFrame (write_same h x (e.eval σ))]",
          "h": "Two rewrites, left to right. The first makes the left side <code>some (e.eval σ)</code>. The second makes the right side <code>some (e.eval σ)</code>, using <code>write_same h x _</code> as the “the left heap has this cell” premise of <code>union_of_some</code>. Both sides now agree and <code>rw</code>’s trailing <code>rfl</code> closes it." },
        { "tac": "· rw [write_other (Heap.union h hFrame) l x (e.eval σ) hxl]",
          "h": "Off the written cell: the left side becomes <code>Heap.union h hFrame x</code>." },
        { "tac": "have hwx : Heap.write h l (e.eval σ) x = h x := write_other h l x (e.eval σ) hxl",
          "h": "The same fact about the <i>small</i> heap, named because both branches of the next split need it." },
        { "tac": "cases hx : h x with",
          "h": "A split on an expression rather than a hypothesis, giving branches <code>none</code> and <code>some w</code>. The <code>hx :</code> prefix records the equation; without it the split buys nothing, because <code>rw [write_other …]</code> has already removed every occurrence of <code>h x</code> from the goal." },
        { "tac": "| none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]",
          "h": "Both sides fall through to <code>hFrame x</code>. On the right the premise wanted is <code>Heap.write h l (e.eval σ) x = none</code>, which is <code>hwx</code> then <code>hx</code> — <code>hwx.trans hx</code> is <code>Eq.trans</code> in dot notation, composing <code>a = b</code> with <code>b = c</code>." },
        { "tac": "| some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]",
          "h": "Identical with the other lemma: both sides are <code>some w</code>." }
      ],

      "deep": [
        { "t": "trace", "title": "heapLocal_write, the interesting states",
          "start": "l : Loc\ne : Atom\n⊢ HeapLocal (Cmd.write l e)",
          "steps": [
            { "tac": "intro σ h hFrame s' hd hex\ncases hex with | write hl =>",
              "state": "case write\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\n⊢ { store := { store := σ, heap := h }.store,\n            heap := { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.heap.disjoint\n      hFrame ∧\n    ∃ r,\n      Exec (Cmd.write l e) { store := σ, heap := h.union hFrame } r ∧\n        r.store =\n            { store := { store := σ, heap := h }.store,\n                heap := { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.store ∧\n          r.heap =\n            { store := { store := σ, heap := h }.store,\n                    heap :=\n                      { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.heap.union\n              hFrame",
              "h": "This is a goal with nothing cleaned up: every <code>σ</code> and <code>h</code> wrapped in a projection out of a state you never built. Unreadable, and mathematically irrelevant. The <code>have hl'</code> and the <code>show</code> exist to get out of it." },
            { "tac": "intro x   (inside the hdw block)",
              "state": "l : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nx : Loc\n⊢ h.write l (Atom.eval σ e) x = none ∨ hFrame x = none",
              "h": "Small and clean, because you wrote <code>hdw</code>’s type yourself. Note <code>hl'</code> beside the projection-laden <code>hl</code>: same fact, usable form." },
            { "tac": "rcases hd x with hx | hx; by_cases hxl : x = l",
              "state": "case pos\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nx : Loc\nhx : h x = none\nhxl : x = l\n⊢ h.write l (Atom.eval σ e) x = none ∨ hFrame x = none",
              "h": "The vacuous branch, in words: <code>hd</code> chose “the small heap is empty at <code>x</code>”, but <code>x</code> is the cell being written and <code>Exec.write</code>’s side condition says the small heap owns it. Both cannot hold — and killing this branch is what leaves the frame as the one that must be empty at <code>l</code>." },
            { "tac": "(after the refine)",
              "state": "case write\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nhdw : (h.write l (Atom.eval σ e)).disjoint hFrame\n⊢ { store := σ, heap := (h.union hFrame).write l (Atom.eval σ e) }.heap =\n    { store := { store := σ, heap := h }.store,\n            heap := { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.heap.union\n      hFrame",
              "h": "One goal left, and it is the heap equation — but no lemma in the library is about <code>{ store := σ, heap := … }.heap</code>." },
            { "tac": "show … ; funext x",
              "state": "case write\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nhdw : (h.write l (Atom.eval σ e)).disjoint hFrame\nx : Loc\n⊢ (h.union hFrame).write l (Atom.eval σ e) x = (h.write l (Atom.eval σ e)).union hFrame x",
              "h": "Now it is a statement about heaps at a point, in exactly the vocabulary of <code>write_same</code>, <code>write_other</code>, <code>union_of_some</code>, <code>union_of_none</code>." },
            { "tac": "by_cases hxl : x = l; subst hxl",
              "state": "case pos\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nx : Loc\nhl : { store := σ, heap := h }.heap x = some old✝\nhl' : h x = some old✝\nhdw : (h.write x (Atom.eval σ e)).disjoint hFrame\n⊢ (h.union hFrame).write x (Atom.eval σ e) x = (h.write x (Atom.eval σ e)).union hFrame x",
              "h": "<code>l</code> has vanished from the whole context — <code>hl'</code> and <code>hdw</code> included. That is why the following <code>rw</code> is written <code>write_same (Heap.union h hFrame) x (e.eval σ)</code>." },
            { "tac": "(neg branch, after rw and have hwx)",
              "state": "case neg\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nhdw : (h.write l (Atom.eval σ e)).disjoint hFrame\nx : Loc\nhxl : ¬x = l\nhwx : h.write l (Atom.eval σ e) x = h x\n⊢ h.union hFrame x = (h.write l (Atom.eval σ e)).union hFrame x",
              "h": "The left side is plain <code>h.union hFrame x</code>; the right side is the union of the written heap, which <code>hwx</code> says agrees with <code>h</code> at <code>x</code>. Splitting on <code>h x</code> finishes both." } ],
          "done": "No goals." },

        { "t": "state",
          "src": "error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  (h.union hFrame).write x (Atom.eval σ e) x\nin the target expression\n  { store := σ, heap := (h.union hFrame).write x (Atom.eval σ e) }.heap x =\n    { store := { store := σ, heap := h }.store,\n            heap := { store := σ, heap := h }.heap.write x (Atom.eval { store := σ, heap := h }.store e) }.heap.union\n      hFrame x",
          "cap": "what Lean says if you go straight from the refine to funext, skipping the show" },

        { "t": "detail", "title": "The heap equation on its own", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p", "h": "Pull the second half out and it needs <i>no</i> hypotheses — not disjointness, not that <code>h</code> owns <code>l</code>:" },
            { "t": "code", "tag": "illustration",
              "src": "-- the heap equation half of heapLocal_write needs no disjointness at all\ntheorem write_union_no_disjointness (h hFrame : Heap) (l : Loc) (v : Val) :\n    Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame := by\n  funext x\n  by_cases hxl : x = l\n  · subst hxl\n    rw [write_same (Heap.union h hFrame) x v, union_of_some hFrame (write_same h x v)]\n  · rw [write_other (Heap.union h hFrame) l x v hxl]\n    have hwx : Heap.write h l v x = h x := write_other h l x v hxl\n    cases hx : h x with\n    | none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]\n    | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]",
              "cap": "not in the corpus — compiles against prelude/m8.lean" },
            { "t": "p", "h": "So the side conditions in <code>heapLocal_write</code> are all spent on the <i>other</i> two obligations: <code>h l = some old</code> to run the write on the big heap at all, disjointness for the domain conjunct. The equation itself is a pure fact about <code>write</code> and left-biased union. The next exercise is where that stops being true." } ] }
      ],

      "pitfall": "You will skip <code>have hl'</code> and write <code>rw [hl] at hx</code>. Lean answers <code>Tactic `rewrite` failed: Did not find an occurrence of the pattern { store := σ, heap := h }.heap x in the target expression h x = none</code>. The message is exactly true and still easy to misread: it is not saying the fact is wrong, it is saying the <i>syntax</i> does not occur. The same trap fires again after the <code>refine</code>, where the fix is <code>show</code> instead of <code>have</code>.",

      "variants": "Delete <code>hd</code> and exactly one thing breaks: the conjunct <code>Heap.disjoint (Heap.write h l v) hFrame</code>. Take <code>h = Heap.singleton 0 7</code> and <code>hFrame = Heap.singleton 0 99</code>, which are not disjoint, and run <code>.write 0 (.const 5)</code>: the resulting heap still owns <code>0</code>, so it still overlaps the frame. The heap <i>equation</i> survives untouched — the illustration above proves it with no hypothesis at all. Hold on to that asymmetry: for <code>write</code>, disjointness only keeps the bookkeeping honest, and the next exercise is the one where it is load-bearing. Reverse the union to <code>Heap.union hFrame h</code> and it is the <code>Exec.write</code> side condition that breaks instead, for the same reason as in the load case."
    },

    {
      "t": "ex",
      "id": "m8-3",
      "name": "heapLocal_free",
      "hard": true,

      "why": "The one command that removes a cell, and so the one place where the frame’s disjointness does real work rather than bookkeeping. In <code>write</code> the two heaps never really meet; in <code>free</code> they do, and if the disjointness argument goes wrong the theorem is not merely unproved but false.",
      "setup": "In scope: <code>erase_same : Heap.erase h l l = none</code>, <code>erase_other : x ≠ l → Heap.erase h l x = h x</code>, and the union lemmas. <code>Heap.erase h l</code> is <code>fun x => if x = l then none else h x</code>: it shrinks the domain by exactly one cell.",
      "goal": "theorem heapLocal_free (l : Loc) : HeapLocal (.free l)",

      "hints": [
        "Same skeleton as <code>write</code>: a <code>have</code> for the disjointness, then a <code>refine</code>, then <code>show</code> + <code>funext</code> + a split on <code>x = l</code>. Copy it and fill in the branches.",
        "The disjointness half is <i>easier</i> than for <code>write</code>: erasing only ever turns values into <code>none</code>, so the left disjunct is always the one you want. That is why <code>left</code> comes before the split on <code>x = l</code> rather than inside it.",
        "The interesting branch is <code>x = l</code> in the heap equation. On the left, <code>erase_same</code> gives <code>none</code>. On the right, <code>union_of_none hFrame (erase_same h x)</code> makes the union fall through to <code>hFrame x</code>. So the goal becomes <code>none = hFrame x</code>: you must prove the frame does not own the freed cell.",
        "Which is where disjointness enters: <code>rcases hd x</code>. The branch with <code>h x = none</code> contradicts <code>hl' : h x = some v✝</code>; the branch with <code>hFrame x = none</code> is the goal up to <code>.symm</code>."
      ],

      "sol": "theorem heapLocal_free (l : Loc) : HeapLocal (.free l) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | free hl =>\n      have hl' : h l = _ := hl\n      have hde : Heap.disjoint (Heap.erase h l) hFrame := by\n        intro x\n        rcases hd x with hx | hx\n        · left\n          by_cases hxl : x = l\n          · subst hxl; exact erase_same h x\n          · rw [erase_other h l x hxl]; exact hx\n        · exact Or.inr hx\n      refine ⟨hde, ⟨σ, Heap.erase (Heap.union h hFrame) l⟩,\n              Exec.free (union_of_some hFrame hl'), rfl, ?_⟩\n      show Heap.erase (Heap.union h hFrame) l = Heap.union (Heap.erase h l) hFrame\n      funext x\n      by_cases hxl : x = l\n      · subst hxl\n        rw [erase_same (Heap.union h hFrame) x,\n            union_of_none hFrame (erase_same h x)]\n        rcases hd x with hx | hx\n        · rw [hx] at hl'; exact absurd hl' (by simp)\n        · exact hx.symm\n      · rw [erase_other (Heap.union h hFrame) l x hxl]\n        have hex' : Heap.erase h l x = h x := erase_other h l x hxl\n        cases hx : h x with\n        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hex'.trans hx)]\n        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hex'.trans hx)]",

      "expl": "Because <code>h l = some v</code>, disjointness forces <code>hFrame l = none</code>; so erasing <code>l</code> from the union really does leave <code>none</code> there, matching <code>(erase h l) ∪ hFrame</code>. If the frame were allowed to own <code>l</code> too, freeing your own cell would silently expose the frame’s value at the same address, and locality would fail — which is the bug this logic exists to make unstatable.",

      "walk": [
        { "tac": "intro σ h hFrame s' hd hex", "h": "The six binders." },
        { "tac": "cases hex with", "h": "Named form, for the side condition." },
        { "tac": "| free hl =>", "h": "Binds <code>hl : { store := σ, heap := h }.heap l = some v✝</code> and fixes <code>s' = ⟨σ, Heap.erase h l⟩</code>." },
        { "tac": "have hl' : h l = _ := hl", "h": "The same restatement as in the write case, needed for the same reason." },
        { "tac": "have hde : Heap.disjoint (Heap.erase h l) hFrame := by", "h": "Obligation (a): the erased heap is still disjoint from the frame." },
        { "tac": "intro x", "h": "Fix a location." },
        { "tac": "rcases hd x with hx | hx", "h": "Split the assumption at <code>x</code>." },
        { "tac": "· left",
          "h": "Commit to <code>Heap.erase h l x = none</code> now, before the case split — legitimate here because erasing never creates a value, unlike <code>write</code>, where the choice of disjunct depended on the branch." },
        { "tac": "by_cases hxl : x = l", "h": "At the erased cell, or elsewhere." },
        { "tac": "· subst hxl; exact erase_same h x", "h": "At the erased cell the answer is <code>none</code> by definition, and <code>subst</code> has renamed <code>l</code> to <code>x</code>, so the lemma is applied as <code>erase_same h x</code>." },
        { "tac": "· rw [erase_other h l x hxl]; exact hx", "h": "Elsewhere nothing changed, so <code>hx</code> is already the goal." },
        { "tac": "· exact Or.inr hx", "h": "Second branch: the frame is empty at <code>x</code>, which is the right disjunct unchanged." },
        { "tac": "refine ⟨hde, ⟨σ, Heap.erase (Heap.union h hFrame) l⟩,\n        Exec.free (union_of_some hFrame hl'), rfl, ?_⟩",
          "h": "Five slots. The witness erases <code>l</code> from the big heap; <code>Exec.free</code> needs the cell to exist there; the store is untouched, so <code>rfl</code>; the heap equation is left open." },
        { "tac": "show Heap.erase (Heap.union h hFrame) l = Heap.union (Heap.erase h l) hFrame",
          "h": "Strip the projections so the erase and union lemmas can match." },
        { "tac": "funext x", "h": "Equality of heaps down to equality at each location." },
        { "tac": "by_cases hxl : x = l", "h": "The freed cell versus everything else." },
        { "tac": "· subst hxl", "h": "<code>l</code> becomes <code>x</code> everywhere, <code>hl'</code> and <code>hde</code> included." },
        { "tac": "rw [erase_same (Heap.union h hFrame) x,\n    union_of_none hFrame (erase_same h x)]",
          "h": "Left: erasing at the erased cell gives <code>none</code>. Right: the small heap is <code>none</code> there, so the left-biased union defers to the frame. The goal is now <code>none = hFrame x</code> — a statement purely about the frame." },
        { "tac": "rcases hd x with hx | hx",
          "h": "And this is the moment. You need <code>hFrame x = none</code>, and the only source of it is disjointness." },
        { "tac": "· rw [hx] at hl'; exact absurd hl' (by simp)",
          "h": "The branch where <code>h x = none</code> is impossible, because <code>hl'</code> says the command owned that cell. Rewriting turns <code>hl'</code> into <code>none = some v✝</code>." },
        { "tac": "· exact hx.symm",
          "h": "The branch that survives. <code>hx : hFrame x = none</code> against a goal <code>none = hFrame x</code>, so <code>Eq.symm</code> in dot form." },
        { "tac": "· rw [erase_other (Heap.union h hFrame) l x hxl]",
          "h": "Off the freed cell, erasing changed nothing on the left, so the left side is <code>Heap.union h hFrame x</code>." },
        { "tac": "have hex' : Heap.erase h l x = h x := erase_other h l x hxl",
          "h": "The same fact about the small heap, named for both branches of the next split." },
        { "tac": "cases hx : h x with", "h": "Split on whether the small heap owns <code>x</code>, recording the equation." },
        { "tac": "| none => rw [union_of_none hFrame hx, union_of_none hFrame (hex'.trans hx)]",
          "h": "Both unions fall through to <code>hFrame x</code>." },
        { "tac": "| some w => rw [union_of_some hFrame hx, union_of_some hFrame (hex'.trans hx)]",
          "h": "Both unions return <code>some w</code>." }
      ],

      "deep": [
        { "t": "trace", "title": "heapLocal_free, the interesting states",
          "start": "l : Loc\n⊢ HeapLocal (Cmd.free l)",
          "steps": [
            { "tac": "intro σ h hFrame s' hd hex\ncases hex with | free hl =>",
              "state": "case free\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\n⊢ { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec (Cmd.free l) { store := σ, heap := h.union hFrame } r ∧\n        r.store = { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.store ∧\n          r.heap =\n            { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap.union\n              hFrame",
              "h": "<code>s'</code> is gone, replaced by <code>⟨σ, Heap.erase h l⟩</code> written out inside every projection." },
            { "tac": "(inside hde, pos branch)",
              "state": "case pos\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhl' : h l = some v✝\nx : Loc\nhx : h x = none\nhxl : x = l\n⊢ h.erase l x = none",
              "h": "The goal is <i>only</i> the left disjunct, because <code>left</code> was applied before the split. There is no contradiction to find here; erasing at <code>l</code> genuinely gives <code>none</code>." },
            { "tac": "(after the refine)",
              "state": "case free\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhl' : h l = some v✝\nhde : (h.erase l).disjoint hFrame\n⊢ { store := σ, heap := (h.union hFrame).erase l }.heap =\n    { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap.union hFrame",
              "h": "The heap equation, wrapped; <code>hde</code> has already discharged the first conjunct." },
            { "tac": "show …; funext x; by_cases hxl : x = l; subst hxl",
              "state": "case pos\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nx : Loc\nhl : { store := σ, heap := h }.heap x = some v✝\nhl' : h x = some v✝\nhde : (h.erase x).disjoint hFrame\n⊢ (h.union hFrame).erase x x = (h.erase x).union hFrame x",
              "h": "Clean, with <code>l</code> replaced by <code>x</code> throughout." },
            { "tac": "rw [erase_same …, union_of_none …]",
              "state": "case pos\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nx : Loc\nhl : { store := σ, heap := h }.heap x = some v✝\nhl' : h x = some v✝\nhde : (h.erase x).disjoint hFrame\n⊢ none = hFrame x",
              "h": "<b>The whole theorem, in one goal.</b> Erasing the cell from the union left <code>none</code> there; the reassembled heap reads <code>hFrame x</code> there. They agree exactly when the frame does not own <code>x</code> — and it does not, because the command did, and the two are disjoint. Every other line of this proof is bookkeeping around this." },
            { "tac": "(neg branch, after rw and have hex')",
              "state": "case neg\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhl' : h l = some v✝\nhde : (h.erase l).disjoint hFrame\nx : Loc\nhxl : ¬x = l\nhex' : h.erase l x = h x\n⊢ h.union hFrame x = (h.erase l).union hFrame x",
              "h": "Away from the freed cell, both sides are unions that agree because the erased heap agrees with <code>h</code> at <code>x</code>." } ],
          "done": "No goals." },

        { "t": "steps", "title": "The mathematical content, stripped of Lean",
          "items": [
            { "k": "Claim", "h": "If <code>h ⊥ hFrame</code> and <code>l ∈ dom h</code>, then <code>(h ∪ hFrame) ∖ l = (h ∖ l) ∪ hFrame</code>." },
            { "k": "At l", "h": "Left: <code>l</code> was erased, so <code>none</code>. Right: <code>h ∖ l</code> is undefined at <code>l</code>, so the union defers to <code>hFrame l</code>. These agree <i>iff</i> <code>l ∉ dom hFrame</code>, which follows from <code>l ∈ dom h</code> and disjointness. <b>The only place the hypotheses are used.</b>" },
            { "k": "Away from l", "h": "Erasing does nothing on either side, so both reduce to <code>(h ∪ hFrame) x</code>. No hypothesis needed." },
            { "k": "Against write", "h": "For <code>write</code> the corresponding point gives <code>some v</code> on both sides regardless of the frame, so disjointness is needed only for the domain conjunct. <code>free</code> needs it for the equation as well." } ] }
      ],

      "pitfall": "The direction of the final equality. After the two rewrites the goal is <code>none = hFrame x</code> and your hypothesis is <code>hx : hFrame x = none</code>; <code>exact hx</code> fails with a type mismatch that reads like nonsense until you look twice. The fix is <code>hx.symm</code>. The goal comes out backwards because <code>rw</code> rewrote the left-hand side to <code>none</code> and left the right alone, and no rule says a goal must end up in the orientation you find natural.",

      "variants": "Let the frame own <code>l</code> too — that is, drop <code>hd</code>. Take <code>h = Heap.singleton 0 7</code>, <code>hFrame = Heap.singleton 0 99</code>, <code>c = .free 0</code>. The small run leaves <code>Heap.empty</code>, so the reassembled heap <code>Heap.empty ∪ hFrame</code> maps <code>0</code> to <code>99</code>. The big run starts from <code>h ∪ hFrame</code>, which maps <code>0</code> to <code>7</code>, and erases it, giving <code>none</code>. The two differ at location <code>0</code>: locality is false, at one point, for one reason. Weaken disjointness to compatibility (agreement on the overlap) and this same witness still kills it, since the two heaps disagree at <code>0</code> — but so does <code>hFrame = Heap.singleton 0 7</code>, which is compatible with <code>h</code> and still ends up disagreeing after the free."
    },

    {
      "t": "ex",
      "id": "m8-4",
      "name": "heapLocal_seq",
      "hard": false,

      "why": "Locality composes, which is what makes it a side condition on the language rather than an obligation per program. It is also the exercise that pays for the extra conjunct: you need disjointness in the middle of the sequence, and there is nowhere else to get it.",
      "setup": "In scope: <code>Exec.seq {s s' s'' c₁ c₂} (h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'') : Exec (c₁ ;; c₂) s s''</code>. The middle state is implicit, which is the source of the one wrinkle here.",
      "goal": "theorem heapLocal_seq {c₁ c₂ : Cmd} (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) :\n    HeapLocal (c₁ ;; c₂)",

      "hints": [
        "Apply <code>h₁</code> to get from the start to the middle, then <code>h₂</code> from the middle to the end, then glue the two lifted runs with <code>Exec.seq</code>.",
        "After <code>cases hex with | seq hex₁ hex₂</code>, look at the context: the intermediate state is there but it is called <code>s'✝</code> and you cannot type that. <code>rename_i sMid</code> names it. <code>rename_i</code> gives names to inaccessible hypotheses counting <i>from the right</i>, skipping the accessible ones, so with one argument it lands on the most recent <code>✝</code>.",
        "Applying <code>h₂</code> needs disjointness for the <i>middle</i> heap and the frame. That is <code>hdMid</code>, the first component of what <code>h₁</code> just gave you.",
        "Last wrinkle: <code>h₂</code> produced <code>Exec c₂ ⟨sMid.store, sMid.heap ∪ hFrame⟩ r₂</code> while <code>Exec.seq hr₁ ?_</code> wants <code>Exec c₂ r₁ r₂</code>. Prove <code>heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩</code> by <code>rw [← hst₁, ← hhp₁]</code> — rewriting backwards turns the right-hand side into <code>⟨r₁.store, r₁.heap⟩</code>, structure eta makes that <code>r₁</code>, and <code>rw</code>’s trailing <code>rfl</code> closes it. Then <code>rw [heq]</code> in the main goal."
      ],

      "sol": "theorem heapLocal_seq {c₁ c₂ : Cmd} (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) :\n    HeapLocal (c₁ ;; c₂) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | seq hex₁ hex₂ =>\n      rename_i sMid\n      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁\n      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂\n      refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩\n      have heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩ := by\n        rw [← hst₁, ← hhp₁]\n      rw [heq]\n      exact hr₂",

      "expl": "<code>hdMid</code> comes out of the first application and goes straight into the second; without the disjointness conjunct you would be stranded halfway. What remains is a wrinkle about notation, not content: <code>h₂</code> hands you a run out of <code>⟨sMid.store, sMid.heap ∪ hFrame⟩</code> while the glued execution wants one out of <code>r₁</code>, and <code>heq</code> shows they are the same state.",

      "walk": [
        { "tac": "intro σ h hFrame s' hd hex",
          "h": "The six binders. <code>h₁</code> and <code>h₂</code>, the locality assumptions for the halves, were bound as theorem arguments." },
        { "tac": "cases hex with", "h": "Only <code>Exec.seq</code> can produce an execution of a sequence." },
        { "tac": "| seq hex₁ hex₂ =>",
          "h": "Names the two sub-executions. The intermediate state is an <i>implicit</i> field, so it is introduced and left inaccessible as <code>s'✝</code>." },
        { "tac": "rename_i sMid",
          "h": "Names it. Without a name you cannot instantiate <code>h₁</code> at the middle state, because you cannot write the state down. Nothing mathematical happens; the proof simply becomes writable." },
        { "tac": "obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁",
          "h": "Applies the first locality assumption to the first half and destructures the result: the middle disjointness, the lifted middle state, its execution, and the two equations. Five names for the five conjuncts of <code>HeapLocal</code>’s conclusion." },
        { "tac": "obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂",
          "h": "The same for the second half, starting from the middle state, with <code>hdMid</code> as the disjointness hypothesis. <b>This is the line that is impossible without the extra conjunct.</b>" },
        { "tac": "refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩",
          "h": "End disjointness and both equations come from <code>h₂</code>; the final state is <code>r₂</code>. Only the second half of the glued execution is left open." },
        { "tac": "have heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩ := by",
          "h": "Assert that the two spellings of the middle state name the same state." },
        { "tac": "rw [← hst₁, ← hhp₁]",
          "h": "Backwards along the two equations: <code>sMid.store</code> becomes <code>r₁.store</code> and <code>sMid.heap.union hFrame</code> becomes <code>r₁.heap</code>, leaving <code>r₁ = ⟨r₁.store, r₁.heap⟩</code>, which structure eta makes true by <code>rfl</code> — so the block needs no closing tactic." },
        { "tac": "rw [heq]", "h": "Turns the goal <code>Exec c₂ r₁ r₂</code> into <code>Exec c₂ ⟨sMid.store, sMid.heap ∪ hFrame⟩ r₂</code>." },
        { "tac": "exact hr₂", "h": "Which is what <code>h₂</code> handed over." }
      ],

      "deep": [
        { "t": "trace", "title": "heapLocal_seq, tactic by tactic",
          "start": "c₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\n⊢ HeapLocal (c₁ ;; c₂)",
          "steps": [
            { "tac": "intro σ h hFrame s' hd hex\ncases hex with | seq hex₁ hex₂ =>",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\ns'✝ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s'✝\nhex₂ : Exec c₂ s'✝ s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Look at <code>s'✝ : State</code>. It exists, both sub-executions mention it, and you cannot refer to it. That is the entire reason the next line exists." },
            { "tac": "rename_i sMid",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Same context, one name changed." },
            { "tac": "obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Five new hypotheses. <code>hdMid : sMid.heap.disjoint hFrame</code> is the one to watch." },
            { "tac": "obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\nhdEnd : s'.heap.disjoint hFrame\nr₂ : State\nhr₂ : Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nhst₂ : r₂.store = s'.store\nhhp₂ : r₂.heap = s'.heap.union hFrame\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Five more, and everything the goal asks for is now in the context except the execution." },
            { "tac": "refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\nhdEnd : s'.heap.disjoint hFrame\nr₂ : State\nhr₂ : Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nhst₂ : r₂.store = s'.store\nhhp₂ : r₂.heap = s'.heap.union hFrame\n⊢ Exec c₂ r₁ r₂",
              "h": "One goal, and it is a mismatch of spelling rather than of content: <code>hr₂</code> is about <code>{ store := sMid.store, heap := sMid.heap.union hFrame }</code>, the goal about <code>r₁</code>." },
            { "tac": "have heq : … := by rw [← hst₁, ← hhp₁]\nrw [heq]",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\nhdEnd : s'.heap.disjoint hFrame\nr₂ : State\nhr₂ : Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nhst₂ : r₂.store = s'.store\nhhp₂ : r₂.heap = s'.heap.union hFrame\nheq : r₁ = { store := sMid.store, heap := sMid.heap.union hFrame }\n⊢ Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂",
              "h": "And <code>exact hr₂</code> closes it." } ],
          "done": "No goals." },

        { "t": "detail", "title": "Why <code>exact hr₂</code> does not just work", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p", "h": "<code>r₁</code> is an opaque variable; all you know about it is two <i>propositional</i> equations, and definitional equality cannot see through a hypothesis. So:" },
            { "t": "state",
              "src": "error: Type mismatch\n  hr₂\nhas type\n  Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nbut is expected to have type\n  Exec c₂ r₁ r₂",
              "cap": "what happens if you drop the have/rw" },
            { "t": "p", "h": "The part that <i>is</i> definitional is structure eta: <code>r₁</code> and <code>⟨r₁.store, r₁.heap⟩</code> are interchangeable with no proof at all. So the job of <code>rw [← hst₁, ← hhp₁]</code> is to manoeuvre the goal into that shape." } ] },

        { "t": "detail", "title": "The <code>obtain</code> shortcut that silently does not work", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p", "h": "<code>Exec.seq</code> has three fields — the middle state and the two sub-executions — so it is natural to try <code>obtain ⟨sMid, hex₁, hex₂⟩ := hex</code> and skip the <code>rename_i</code>. Lean accepts the line. Here is the context immediately afterwards:" },
            { "t": "state",
              "src": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\ns'✝ : State\nh₁✝ : Exec c₁ { store := σ, heap := h } s'✝\nh₂✝ : Exec c₂ s'✝ s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "cap": "after obtain ⟨sMid, hex₁, hex₂⟩ := hex" },
            { "t": "p", "h": "All three names were dropped, and the replacements are not arbitrary: <code>s'</code>, <code>h₁</code> and <code>h₂</code> are <code>Exec.seq</code>’s own field names. A name already in scope is not overwritten, so Lean marks the <i>incoming</i> ones inaccessible instead — which is why your locality assumptions survive and the line raises nothing at all." },
            { "t": "p", "h": "The bill arrives one line later:" },
            { "t": "state",
              "src": "error(lean.unknownIdentifier): Unknown identifier `sMid`\nerror(lean.unknownIdentifier): Unknown identifier `hex₁`",
              "cap": "reported at the use, not at the obtain" },
            { "t": "p", "h": "<code>cases … with | seq hex₁ hex₂</code> does name the explicit fields; only the implicit middle state needs <code>rename_i</code>." } ] }
      ],

      "pitfall": "The shortcut above — it reports no error, which is the trap, and then the next line that mentions <code>sMid</code> or <code>hex₁</code> fails with <code>Unknown identifier</code> at the <i>use</i>, saying nothing about the <code>obtain</code> that swallowed the names. Writing <code>s'✝</code> by hand is not an option either: <code>✝</code> is not an input character.",

      "variants": "Remove the <code>Heap.disjoint s'.heap hFrame</code> conjunct from <code>HeapLocal</code> and this proof dies at the second <code>obtain</code>: <code>h₂</code> demands disjointness for <code>sMid.heap</code>, you have it only for the initial heap, and no lemma converts between them — there cannot be one, since it is exactly the fact that was deleted. Apply <code>h₂</code> first instead and you get nowhere, because the second command’s run starts at a state you have not produced yet. And note what is <i>not</i> needed: nothing about <code>c₁</code> and <code>c₂</code> individually, no determinism, no termination. Locality composes for the reason simulations compose."
    },

    { "t": "sec", "s": "The frame rule, discharged" },

    {
      "t": "ex",
      "id": "m8-5",
      "name": "hoare_frame",
      "hard": true,

      "why": "<b>The theorem the whole course exists to prove.</b> Eight lines. Once it is there, the rest of the workbook is composition.",
      "setup": "Everything is already available. <code>Hoare P c Q</code> is <code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>, and <code>(P ∗ R) σ h</code> is <code>∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ R σ h₂</code>. No M4 lemma about <code>∗</code> is needed; you go through the definition in both directions.",
      "goal": "theorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R)",

      "hints": [
        "<code>intro σ h hstar</code>, then destructure <code>hstar</code> with the six-slot star pattern.",
        "Then two applications, in order. <code>hc σ hP hp</code> runs the command on the small heap. <code>hlocal σ hP hR s' hd hex</code> lifts that run to the union. Both are literally applications — the arguments are the things you already have.",
        "Before assembling, kill <code>hu : h = hP.union hR</code> with <code>subst hu</code>. Otherwise the goal still mentions <code>h</code> while the lifted execution mentions <code>hP.union hR</code>, and the <code>refine</code> fails on an application type mismatch.",
        "The final <code>refine</code> takes eight components: <code>⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩</code> — the state, its execution, then the cut <code>s'.heap</code> / <code>hR</code>, their disjointness, the union equation, and the two halves of the star. The union equation the star wants is <code>r.heap = Heap.union s'.heap hR</code>, which is <code>hrhp</code> unchanged.",
        "Goal 1 is <code>Q r.store s'.heap</code> against <code>hq : Q s'.store s'.heap</code>; <code>rw [hrst]</code> bridges them. Goal 2 is <code>R r.store hR</code>, which is what <code>Preserves</code> was defined to give: <code>hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr</code>."
      ],

      "sol": "theorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R) := by\n  intro σ h hstar\n  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar\n  obtain ⟨s', hex, hq⟩ := hc σ hP hp\n  obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex\n  subst hu\n  refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩\n  · rw [hrst]; exact hq\n  · exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",

      "expl": "Split the heap, run the command small, lift the run, reassemble, re-establish <code>R</code>: one line each, in that order. The only decision in the whole proof is the cut in the postcondition — <code>s'.heap</code> for the <code>Q</code> part, <code>hR</code> untouched for the <code>R</code> part — and <code>HeapLocal</code>’s conclusion was stated so that the disjointness and the union equation it needs are already in the exact form the star demands.",

      "walk": [
        { "tac": "intro σ h hstar",
          "h": "Opens the <code>Hoare</code> in the conclusion. You now owe an execution and a postcondition, given <code>P ∗ R</code> of <code>h</code>." },
        { "tac": "obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar",
          "h": "<b>Split.</b> The two heaps, their disjointness, the union equation, and the two assertions." },
        { "tac": "obtain ⟨s', hex, hq⟩ := hc σ hP hp",
          "h": "<b>Run it small.</b> Feed the small heap and <code>hp : P σ hP</code> to the triple you were given. Out comes a final state, an execution on the small heap, and <code>Q</code> of that state." },
        { "tac": "obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex",
          "h": "<b>Lift it.</b> Locality takes the small run and the frame heap <code>hR</code> — the heap that <code>R</code> describes, not <code>R</code> itself — and returns the end disjointness, the big final state, its execution, and the two equations." },
        { "tac": "subst hu",
          "h": "Replaces <code>h</code> by <code>hP.union hR</code> everywhere, the goal included, so the goal’s execution and <code>hrex</code> start from the same heap." },
        { "tac": "refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩",
          "h": "<b>Reassemble.</b> Eight components flattened out of <code>∃ s', Exec ∧ (∃ h₁ h₂, disjoint ∧ eq ∧ Q ∧ R)</code>. <code>hdEnd</code> fills the disjointness slot and is available only because <code>HeapLocal</code> carries it; <code>hrhp : r.heap = s'.heap.union hR</code> fills the union slot with no massaging at all." },
        { "tac": "· rw [hrst]; exact hq",
          "h": "Goal 1 is <code>Q r.store s'.heap</code>. <code>hrst : r.store = s'.store</code> rewrites it to <code>hq</code>: the frame did not change what the command did to the store, so <code>Q</code> still holds." },
        { "tac": "· exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",
          "h": "<b>Re-establish R.</b> Goal 2 is <code>R r.store hR</code> — untouched heap, moved store. <code>Preserves</code> takes the initial state, the final state, the execution between them, the frame heap, and <code>R</code> at the old store. You build the initial state by hand because <code>Preserves</code> is stated about states rather than about a store-and-heap pair." }
      ],

      "deep": [
        { "t": "trace", "title": "hoare_frame, tactic by tactic",
          "start": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\n⊢ Hoare (P ∗ R) c (Q ∗ R)",
          "steps": [
            { "tac": "intro σ h hstar",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh : Heap\nhstar : (P ∗ R) σ h\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "Produce a final state, an execution from <code>⟨σ, h⟩</code>, and <code>Q ∗ R</code> of it." },
            { "tac": "obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "The star’s six pieces are in the context; the goal is unchanged." },
            { "tac": "obtain ⟨s', hex, hq⟩ := hc σ hP hp",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "<code>hex</code> runs in <code>hP</code>; the goal wants a run in <code>h</code>. That distance is the whole reason <code>HeapLocal</code> exists." },
            { "tac": "obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "Closed: <code>hrex</code> starts from <code>hP.union hR</code>. And <code>hdEnd</code> is sitting there for the reassembly." },
            { "tac": "subst hu",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ ∃ s', Exec c { store := σ, heap := hP.union hR } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "<code>h</code> is gone and the goal starts from <code>hP.union hR</code>, matching <code>hrex</code> exactly. Do this <i>before</i> the <code>refine</code>." },
            { "tac": "refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩",
              "state": "case refine_1\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ Q r.store s'.heap",
              "h": "First hole: <code>Q</code> at the new store, on the old small heap." },
            { "tac": "· rw [hrst]; exact hq",
              "state": "case refine_2\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ R r.store hR",
              "h": "Second hole: <code>R</code> at the new store, on the untouched frame heap. There is no way to reach it from <code>hr : R σ hR</code> alone, and this is the goal <code>Preserves</code> was invented for." } ],
          "done": "No goals." },

        { "t": "detail", "title": "The same proof over <code>HeapLocalWeak</code>, stranded", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p", "h": "Worth seeing rather than being told. Take the definition without the disjointness conjunct and carry the proof as far as it will go:" },
            { "t": "code", "tag": "illustration",
              "src": "example {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocalWeak c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R) := by\n  intro σ h hstar\n  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar\n  obtain ⟨s', hex, hq⟩ := hc σ hP hp\n  obtain ⟨r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex\n  subst hu\n  refine ⟨r, hrex, s'.heap, hR, ?_, hrhp, ?_, ?_⟩\n  · sorry                       -- ⊢ s'.heap.disjoint hR  — nothing proves this\n  · rw [hrst]; exact hq\n  · exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",
              "cap": "not in the corpus — compiles with one sorry against prelude/m8.lean" },
            { "t": "p", "h": "Seven of the eight components go through. The first <code>?_</code> does not:" },
            { "t": "state",
              "src": "case refine_1\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocalWeak c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ s'.heap.disjoint hR",
              "cap": "the goal at the sorry" },
            { "t": "p", "h": "Every hypothesis about disjointness in that context is <code>hd</code>, which is about <code>hP</code>. <code>hrhp</code> pins down <code>r.heap</code> and says nothing about <code>s'.heap</code> against <code>hR</code>. The information is not there to be derived." } ] }
      ],

      "pitfall": "Forgetting <code>subst hu</code>, or doing the <code>refine</code> first and hoping to repair it. The goal keeps saying <code>Exec c { store := σ, heap := h } r</code> while <code>hrex</code> says <code>Exec c { store := σ, heap := hP.union hR } r</code>, and Lean reports it from inside <code>And.intro</code>, which is a confusing place to be told:<br><code>Application type mismatch: The argument hrex has type Exec c { store := σ, heap := hP.union hR } r but is expected to have type Exec c { store := σ, heap := h } r</code>. <code>h</code> and <code>hP.union hR</code> are propositionally equal, not definitionally, so only a rewrite closes that gap, and <code>subst</code> is the cheapest one.",

      "variants": "Drop <code>hpres</code> and the second hole is unprovable — the <code>x := 1</code> counterexample earlier in the chapter refutes it with an empty heap. Drop <code>hlocal</code> and you cannot start: <code>hc</code> gives an execution on <code>hP</code> and a triple says nothing about larger heaps. Weaken <code>hlocal</code> to <code>HeapLocalWeak</code> and the fifth component has nothing to fill it, as above. And note that the proof never uses <code>hd</code> directly — it only passes it to <code>hlocal</code>. All of the initial-disjointness reasoning was pushed into the locality lemmas, which is precisely the modularity you were buying."
    },

    { "t": "note", "kind": "key", "title": "Locality is all the frame rule knows about c",
      "h": "That proof contains no induction on <code>c</code>, no case analysis on <code>Exec</code>, no lemma about <code>∗</code>, no determinism, no finiteness of heaps. <code>hoare_frame</code> is a fact about <i>any</i> relation satisfying <code>HeapLocal</code> and <code>Preserves</code>; all the command-specific work sits in the four exercises before it, sealed off. Add a command to the language tomorrow, prove <code>HeapLocal</code> for it, and the frame rule extends with no further thought." },

    {
      "t": "ex",
      "id": "m8-6",
      "name": "write_with_frame",
      "hard": false,

      "why": "The reason for all of the above. Do <b>not</b> prove it by unfolding two cells: the point is that the proof does not grow when the frame does. Replace <code>other ↦ w</code> by a ten-thousand-node linked list and not one character changes.",
      "setup": "In scope: <code>hoare_write l e old : Hoare (l ↦ old) (.write l e) (fun σ h => (l ↦ (e.eval σ)) σ h)</code> from M7, plus this chapter’s <code>hoare_frame</code>, <code>heapLocal_write</code>, <code>preserves_of_heapOnly</code> and <code>heapOnly_pointsTo</code>.",
      "goal": "theorem write_with_frame (l other : Loc) (old new w : Val) :\n    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new))\n      ((l ↦ new) ∗ (other ↦ w))",

      "hints": [
        "Do not <code>intro</code> anything. This is an application of <code>hoare_frame</code> and nothing else; if you are looking at a heap, you have taken a wrong turn.",
        "<code>hoare_frame</code> wants three arguments: the small triple, a locality proof, a <code>Preserves</code> proof. The small triple is <code>hoare_write l (.const new) old</code>; naming it with a <code>have</code> that ascribes the postcondition <code>l ↦ new</code> makes the application readable, though inlining also compiles.",
        "The <code>Preserves</code> argument is <code>preserves_of_heapOnly _ (heapOnly_pointsTo other w)</code>. The underscore is the command, which <code>preserves_of_heapOnly</code> takes explicitly and first — omit it and Lean complains that a <code>Prop</code> was supplied where a <code>Cmd</code> was expected."
      ],

      "sol": "theorem write_with_frame (l other : Loc) (old new w : Val) :\n    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new)) ((l ↦ new) ∗ (other ↦ w)) := by\n  have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=\n    hoare_write l (.const new) old\n  exact hoare_frame base (heapLocal_write l (.const new))\n    (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",

      "expl": "Four lines, and not one of them mentions a heap. Now imagine the frame is a linked list of ten thousand nodes: the proof is the same length. That invariance is the entire practical argument for separation logic.",

      "walk": [
        { "tac": "have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=",
          "h": "Names the small triple with its postcondition written the way you want to read it. <code>hoare_write</code>’s postcondition is the store-dependent <code>fun σ h => (l ↦ (e.eval σ)) σ h</code>; ascribing <code>l ↦ new</code> asks Lean to check that <code>(Atom.const new).eval σ</code> reduces to <code>new</code>, which it does definitionally." },
        { "tac": "hoare_write l (.const new) old",
          "h": "The M7 rule, instantiated. Nothing more is needed for the footprint: the write owns exactly one cell." },
        { "tac": "exact hoare_frame base (heapLocal_write l (.const new))",
          "h": "Applies the frame rule with <code>P := l ↦ old</code>, <code>Q := l ↦ new</code>, <code>R := other ↦ w</code>, all three read off the goal by unification." },
        { "tac": "(preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
          "h": "The store-stability obligation. <code>other ↦ w</code> ignores its store argument, so <code>heapOnly_pointsTo</code> applies and the bridge converts it. The <code>_</code> is the command." }
      ],

      "deep": [
        { "t": "trace", "title": "write_with_frame, tactic by tactic",
          "start": "l other : Loc\nold new w : Val\n⊢ Hoare (l ↦ old ∗ other ↦ w) (Cmd.write l (Atom.const new)) (l ↦ new ∗ other ↦ w)",
          "steps": [
            { "tac": "have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) := hoare_write l (.const new) old",
              "state": "l other : Loc\nold new w : Val\nbase : Hoare (l ↦ old) (Cmd.write l (Atom.const new)) (l ↦ new)\n⊢ Hoare (l ↦ old ∗ other ↦ w) (Cmd.write l (Atom.const new)) (l ↦ new ∗ other ↦ w)",
              "h": "One new hypothesis, and look at what is on the screen: no heaps, no unions, no disjointness anywhere." },
            { "tac": "exact hoare_frame base (heapLocal_write l (.const new)) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
              "state": "No goals.",
              "h": "Three arguments, three obligations, done." } ],
          "done": "No goals." },

        { "t": "cmp",
          "left": {
            "t": "Without the frame rule",
            "kind": "bad",
            "h": "<code>intro σ h hstar</code>, destructure the star into <code>Heap.singleton l old</code> and <code>Heap.singleton other w</code>, build the union, prove the cell exists in it with <code>union_of_some</code>, construct the <code>Exec.write</code> derivation, then prove <code>Heap.write (union …) l new = Heap.union (Heap.singleton l new) (Heap.singleton other w)</code> by <code>funext</code> and a three-way split. About twenty lines. Now do three cells."
          },
          "right": {
            "t": "With the frame rule",
            "kind": "good",
            "h": "Four lines, and the length does not depend on the frame. Everything earlier in this chapter was the price of admission for that one property."
          } },

        { "t": "detail", "title": "Where does <code>l ≠ other</code> come from?", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p", "h": "It is never stated and never needed as a hypothesis, because the precondition implies it. <code>(l ↦ old) ∗ (other ↦ w)</code> asserts a split of the heap into two disjoint singletons, and <code>two_cells_distinct</code> extracts <code>l ≠ other</code> from exactly that. If <code>l = other</code> the precondition is unsatisfiable and the triple holds vacuously." },
            { "t": "p", "h": "So the non-aliasing side conditions that clutter a classical development are absorbed into the connective, and the frame rule inherits them without ever mentioning them." } ] }
      ],

      "pitfall": "Writing <code>preserves_of_heapOnly (heapOnly_pointsTo other w)</code> without the leading <code>_</code>:<br><code>Application type mismatch: The argument heapOnly_pointsTo other w has type HeapOnly (other ↦ w) of sort `Prop` but is expected to have type Cmd of sort `Type` in the application preserves_of_heapOnly (heapOnly_pointsTo other w)</code>. Read quickly, that suggests something is wrong with <code>heapOnly_pointsTo</code>; nothing is, you are one underscore short. The other way to lose time is to open with <code>intro σ h hstar</code> out of habit — once <code>Hoare</code> is unfolded you cannot apply <code>hoare_frame</code> to the goal without folding it back up.",

      "variants": "Frame something store-dependent instead — say <code>pure (fun σ => σ x = 3)</code> — and <code>heapOnly_pointsTo</code> is no help, for the reason <code>not_heapOnly_pure</code> gives. For a <code>write</code> there is still a route, and the closing section says which. Frame the same assertion around <code>.assign x</code> and it genuinely fails; that is the counterexample from the top of the chapter. Take <code>other := l</code> and the theorem stays true but says nothing: <code>(l ↦ old) ∗ (l ↦ w)</code> is unsatisfiable."
    },

    { "t": "h3", "s": "The commands not in the exercises" },

    { "t": "p",
      "h": "Two constructors are left. The conditional is the same argument twice, so here it is as a free sample:" },

    { "t": "code", "tag": "illustration",
      "src": "theorem heapLocal_ite {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) : HeapLocal (.ite b c₁ c₂) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | iteTrue hb hex =>\n      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₁ σ h hFrame s' hd hex\n      exact ⟨hdEnd, r, Exec.iteTrue hb hr, hst, hhp⟩\n  | iteFalse hb hex =>\n      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₂ σ h hFrame s' hd hex\n      exact ⟨hdEnd, r, Exec.iteFalse hb hr, hst, hhp⟩",
      "cap": "not in the corpus — compiles against prelude/m8.lean" },

    { "t": "p",
      "h": "One <code>obtain</code> and one <code>exact</code> per branch, and the boolean side condition <code>hb</code> transfers unchanged because <code>b.eval</code> reads only the store. The frame is invisible to the guard, for the same reason it is invisible to a load." },

    { "t": "detail", "title": "The loop, and the induction it needs", "tag": "aside", "open": false,
      "blocks": [
        { "t": "p", "h": "Nothing in the workbook needs <code>HeapLocal (.loop b c)</code> — M13 verifies loops through an invariant and never frames one. But it is true, and the setup it forces is a manoeuvre you will meet again there." },
        { "t": "p", "h": "The obvious first move fails. <code>induction hex</code> on <code>hex : Exec (.loop b c) ⟨σ, h⟩ s'</code> gets:" },
        { "t": "state",
          "src": "error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)\n  Cmd.loop b c",
          "cap": "induction hex, straight off" },
        { "t": "p", "h": "To induct on a derivation, every index of the inductive family must be a <i>variable</i>, so that the motive can be abstracted over it. The command index here is the concrete term <code>Cmd.loop b c</code>. The standard repair is to prove a statement about an arbitrary <code>cmd</code> and carry the equation <code>cmd = .loop b₀ c₀</code> as a hypothesis; the eight branches that cannot be a loop then die to <code>cases</code> on that equation, which sees a constructor clash and closes the goal outright." },
        { "t": "p", "h": "Two more things have to be generalised, both because the induction hypothesis gets used at the <i>middle</i> state of one unrolling and must be available there: the start state becomes an arbitrary <code>s</code>, and <code>hFrame</code> goes <i>after</i> the equation, so the hypothesis is quantified over frames rather than fixed to one." },
        { "t": "code", "tag": "illustration",
          "src": "theorem heapLocal_loop_aux {b₀ : BExpr} {c₀ : Cmd} (hc : HeapLocal c₀) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      ∀ hFrame, Heap.disjoint s.heap hFrame →\n        Heap.disjoint s'.heap hFrame ∧\n        ∃ r : State,\n          Exec (.loop b₀ c₀) ⟨s.store, Heap.union s.heap hFrame⟩ r ∧\n          r.store = s'.store ∧\n          r.heap = Heap.union s'.heap hFrame := by\n  intro cmd s s' hex\n  induction hex with\n  | skip => intro heq; cases heq\n  | assign => intro heq; cases heq\n  | load _ => intro heq; cases heq\n  | write _ => intro heq; cases heq\n  | free _ => intro heq; cases heq\n  | seq _ _ _ _ => intro heq; cases heq\n  | iteTrue _ _ _ => intro heq; cases heq\n  | iteFalse _ _ _ => intro heq; cases heq\n  | loopFalse hb =>\n      intro heq hFrame hd\n      cases heq\n      exact ⟨hd, _, Exec.loopFalse hb, rfl, rfl⟩\n  | loopTrue hb hbdy hrst _ ihrst =>\n      intro heq hFrame hd\n      cases heq\n      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := hc _ _ hFrame _ hd hbdy\n      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := ihrst rfl hFrame hdMid\n      refine ⟨hdEnd, r₂, Exec.loopTrue hb hr₁ ?_, hst₂, hhp₂⟩\n      have heq : r₁ = ⟨r₁.store, r₁.heap⟩ := rfl\n      rw [hst₁, hhp₁] at heq\n      rw [heq]\n      exact hr₂\n\ntheorem heapLocal_loop {b : BExpr} {c : Cmd} (hc : HeapLocal c) :\n    HeapLocal (.loop b c) := by\n  intro σ h hFrame s' hd hex\n  exact heapLocal_loop_aux hc hex rfl hFrame hd",
          "cap": "not in the corpus — compiles against prelude/m8.lean" },
        { "t": "p", "h": "The <code>loopTrue</code> branch is <code>heapLocal_seq</code> with the tail supplied by the induction hypothesis instead of a second assumption: body through <code>hc</code>, tail through <code>ihrst</code>, glued with <code>Exec.loopTrue</code>. The underscores in <code>hc _ _ hFrame _ hd hbdy</code> are the store, the heap and the middle state, all read off <code>hbdy</code> — necessary because <code>induction</code> left those states inaccessible." },
        { "t": "p", "h": "The same inaccessibility forces a different spelling of the structure-eta step. In <code>heapLocal_seq</code> you could write <code>have heq : r₁ = ⟨sMid.store, …⟩</code> because <code>sMid</code> had a name. Here you start instead from the one equation always available — <code>r₁ = ⟨r₁.store, r₁.heap⟩</code>, true by <code>rfl</code> — and rewrite <i>forwards</i> with <code>hst₁</code> and <code>hhp₁</code> to push it into the shape the goal wants. Same fact, approached from the other end." } ] },

    { "t": "note", "kind": "warn", "title": "Allocation breaks locality if you are careless",
      "h": "Do <b>not</b> add a command “allocate exactly location <code>l</code>” and keep an unrestricted frame rule. If the frame already owns <code>l</code>, the allocation is not local and the rule becomes unsound — the same failure shape as <code>free</code> in exercise 3, at a different command. The three honest fixes: a side condition that the frame does not own <code>l</code>; nondeterministic fresh allocation with an existential in the postcondition; or finite heaps, so that a fresh location provably exists." },

    { "t": "h3", "s": "One obligation short" },

    { "t": "p",
      "h": "Go back to <code>readAndFree</code>, the two-command program that had to be rebuilt from <code>Exec</code> because the rules would not meet. The load leaves <code>pure (fun σ => σ x = v) ∗ (l ↦ v)</code>; <code>hoare_free</code> starts at <code>l ↦ v</code>. Frame the pure fact around the free, use <code>star_comm</code> to put the cell where the frame rule expects it and <code>star_emp_left</code> to clear up afterwards, and the composition goes through — four structural rules, no <code>Exec</code>:" },

    { "t": "code", "tag": "illustration",
      "src": "theorem readAndFree_framed (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=\n  hoare_seq\n    (hoare_consequence (entails_refl _) (hoare_load x l v) (star_comm _ _))\n    (hoare_consequence (entails_refl _)\n      (hoare_frame (hoare_free l v) (heapLocal_free l)\n        (sorry : Preserves (.free l) (pure (fun σ => σ x = v))))\n      (star_emp_left _))",
      "cap": "not in the corpus — compiles with one sorry against prelude/m8.lean" },

    { "t": "p",
      "h": "Everything except the <code>sorry</code>. The frame is <code>pure (fun σ => σ x = v)</code>, which reads the store, so <code>not_heapOnly_pure</code> applies and <code>preserves_of_heapOnly</code> is out. The obligation left standing is <code>Preserves (.free l) (pure (fun σ => σ x = v))</code>, and it is true for a reason that has nothing to do with the assertion: <code>.free l</code> does not touch the store at all, so it preserves <i>every</i> assertion. Nothing in scope says that." },

    { "t": "p",
      "h": "That missing lemma, and the habit of reading a program forwards — pick the footprint, frame the rest, reshape the assertion so the next rule fits — is M9. Once it is in place, <code>Exec</code> in one of your proofs means you are missing a lemma." },

    { "t": "dod",
      "h": "You have proved the frame rule from operational locality rather than accepting it as an axiom, and you know exactly which properties of the language it depends on — including which single command would break it." }

  ]
});
