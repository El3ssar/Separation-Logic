/* M9 — Symbolic execution — verifying real programs
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m9",
  "num": "M9",
  "phase": "Phase 2 · Program logic",
  "title": "Symbolic execution — verifying real programs",
  "blurb": "Using the logic compositionally: copy, move, and the handful of glue lemmas you need.",

  "orient": {
    "youWill": [
      "Verify a complete heap-manipulating program without ever writing the word <code>Heap</code>, <code>union</code>, or <code>disjoint</code> in the proof.",
      "Read the intermediate assertion for <code>hoare_seq</code> off the <i>next</i> command’s footprint instead of guessing it.",
      "Discharge the two <code>hoare_frame</code> side conditions mechanically: <code>heapLocal_*</code> for the heap, <code>preserves_of_heapOnly</code> or <code>preserves_of_storeStable</code> for the store.",
      "Reshape an assertion into the exact syntactic form a rule demands, using <code>star_assoc_left</code>, <code>star_comm</code>, <code>star_mono_right</code> and <code>pure_star_regroup</code>.",
      "Name the point where a program-variable side condition such as <code>tmp₁ ≠ tmp₂</code> is consumed, and say why it is the store-side twin of heap disjointness."
    ],
    "needs": [
      "M6: <code>hoare_seq</code> and <code>hoare_consequence</code>, including the habit of supplying the intermediate assertion explicitly as <code>hoare_seq (Q := …)</code>.",
      "M7: the three small-footprint rules <code>hoare_load</code>, <code>hoare_write</code>, <code>hoare_free</code>.",
      "M8: <code>hoare_frame</code> and its two hypotheses <code>HeapLocal c</code> and <code>Preserves c R</code>, plus <code>preserves_of_heapOnly</code>.",
      "M4: <code>star_comm</code>, <code>star_assoc_left</code>, <code>star_mono_right</code>, <code>star_emp_left</code>. All four appear in one proof below."
    ],
    "payoff": "This is where the machinery stops being machinery: a verification becomes a short readable term, and the very same term works whether the untouched part of the heap is one cell or ten thousand."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "From here on, verification should look like this and nothing else:"
    },
    {
      "t": "txt",
      "src": "  hoare_seq          split the program at a chosen intermediate assertion\n  hoare_frame        set aside the part of the heap this command does not touch\n  hoare_load/write/free/assign     apply the small rule to the footprint\n  hoare_consequence  reshape the assertion with the ∗-algebra from M4"
    },
    {
      "t": "p",
      "h": "<code>Exec</code> should not appear. If you find yourself unfolding the semantics, you are missing a lemma."
    },
    {
      "t": "p",
      "h": "“Symbolic execution” is the name for the discipline this imposes. You do not reason about a heap; you carry an <i>assertion</i> forward through the program, one command at a time, and each command transforms it in a way that is completely determined by the rule for that command. The only creative act left is choosing where to cut — and even that choice is forced, as you are about to see, by the shape the next rule demands."
    },
    {
      "t": "steps",
      "title": "One command, four moves",
      "items": [
        {
          "k": "Identify the footprint",
          "h": "Look at the command. <code>.load x l</code> touches exactly <code>l ↦ v</code>. <code>.write l e</code> touches exactly <code>l ↦ old</code>. <code>.free l</code> touches exactly <code>l ↦ v</code>. That single cell — and nothing else — is what the small rule from M7 talks about."
        },
        {
          "k": "Rotate the footprint into first position",
          "h": "<code>hoare_frame</code> has a fixed shape: it turns <code>Hoare P c Q</code> into <code>Hoare (P ∗ R) c (Q ∗ R)</code>. The framed part <code>R</code> is always on the <i>right</i>. So whatever you own has to be reassociated and commuted until the footprint is the leftmost factor. That is what <code>star_comm</code> and <code>star_assoc_left</code> are for."
        },
        {
          "k": "Apply the small rule under the frame",
          "h": "<code>hoare_frame (small rule) (heapLocal_… ) (preserves_… )</code>. Three arguments, and in this chapter the second and third are always taken from the short fixed list below — you never prove either from scratch."
        },
        {
          "k": "Renormalise for the next command",
          "h": "The postcondition you get is almost never the precondition the next rule wants. <code>hoare_consequence</code> plus a chain of <code>entails_trans</code> puts it right. Most of a real verification is this step, which is why M4 was worth the effort."
        }
      ]
    },
    {
      "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": "Every proof in this chapter is <b>frame, apply, reshape</b>, repeated. Nothing else happens. When a proof feels hard it is almost always because the assertion is in the wrong <i>syntactic</i> shape — not because anything is mathematically unclear. Separation logic buys you a semantics you never have to look at, in exchange for bookkeeping about where the parentheses go."
    },
    {
      "t": "cmp",
      "left": {
        "t": "What you would write on paper",
        "kind": "good",
        "h": "“Load <code>src</code> into <code>tmp</code>; the cell <code>dst</code> is untouched, so it is still <code>dst ↦ b</code>, and now we know <code>tmp = a</code>. Write <code>tmp</code> to <code>dst</code>; the cell <code>src</code> is untouched.” Two sentences, and the reassociations are invisible because on paper <code>∗</code> is silently associative and commutative."
      },
      "right": {
        "t": "What Lean makes you write",
        "h": "In Lean, <code>P ∗ (Q ∗ R)</code> and <code>(P ∗ Q) ∗ R</code> are <i>different terms</i>. They are provably equivalent — that is what <code>star_assoc_left</code> and <code>star_comm</code> say — but <code>hoare_frame</code> matches on syntax, so each reassociation must be applied explicitly as an entailment. Every line like this is a step your paper proof performed silently:",
        "tag": "sketch",
        "src": "refine entails_trans (star_assoc_left _ _ _) ?_\nrefine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_"
      }
    },
    {
      "t": "h4",
      "s": "Two glue lemmas you will need"
    },
    {
      "t": "p",
      "h": "First: <code>write</code> and <code>free</code> never change the store, so they preserve <i>every</i> assertion. This is much stronger than <code>heapOnly</code> and makes framing pure facts around them trivial."
    },
    {
      "t": "anat",
      "src": "def StoreStable (c : Cmd) : Prop := ∀ s s', Exec c s s' → s'.store = s.store\n\ntheorem storeStable_write (l : Loc) (e : Atom) : StoreStable (.write l e) := by\n  intro s s' hex; cases hex; rfl\n\ntheorem storeStable_free (l : Loc) : StoreStable (.free l) := by\n  intro s s' hex; cases hex; rfl\n\ntheorem preserves_of_storeStable {c : Cmd} (h : StoreStable c) (R : Assertion) :\n    Preserves c R := by\n  intro s s' hex hFrame hr\n  rw [h s s' hex]; exact hr",
      "parts": [
        {
          "m": "∀ s s', Exec c s s' → s'.store = s.store",
          "h": "A property of the <i>command alone</i>. It says nothing about the heap and nothing about any assertion — which is exactly why it can be proved once and reused for every frame you will ever want."
        },
        {
          "m": "cases hex; rfl",
          "h": "<code>cases hex</code> asks which constructor of <code>Exec</code> could have produced a run of <code>.write l e</code>. There is exactly one, <code>Exec.write</code>, and it fixes the final state, so the goal becomes <code>{ store := s.store, heap := s.heap.write l (Atom.eval s.store e) }.store = s.store</code>. Projecting a field out of a literal structure computes, so <code>rfl</code> finishes. (The trace below shows this goal as Lean prints it.)"
        },
        {
          "m": "(R : Assertion)",
          "h": "<code>R</code> is a parameter, not a hypothesis with conditions on it. That is the whole content of the lemma: store stability gives you <code>Preserves c R</code> for <b>every</b> <code>R</code> simultaneously, pure facts about program variables included."
        },
        {
          "m": "rw [h s s' hex]; exact hr",
          "h": "<code>h s s' hex</code> is the equation <code>s'.store = s.store</code>. The goal is <code>R s'.store hFrame</code>; rewriting with that equation turns it into <code>R s.store hFrame</code>, which is literally <code>hr</code>. No induction, no case analysis — the equation does everything."
        }
      ]
    },
    {
      "t": "trace",
      "title": "storeStable_write, tactic by tactic",
      "start": "l : Loc\ne : Atom\n⊢ StoreStable (Cmd.write l e)",
      "steps": [
        {
          "tac": "intro s s' hex",
          "state": "l : Loc\ne : Atom\ns s' : State\nhex : Exec (Cmd.write l e) s s'\n⊢ s'.store = s.store",
          "h": "<code>StoreStable</code> is a <code>∀</code> in disguise, so <code>intro</code> peels it. Nothing clever: the goal is now an equation between two stores."
        },
        {
          "tac": "cases hex",
          "state": "case write\nl : Loc\ne : Atom\ns : State\nold✝ : Val\nhl✝ : s.heap l = some old✝\n⊢ { store := s.store, heap := s.heap.write l (Atom.eval s.store e) }.store = s.store",
          "h": "Inversion. <code>s'</code> has vanished from the context — <code>cases</code> replaced it everywhere by the state that <code>Exec.write</code> produces. The daggered names <code>old✝</code> and <code>hl✝</code> are <i>inaccessible</i>: Lean invented them because the constructor’s arguments were not given names here, and you cannot refer to them. That is fine, because you do not need them."
        },
        {
          "tac": "rfl",
          "state": "No goals.",
          "h": "<code>{ store := s.store, heap := … }.store</code> reduces to <code>s.store</code> by projection, so both sides are the same term. This is one of the places where <code>rfl</code> is doing real work — it is not that the goal was already syntactically <code>a = a</code>, it is that it becomes so after computation."
        }
      ],
      "done": "No goals."
    },
    {
      "t": "detail",
      "title": "Why two different preservation helpers, and not one",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "M8 gave you <code>preserves_of_heapOnly</code>: if <code>R</code> does not look at the store at all, no command can disturb it. That covers frames like <code>dst ↦ b</code>. It does <i>not</i> cover frames like <code>pure (fun σ => σ tmp = a)</code>, which are entirely about the store."
        },
        {
          "t": "p",
          "h": "<code>preserves_of_storeStable</code> comes at the same obligation from the other end: if the <i>command</i> cannot change the store, then no assertion about the store can break. The two helpers quantify over opposite arguments — one fixes <code>R</code> and lets <code>c</code> vary, the other fixes <code>c</code> and lets <code>R</code> vary — and between them they cover every side condition in this chapter except one. The exception is a <code>load</code> (which does change the store) with a pure fact as its frame; that is <code>preserves_load_fact</code>, and it is the only place a hypothesis is needed."
        },
        {
          "t": "p",
          "h": "The rejected alternative is the classical one: a <i>syntactic</i> side condition, “<code>R</code> does not mention any variable modified by <code>c</code>”. It requires defining the set of modified variables, defining the free variables of an assertion (impossible here — assertions are functions <code>Store → Heap → Prop</code>, not syntax), and proving a substitution lemma. The semantic condition <code>Preserves</code> costs three helper lemmas and is strictly more permissive: an assertion may mention a modified variable and still be preserved, if the modification happens to keep it true."
        },
        {
          "t": "p",
          "h": "“Strictly more permissive” is a claim, so here is the witness. <code>x := x</code> modifies <code>x</code> — syntactically it is out of bounds for <i>every</i> frame mentioning <code>x</code> — and yet it preserves every assertion whatsoever:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "example (x : Var) (R : Assertion) : Preserves (.assign x (.var x)) R := by\n  intro s s' hex hFrame hr\n  cases hex with\n  | assign =>\n      have : Store.set s.store x (Atom.eval s.store (.var x)) = s.store := by\n        funext y; by_cases hy : y = x <;> simp [Store.set, Atom.eval, hy]\n      show R (Store.set s.store x (Atom.eval s.store (.var x))) hFrame\n      rw [this]; exact hr",
          "cap": "The funext is the point: Store.set σ x (σ x) and σ agree at every variable but are not the same term, so the equation has to be proved pointwise before rw can use it."
        }
      ]
    },
    {
      "t": "p",
      "h": "Second: the write rule as stated has a store-dependent postcondition, which is awkward to match. This variant takes the value as a parameter and demands a pure fact instead:"
    },
    {
      "t": "cmp",
      "left": {
        "t": "M7’s rule — hard to use here",
        "kind": "bad",
        "h": "The postcondition is a <i>lambda</i>: the value stored is whatever <code>e</code> evaluates to in the final store. To match this against a goal like <code>dst ↦ a</code> you would have to know that <code>Atom.eval σ (.var tmp) = a</code>, and there is nowhere in the statement to put that knowledge.",
        "tag": "sketch",
        "src": "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h)"
      },
      "right": {
        "t": "The variant — value up front",
        "kind": "good",
        "h": "The value <code>v</code> is now a parameter, the postcondition is the flat <code>l ↦ v</code>, and the obligation “<code>e</code> really does evaluate to <code>v</code>” has been moved into the precondition as a <code>fact</code>. That <code>fact</code> is precisely what the preceding <code>load</code> left lying around.",
        "tag": "sketch",
        "src": "theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :\n    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v)"
      }
    },
    {
      "t": "p",
      "h": "It is worth seeing what goes wrong concretely. Feed M7’s <code>hoare_write</code> to <code>hoare_frame</code> where the copy proof needs it and Lean says:"
    },
    {
      "t": "state",
      "src": "error: Application type mismatch: The argument\n  hoare_write dst (Atom.var tmp) b\nhas type\n  Hoare (dst ↦ b) (Cmd.write dst (Atom.var tmp)) fun σ h => (dst ↦ Atom.eval σ (Atom.var tmp)) σ h\nbut is expected to have type\n  Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b)) (Cmd.write dst (Atom.var tmp)) (dst ↦ a)\nin the application\n  hoare_frame (hoare_write dst (Atom.var tmp) b)",
      "cap": "The precondition is missing the fact, and the postcondition is a lambda where a points-to is wanted. Both halves are fixed by hoare_write_val."
    },
    {
      "t": "code",
      "src": "theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :\n    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v) := by\n  intro σ h hpre\n  obtain ⟨hv, hp⟩ := hpre\n  subst hp\n  refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,\n          Exec.write (singleton_same l old), ?_⟩\n  show Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l v\n  rw [write_singleton]\n  have : e.eval σ = v := hv\n  rw [this]"
    },
    {
      "t": "trace",
      "title": "hoare_write_val, tactic by tactic",
      "start": "l : Loc\ne : Atom\nold v : Val\n⊢ Hoare (aAnd (fact fun σ => Atom.eval σ e = v) (l ↦ old)) (Cmd.write l e) (l ↦ v)",
      "steps": [
        {
          "tac": "intro σ h hpre",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nh : Heap\nhpre : aAnd (fact fun σ => Atom.eval σ e = v) (l ↦ old) σ h\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (l ↦ v) s'.store s'.heap",
          "h": "<code>Hoare</code> unfolds to a <code>∀ σ h, P σ h → ∃ s', …</code>, so three <code>intro</code>s put you in front of the existential. This is the only place in the whole chapter where you see the definition of <code>Hoare</code> at all."
        },
        {
          "tac": "obtain ⟨hv, hp⟩ := hpre",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nh : Heap\nhv : fact (fun σ => Atom.eval σ e = v) σ h\nhp : (l ↦ old) σ h\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (l ↦ v) s'.store s'.heap",
          "h": "<code>aAnd P Q σ h</code> <i>is</i> <code>P σ h ∧ Q σ h</code> by definition, so the anonymous-constructor pattern <code>⟨hv, hp⟩</code> splits it. Lean does not need you to <code>unfold aAnd</code> first: <code>obtain</code> looks through definitional unfolding."
        },
        {
          "tac": "subst hp",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old } s' ∧ (l ↦ v) s'.store s'.heap",
          "h": "<code>hp : (l ↦ old) σ h</code> looks like a predicate application, but <code>pointsTo</code> is defined as <code>fun _ h => h = Heap.singleton l v</code>, so <code>hp</code> <i>is</i> the equation <code>h = Heap.singleton l old</code>. <code>subst</code> sees through the definition and eliminates <code>h</code> everywhere. This is the single most useful move in the whole workbook: exact ownership means the precondition <i>determines</i> the heap."
        },
        {
          "tac": "refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩, Exec.write (singleton_same l old), ?_⟩",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ (l ↦ v) { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.store\n    { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.heap",
          "h": "Supply the witness state and the execution derivation, and leave the postcondition as a hole. <code>singleton_same l old : Heap.singleton l old l = some old</code> is the side condition <code>Exec.write</code> demands — the cell must already exist. Note that the goal is now stated in terms of projections out of the literal state."
        },
        {
          "tac": "show Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l v",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ (Heap.singleton l old).write l (Atom.eval σ e) = Heap.singleton l v",
          "h": "<code>show</code> changes the goal to a definitionally equal one you can actually read. Two things happened at once: the projections computed away, and <code>(l ↦ v) σ' h'</code> unfolded to the equation <code>h' = Heap.singleton l v</code>. Neither is a proof step — <code>show</code> only ever renames the goal — but the goal is now a heap equation, which you have lemmas about."
        },
        {
          "tac": "rw [write_singleton]",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ Heap.singleton l (Atom.eval σ e) = Heap.singleton l v",
          "h": "<code>write_singleton</code> from M1: overwriting the one cell of a singleton gives a singleton. All that is left is that the two stored values agree."
        },
        {
          "tac": "have : e.eval σ = v := hv",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\nthis : Atom.eval σ e = v\n⊢ Heap.singleton l (Atom.eval σ e) = Heap.singleton l v",
          "h": "<code>hv</code> has type <code>fact (fun σ => e.eval σ = v) σ (Heap.singleton l old)</code>. Since <code>fact φ</code> is <code>fun σ _ => φ σ</code>, that type <i>is</i> the equation <code>Atom.eval σ e = v</code>, definitionally. <code>have : T := hv</code> with an explicit <code>T</code> is a type ascription: the same proof term, re-announced at the unfolded type. Nothing is proved on this line. It is worth being clear about what it is <i>not</i>: it is not needed to make <code>rw</code> work — <code>rw [hv]</code> unfolds the hypothesis's type looking for an equation and closes this goal on its own. The ascription is for the reader, putting the fact you are about to rewrite with on the page instead of leaving it buried inside a <code>fact</code>."
        },
        {
          "tac": "rw [this]",
          "state": "No goals.",
          "h": "Both sides become <code>Heap.singleton l v</code> and <code>rw</code> closes the goal with <code>rfl</code> automatically."
        }
      ],
      "done": "No goals."
    },
    {
      "t": "p",
      "h": "And one bookkeeping entailment, moving a pure fact from “left of a <code>∗</code>” to “conjoined with the first factor”:"
    },
    {
      "t": "code",
      "src": "theorem pure_star_regroup (φ : Store → Prop) (P R : Assertion) :\n    pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by\n  intro σ h hstar\n  obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar\n  subst he\n  refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩\n  rw [hu, union_empty_left, huPR]"
    },
    {
      "t": "p",
      "h": "Why not just <code>star_pure_left</code> from M4, which already says <code>pure φ ∗ P ⊢ aAnd (fact φ) P</code>? Instantiate it at <code>P := (dst ↦ b) ∗ (src ↦ a)</code> and you land on <code>aAnd (fact φ) ((dst ↦ b) ∗ (src ↦ a))</code>. That assertion is <i>not a <code>∗</code> at the top level</i>, so <code>hoare_frame</code> — which matches the syntactic pattern <code>?P ∗ ?R</code> — cannot fire. You would then have to prove <code>aAnd (fact φ) (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R</code> to get unstuck, and at that point you have re-derived <code>pure_star_regroup</code> the long way round. The lemma exists so that the pure fact lands <i>inside</i> the left factor in one step, leaving a top-level <code>∗</code> for the frame rule to bite on."
    },
    {
      "t": "detail",
      "title": "pure_star_regroup, tactic by tactic",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "This is the only proof in the chapter that touches heaps, and it is worth reading once so you can then forget it. The content is: the <code>pure</code> factor owns the empty heap, so the three-way split <code>h = h₀ ∪ (hP ∪ hR)</code> collapses to the two-way split <code>h = hP ∪ hR</code>."
        },
        {
          "t": "trace",
          "title": "pure_star_regroup",
          "start": "φ : Store → Prop\nP R : Assertion\n⊢ _root_.pure φ ∗ P ∗ R ⊢ aAnd (fact φ) P ∗ R",
          "steps": [
            {
              "tac": "intro σ h hstar",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh : Heap\nhstar : (_root_.pure φ ∗ P ∗ R) σ h\n⊢ (aAnd (fact φ) P ∗ R) σ h",
              "h": "<code>⊢</code> between assertions is <code>Entails</code>, i.e. <code>∀ σ h, P σ h → Q σ h</code>, so three <code>intro</code>s. Note that Lean prints our <code>pure</code> as <code>_root_.pure</code>: there is another <code>pure</code> in scope (the monadic one), so the pretty-printer disambiguates. It is the same function you defined in M3."
            },
            {
              "tac": "obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh h₀ hPR : Heap\nhd : h₀.disjoint hPR\nhu : h = h₀.union hPR\nhφ : fact φ σ h₀\nhe : emp σ h₀\nhP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\n⊢ (aAnd (fact φ) P ∗ R) σ h",
              "h": "One nested pattern destroys both stars at once. <code>star</code> is a five-field existential (<code>∃ h₁ h₂, disjoint ∧ eq ∧ P ∧ Q</code>), which is why each level costs six names, and <code>pure φ</code> is an <code>aAnd</code>, which is why <code>⟨hφ, he⟩</code> splits it further."
            },
            {
              "tac": "subst he",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh hPR hP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\nhd : Heap.empty.disjoint hPR\nhu : h = Heap.empty.union hPR\nhφ : fact φ σ Heap.empty\n⊢ (aAnd (fact φ) P ∗ R) σ h",
              "h": "<code>he : emp σ h₀</code> unfolds to <code>h₀ = Heap.empty</code>, so <code>subst</code> eliminates <code>h₀</code>. Watch what it did to the context: <code>hd</code>, <code>hu</code> and <code>hφ</code> were all rewritten and re-ordered to the bottom. That reordering is normal and harmless, but it is why hypothesis order in a printed goal is not something to rely on."
            },
            {
              "tac": "refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh hPR hP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\nhd : Heap.empty.disjoint hPR\nhu : h = Heap.empty.union hPR\nhφ : fact φ σ Heap.empty\n⊢ h = hP.union hR",
              "h": "Choose the new cut: <code>hP</code> and <code>hR</code>, exactly the inner one. Five of the six components are already in the context; only the heap equation is left as <code>?_</code>."
            },
            {
              "tac": "rw [hu, union_empty_left, huPR]",
              "state": "No goals.",
              "h": "Three rewrites, left to right: <code>h</code> becomes <code>Heap.empty ∪ hPR</code>, that becomes <code>hPR</code>, that becomes <code>hP ∪ hR</code>. The goal is now <code>hP ∪ hR = hP ∪ hR</code> and <code>rw</code> closes it by <code>rfl</code>."
            }
          ],
          "done": "No goals."
        }
      ]
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "hoare_seq (Q := …) h₁ h₂",
          "h": "Split the program at <code>Q</code>. <code>Q</code> is the one thing you genuinely have to invent, and Lean cannot guess it, so it is always supplied by name."
        },
        {
          "k": "hoare_frame hc hlocal hpres",
          "h": "Three arguments: the small triple, heap locality, store preservation. The last two are the bureaucracy; the list below is the complete set of terms you will ever pass for them in this chapter."
        },
        {
          "k": "heapLocal_load / heapLocal_write / heapLocal_free",
          "h": "The heap-side obligation. Proved once per primitive in M8; you only ever cite them."
        },
        {
          "k": "preserves_of_heapOnly _ (heapOnly_pointsTo l v)",
          "h": "The store-side obligation when the framed assertion is a points-to. <code>heapOnly_star</code> combines them if the frame is a <code>∗</code> of several cells."
        },
        {
          "k": "preserves_of_storeStable (storeStable_write l e) _",
          "h": "The store-side obligation when the command is a <code>write</code> (or <code>free</code>). Works for <i>any</i> frame, including pure facts — that is the point of the lemma."
        },
        {
          "k": "preserves_load_fact l hne",
          "h": "The store-side obligation for the one remaining case: framing a pure fact about a variable around a <code>load</code>. The only one of the five that needs a hypothesis, namely that the two variables differ."
        },
        {
          "k": "hoare_consequence hpre hc hpost",
          "h": "Reshape. Pass <code>entails_refl _</code> on whichever side you do not want to change — you will write that a lot."
        },
        {
          "k": "star_comm · star_assoc_left · star_mono_left · star_mono_right · star_emp_left · pure_star_regroup",
          "h": "The reshaping vocabulary, chained with <code>entails_trans</code>. Six lemmas cover every rearrangement in this chapter. The two worked programs need only four of them; <code>star_mono_left</code> — the mirror of <code>star_mono_right</code>, rewriting under the <i>left</i> factor — first earns its place in the swap proof."
        }
      ]
    },
    {
      "t": "sec",
      "s": "Program 1 · copy one cell into another"
    },
    {
      "t": "code",
      "src": "def copyCell (tmp : Var) (src dst : Loc) : Cmd :=\n  .load tmp src ;; .write dst (.var tmp)"
    },
    {
      "t": "txt",
      "src": "  { src ↦ a ∗ dst ↦ b }\n      copyCell tmp src dst\n  { src ↦ a ∗ dst ↦ a }"
    },
    {
      "t": "p",
      "h": "The proof plan, in words:"
    },
    {
      "t": "ol",
      "items": [
        "Frame <code>dst ↦ b</code> around the load. The load’s footprint is only <code>src ↦ a</code>.",
        "The load leaves the pure fact <code>σ tmp = a</code>. Renormalise: pull the pure fact out front, and swap <code>src ↦ a</code> and <code>dst ↦ b</code> so that the cell the write needs is on the outside.",
        "Frame <code>src ↦ a</code> around the write, using <code>hoare_write_val</code> with the value <code>a</code> supplied by the pure fact.",
        "Commute the final star."
      ]
    },
    {
      "t": "p",
      "h": "The same plan, as the assertion Lean is actually carrying at each point. Read the right-hand column downwards and you have the proof:"
    },
    {
      "t": "tbl",
      "head": [
        "where you are",
        "the assertion in hand"
      ],
      "rows": [
        [
          "start",
          "<code>(src ↦ a) ∗ (dst ↦ b)</code>"
        ],
        [
          "after <code>hoare_load</code> on the footprint alone",
          "<code>pure (σ tmp = a) ∗ (src ↦ a)</code>"
        ],
        [
          "…re-attaching the frame <code>dst ↦ b</code>",
          "<code>(pure (σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)</code>"
        ],
        [
          "…<code>star_assoc_left</code>",
          "<code>pure (σ tmp = a) ∗ ((src ↦ a) ∗ (dst ↦ b))</code>"
        ],
        [
          "…<code>star_mono_right _ (star_comm …)</code>",
          "<code>pure (σ tmp = a) ∗ ((dst ↦ b) ∗ (src ↦ a))</code>"
        ],
        [
          "…<code>pure_star_regroup</code>",
          "<code>(aAnd (fact (σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code>"
        ],
        [
          "after <code>hoare_write_val</code>, frame <code>src ↦ a</code>",
          "<code>(dst ↦ a) ∗ (src ↦ a)</code>"
        ],
        [
          "…<code>star_comm</code>",
          "<code>(src ↦ a) ∗ (dst ↦ a)</code>"
        ]
      ],
      "cap": "Eight lines, of which two are rule applications and five are reshaping. That ratio is typical."
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "How the intermediate assertion was found",
      "h": "Do not try to guess <code>Q</code> by pushing forward from the precondition. Work <i>backwards</i> from the second command. The write needs <code>aAnd (fact (…= a)) (dst ↦ b)</code> as its footprint — that is <code>hoare_write_val</code>’s precondition, verbatim — and it needs everything else to sit to the right of a top-level <code>∗</code> so the frame rule can take it. That forces <code>Q = (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code> and there is no freedom left. Once you have <code>Q</code>, the first half of the proof is just “get from the load’s output to <code>Q</code>”."
    },
    {
      "t": "ex",
      "id": "m9-1",
      "name": "copyCell_spec",
      "hard": true,
      "why": "The first genuinely compositional verification. Note that at no point does the proof mention a heap, a union, or a disjointness. It is also the template for every remaining proof in the chapter: pick the cut, frame, apply, reshape.",
      "setup": "Everything you need exists: <code>hoare_seq</code>, <code>hoare_consequence</code>, <code>hoare_frame</code>, <code>hoare_load</code>, <code>hoare_write_val</code>, <code>heapLocal_load</code>, <code>heapLocal_write</code>, <code>preserves_of_heapOnly</code>, <code>heapOnly_pointsTo</code>, <code>preserves_of_storeStable</code>, <code>storeStable_write</code>, and from M4 <code>entails_refl</code>, <code>entails_trans</code>, <code>star_assoc_left</code>, <code>star_comm</code>, <code>star_mono_right</code>, <code>pure_star_regroup</code>.",
      "goal": "theorem copyCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst)\n      ((src ↦ a) ∗ (dst ↦ a))",
      "hints": [
        "Start from the <i>second</i> command, not the first. Write down the exact precondition <code>hoare_write_val dst (.var tmp) b a</code> demands, then put everything the write does not touch to the right of a top-level <code>∗</code>. That assertion is your <code>Q</code>.",
        "Both halves have the same shape: build the framed triple as a <code>have step : … := hoare_frame …</code>, then fix up the ends with <code>hoare_consequence</code>. For the load, the frame is <code>dst ↦ b</code> and the preservation obligation is <code>preserves_of_heapOnly _ (heapOnly_pointsTo dst b)</code>. For the write, the frame is <code>src ↦ a</code> and the obligation is <code>preserves_of_storeStable (storeStable_write dst (.var tmp)) _</code>.",
        "In the first half, the postcondition you are handed is <code>(pure (σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)</code> and the one you want is <code>(aAnd (fact (σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code>. Three moves: reassociate, commute the inner pair, regroup the pure fact.",
        "Use <code>hoare_seq</code> with intermediate assertion <code>(aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code>. Getting to that shape is three <code>entails_trans</code> steps: <code>star_assoc_left</code>, then <code>star_mono_right … (star_comm …)</code>, then <code>pure_star_regroup</code>."
      ],
      "sol": "theorem copyCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst) ((src ↦ a) ∗ (dst ↦ a)) := by\n  refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_\n  · -- the load, framed by `dst ↦ b`, then renormalised\n    have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src)\n        ((pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)) :=\n      hoare_frame (hoare_load tmp src a) (heapLocal_load tmp src)\n        (preserves_of_heapOnly _ (heapOnly_pointsTo dst b))\n    refine hoare_consequence (entails_refl _) step ?_\n    refine entails_trans (star_assoc_left _ _ _) ?_\n    refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_\n    exact pure_star_regroup _ _ _\n  · -- the write, with the value known from the pure fact, framed by `src ↦ a`\n    have step : Hoare ((aAnd (fact (fun σ => (Atom.var tmp).eval σ = a)) (dst ↦ b)) ∗ (src ↦ a))\n        (.write dst (.var tmp)) ((dst ↦ a) ∗ (src ↦ a)) :=\n      hoare_frame (hoare_write_val dst (.var tmp) b a) (heapLocal_write dst (.var tmp))\n        (preserves_of_storeStable (storeStable_write dst (.var tmp)) _)\n    exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))",
      "expl": "The intermediate assertion is the only creative choice, and it is dictated by what the write needs: the write’s footprint is <code>dst ↦ b</code>, and it needs to know the value it is about to store, so <code>dst ↦ b</code> must be conjoined with the fact <code>σ tmp = a</code> and everything else must be to the right of a <code>∗</code>. Once you see that, the renormalisation chain writes itself. Also note the two <code>Preserves</code> obligations, each discharged by a different helper: <code>heapOnly</code> for the load (it changes the store, but <code>dst ↦ b</code> does not care), <code>storeStable</code> for the write (it does not change the store at all).",
      "walk": [
        {
          "tac": "refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_",
          "h": "Cuts the program in two and leaves two goals, <code>refine_1</code> (the load) and <code>refine_2</code> (the write). <code>Q</code> is passed by name because it appears in neither the conclusion nor the other arguments, so Lean has no way to infer it. Notice in the trace that Lean has already replaced <code>copyCell tmp src dst</code> by <code>Cmd.load tmp src</code> in the first goal: matching <code>?c₁ ;; ?c₂</code> against the goal unfolded the definition for free, so no <code>unfold copyCell</code> is needed."
        },
        {
          "tac": "· -- the load, framed by `dst ↦ b`, then renormalised",
          "h": "The <code>·</code> focuses the first goal. Everything indented under it must close that goal before the second bullet starts. This is cosmetic, but without it a stray tactic can silently apply to the wrong goal."
        },
        {
          "tac": "have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src)",
          "h": "Forward reasoning: build the triple you want, state its type in full, and only then match it against the goal. Stating the type is not optional decoration — it is what pins down the implicit <code>R</code> in <code>hoare_frame</code>, which nothing else determines."
        },
        {
          "tac": "((pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)) :=",
          "h": "The postcondition, written exactly as the frame rule produces it: <code>hoare_load</code>’s output <code>pure (σ tmp = a) ∗ (src ↦ a)</code>, with the frame <code>dst ↦ b</code> stuck on the right. The outer brackets are not decoration — <code>∗</code> is right-associative, so without them the same characters would parse as <code>pure … ∗ ((src ↦ a) ∗ (dst ↦ b))</code>, a different assertion that the frame rule would not accept."
        },
        {
          "tac": "hoare_frame (hoare_load tmp src a) (heapLocal_load tmp src)",
          "h": "The first two of the frame rule’s three arguments: the small triple for the load, and the proof that <code>load</code> is heap-local. Both are quoted straight from M7 and M8."
        },
        {
          "tac": "(preserves_of_heapOnly _ (heapOnly_pointsTo dst b))",
          "h": "The third argument. A <code>load</code> <i>does</i> change the store, so <code>storeStable</code> is unavailable here; instead you argue from the frame: <code>dst ↦ b</code> never looks at the store, so nothing a command does to the store can disturb it. The <code>_</code> is the command, which Lean infers."
        },
        {
          "tac": "refine hoare_consequence (entails_refl _) step ?_",
          "h": "Keep the precondition (<code>entails_refl</code>: it already matches), use <code>step</code> for the middle, and leave the postcondition entailment as a hole. The goal changes type here — from a <code>Hoare</code> to an <code>Entails</code> — which is the moment the proof leaves program logic and becomes pure ∗-algebra."
        },
        {
          "tac": "refine entails_trans (star_assoc_left _ _ _) ?_",
          "h": "<code>entails_trans</code> is composition of entailments: give it the first leg, keep the rest as a hole. <code>star_assoc_left : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)</code> reassociates so the pure fact is alone on the left."
        },
        {
          "tac": "refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_",
          "h": "<code>star_mono_right P h</code> applies an entailment <i>under</i> a star, to the right factor only. Here it swaps <code>(src ↦ a) ∗ (dst ↦ b)</code> into <code>(dst ↦ b) ∗ (src ↦ a)</code> while leaving the pure fact where it is. This is the step that brings the cell the write needs to the front."
        },
        {
          "tac": "exact pure_star_regroup _ _ _",
          "h": "The glue lemma, in exactly the position it was designed for: <code>pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R</code> with <code>φ := (σ tmp = a)</code>, <code>P := dst ↦ b</code>, <code>R := src ↦ a</code>. First goal closed."
        },
        {
          "tac": "· -- the write, with the value known from the pure fact, framed by `src ↦ a`",
          "h": "Second bullet: <code>Hoare Q (.write dst (.var tmp)) ((src ↦ a) ∗ (dst ↦ a))</code>."
        },
        {
          "tac": "have step : Hoare ((aAnd (fact (fun σ => (Atom.var tmp).eval σ = a)) (dst ↦ b)) ∗ (src ↦ a))",
          "h": "The fact is written as <code>(Atom.var tmp).eval σ = a</code>, not <code>σ tmp = a</code>, because that is the literal form <code>hoare_write_val</code> produces from its <code>e</code> parameter. The two are definitionally equal — <code>Atom.eval σ (.var tmp)</code> reduces to <code>σ tmp</code> — and the final <code>exact</code> is what quietly reconciles them."
        },
        {
          "tac": "(.write dst (.var tmp)) ((dst ↦ a) ∗ (src ↦ a)) :=",
          "h": "Postcondition with the frame on the right, again: <code>hoare_write_val</code> gives <code>dst ↦ a</code>, and the untouched <code>src ↦ a</code> comes back attached to it."
        },
        {
          "tac": "hoare_frame (hoare_write_val dst (.var tmp) b a) (heapLocal_write dst (.var tmp))",
          "h": "<code>hoare_write_val dst (.var tmp) b a</code>: location <code>dst</code>, expression <code>.var tmp</code>, old value <code>b</code>, new value <code>a</code>. The last argument is the one that makes the postcondition come out as <code>dst ↦ a</code> rather than as a lambda."
        },
        {
          "tac": "(preserves_of_storeStable (storeStable_write dst (.var tmp)) _)",
          "h": "The frame here is <code>src ↦ a</code>, so <code>heapOnly</code> would have worked too. But <code>storeStable</code> is the better habit: it discharges the obligation for <i>any</i> frame, which matters as soon as a pure fact is in the frame — as it is in the swap exercise."
        },
        {
          "tac": "exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))",
          "h": "One commutation and the postcondition matches. And this is where the <code>(Atom.var tmp).eval σ</code> versus <code>σ tmp</code> mismatch is absorbed: <code>exact</code> checks up to definitional unfolding, so nothing has to be said about it."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "copyCell_spec, goal by goal",
          "start": "tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (copyCell tmp src dst) (src ↦ a ∗ dst ↦ a)",
          "steps": [
            {
              "tac": "refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a)",
              "h": "Two goals; this is the first. <code>copyCell tmp src dst</code> has become <code>Cmd.load tmp src</code> — unification unfolded the definition to match <code>c₁ ;; c₂</code>. Lean also drops the parentheses you wrote: <code>aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a</code> is <code>(aAnd …) ∗ (src ↦ a)</code>, because <code>∗</code> binds looser than application."
            },
            {
              "tac": "have step : … := hoare_frame (hoare_load tmp src a) …",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a)",
              "h": "The goal is untouched; <code>step</code> is now in context. Compare the two postconditions carefully — same precondition, same command, and the whole remaining problem is the distance between those two assertions. Note <code>_root_.pure</code>: the pretty-printer is disambiguating our <code>pure</code> from the monadic one."
            },
            {
              "tac": "refine hoare_consequence (entails_refl _) step ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ ((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
              "h": "The goal is now an entailment. Two <code>⊢</code> symbols appear on that line: the outer one is Lean’s “the goal is”, the inner one is our <code>Entails</code> notation. Getting used to reading that double turnstile is half of reading this chapter’s goals."
            },
            {
              "tac": "refine entails_trans (star_assoc_left _ _ _) ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ (_root_.pure fun σ => σ tmp = a) ∗ src ↦ a ∗ dst ↦ b ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
              "h": "The left-hand side lost a pair of brackets: it was <code>(pure ∗ src ↦ a) ∗ dst ↦ b</code> and is now <code>pure ∗ (src ↦ a ∗ dst ↦ b)</code>, which Lean prints without parentheses because <code>∗</code> is right-associative. That invisible change of association is the entire step."
            },
            {
              "tac": "refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ (_root_.pure fun σ => σ tmp = a) ∗ dst ↦ b ∗ src ↦ a ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
              "h": "The two cells have swapped under the star. The remaining gap is exactly <code>pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R</code> — one application of <code>pure_star_regroup</code>."
            },
            {
              "tac": "exact pure_star_regroup _ _ _",
              "state": "case refine_2\ntmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp)) (src ↦ a ∗ dst ↦ a)",
              "h": "First goal closed; what you see now is the second. Its precondition is the <code>Q</code> you chose, and its postcondition is the chapter’s goal."
            },
            {
              "tac": "have step : … := hoare_frame (hoare_write_val dst (.var tmp) b a) …",
              "state": "case refine_2\ntmp : Var\nsrc dst : Loc\na b : Val\nstep :\n  Hoare (aAnd (fact fun σ => Atom.eval σ (Atom.var tmp) = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp))\n    (dst ↦ a ∗ src ↦ a)\n⊢ Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp)) (src ↦ a ∗ dst ↦ a)",
              "h": "Look at the difference between <code>step</code> and the goal: <code>Atom.eval σ (Atom.var tmp) = a</code> against <code>σ tmp = a</code>. Those are <i>not</i> the same term, but <code>Atom.eval</code> is defined by pattern matching and reduces on the constructor <code>Atom.var</code>, so they are definitionally equal and <code>exact</code> will accept one for the other. Only the postconditions still differ, by a commutation."
            },
            {
              "tac": "exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))",
              "state": "No goals.",
              "h": "Both goals closed."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "One thing the proof never mentions, and which is worth making explicit: <b>nothing anywhere assumes <code>src ≠ dst</code></b>. It does not have to. The precondition already implies it:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "example (src dst : Loc) (a b : Val) :\n    (src ↦ a) ∗ (dst ↦ b) ⊢ fact (fun _ => src ≠ dst) :=\n  two_cells_distinct src dst a b",
          "cap": "M4’s two_cells_distinct. Owning two cells separately is owning two different cells."
        },
        {
          "t": "p",
          "h": "If a caller does have <code>src = dst</code>, they simply cannot supply the precondition, and the specification says nothing about that case — correctly, because <code>copyCell tmp l l</code> does something perfectly well defined that this triple was never about. Non-aliasing is not a hypothesis you add; it is a consequence of what you own."
        },
        {
          "t": "detail",
          "title": "What the same theorem costs without the frame rule",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Try it: <code>intro σ h hstar</code>, destructure the star into <code>h₁</code>, <code>h₂</code> with a disjointness proof and a union equation, <code>subst</code> both singleton equations, then build an <code>Exec.seq</code> whose two side conditions require <code>union_of_some</code>, then prove that <code>Heap.write (Heap.union (Heap.singleton src a) (Heap.singleton dst b)) dst a</code> splits as <code>Heap.singleton src a ∪ Heap.singleton dst b</code> with the second component rewritten — a <code>funext</code> and a case split on the location. The exact line count depends on how you route it; what does not depend on that is that every line is about heaps, and none is about the program."
            },
            {
              "t": "p",
              "h": "Now add a third cell to the precondition. The frame-rule proof does not change at all; the direct proof changes everywhere. That is the practical content of M8, and it is why the discipline in this chapter is worth enforcing even when a direct proof looks shorter."
            }
          ]
        }
      ],
      "pitfall": "The mistake almost everyone makes is putting the pure fact in the wrong place: choosing <code>Q = pure (fun σ => σ tmp = a) ∗ ((dst ↦ b) ∗ (src ↦ a))</code>, which looks tidier. It is unusable. <code>hoare_frame</code> would then have to match <code>pure … ∗ X</code> against <code>?P ∗ ?R</code>, giving <code>P = pure …</code> — a triple about the write whose footprint is empty. No such triple exists, and the reason is worth stating: <code>pure φ</code> forces the heap to be <code>Heap.empty</code>, <code>Exec.write</code> demands <code>s.heap dst = some old</code>, and <code>Heap.empty dst</code> is <code>none</code>, so there is no execution at all to be the witness the triple asks for. The fact has to be <i>conjoined</i> with <code>dst ↦ b</code> (an <code>aAnd</code>, not a <code>∗</code>) so that the left factor is exactly what <code>hoare_write_val</code> wants. The second mistake is the mirror image: writing <code>fact</code> where <code>pure</code> belongs, or the reverse. <code>fact φ</code> holds of <i>any</i> heap; <code>pure φ</code> additionally demands the heap is empty. On the left of a <code>∗</code> you need <code>pure</code> (otherwise the fact would be silently claiming ownership of a cut of the heap); inside an <code>aAnd</code> you need <code>fact</code> (otherwise you would be demanding that <code>dst ↦ b</code> hold of an empty heap, which is false).",
      "variants": "<b>Drop the frame rule</b> and the proof becomes forty lines of heap algebra (see the aside above). <b>Reverse the order of the two commands</b> — write first, then load — and the specification becomes false: <code>dst</code> would be overwritten with the old, unknown contents of <code>tmp</code>. Nothing in the proof would break at a specific line; you simply could not choose a <code>Q</code>, because after the write you know nothing about <code>dst</code>. <b>Replace <code>hoare_write_val</code> by <code>hoare_write</code></b> and the second half dies at once with the application type mismatch shown above: the postcondition is a lambda in <code>σ</code>, and there is no way to specialise it to <code>dst ↦ a</code> without the fact that <code>tmp</code> holds <code>a</code>. <b>Drop the <code>dst ↦ b</code> conjunct from the precondition</b> and the write has no cell to write to: <code>Exec.write</code> requires <code>s.heap dst = some old</code>, and the triple is total-correctness, so it would be unprovable — not merely unproved."
    },
    {
      "t": "sec",
      "s": "Program 2 · move a cell and deallocate the source"
    },
    {
      "t": "code",
      "src": "def moveCell (tmp : Var) (src dst : Loc) : Cmd :=\n  copyCell tmp src dst ;; .free src"
    },
    {
      "t": "txt",
      "src": "  { src ↦ a ∗ dst ↦ b }\n      moveCell tmp src dst\n  { dst ↦ a }"
    },
    {
      "t": "p",
      "h": "Read the two assertions again. The precondition owns two cells; the postcondition owns one. In an ordinary Hoare logic that is not even expressible — assertions there describe a state, and “I no longer own <code>src</code>” is not a statement about the state. Here it is the difference between two <code>∗</code>-expressions, and the logic is doing the accounting for you."
    },
    {
      "t": "note",
      "kind": "info",
      "title": "An associativity trap that will cost you ten minutes",
      "h": "<code>;;</code> is right-associative, so <code>a ;; b ;; c</code> parses as <code>a ;; (b ;; c)</code>. To reuse <code>copyCell_spec</code> you need the left-nested grouping, so define <code>moveCell</code> as <code>copyCell tmp src dst ;; .free src</code>. The two groupings do denote the same relation — prove it as <code>exec_seq_assoc</code> — but they are different <code>Cmd</code> terms, and Lean cares."
    },
    {
      "t": "code",
      "tag": "illustration",
      "src": "example (tmp : Var) (src dst : Loc) :\n    moveCell tmp src dst = ((.load tmp src ;; .write dst (.var tmp)) ;; .free src) := rfl\n\nexample (tmp : Var) (src dst : Loc) :\n    (Cmd.load tmp src ;; Cmd.write dst (.var tmp) ;; Cmd.free src)\n      = (Cmd.load tmp src ;; (Cmd.write dst (.var tmp) ;; Cmd.free src)) := rfl",
      "cap": "Both close by rfl — and they are the two different terms. The first is what moveCell means; the second is what you get if you write the three commands in a row."
    },
    {
      "t": "p",
      "h": "Here is the trap actually springing. Define the program with the flat, right-nested grouping and open the proof with the natural first line:"
    },
    {
      "t": "state",
      "src": "error: Application type mismatch: The argument\n  copyCell_spec tmp src dst a b\nhas type\n  Hoare (src ↦ a ∗ dst ↦ b) (copyCell tmp src dst) (src ↦ a ∗ dst ↦ a)\nbut is expected to have type\n  Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (src ↦ a ∗ dst ↦ a)\nin the application\n  hoare_seq (copyCell_spec tmp src dst a b)",
      "cap": "hoare_seq split off only the load, because the program is `load ;; (write ;; free)`. Your two-command spec has nothing to attach to."
    },
    {
      "t": "ex",
      "id": "m9-2",
      "name": "exec_seq_assoc",
      "hard": false,
      "why": "The escape hatch for exactly the failure above. Once you have it you can move a specification between the two bracketings instead of restructuring the program or re-proving the spec — and it is also your first look at how <code>cases</code> behaves on a hypothesis whose intermediate state you never named.",
      "goal": "theorem exec_seq_assoc {c₁ c₂ c₃ : Cmd} {s s' : State} :\n    Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; (c₂ ;; c₃)) s s'",
      "hints": [
        "An <code>↔</code> is a structure with two fields. <code>constructor</code> splits it into <code>case mp</code> and <code>case mpr</code>; do the two directions independently, they are mirror images.",
        "In each direction you have a hypothesis <code>Exec (something ;; something) s s'</code>. Only one constructor of <code>Exec</code> can produce that, so <code>cases h with | seq h₁ h₂ => …</code> gives you the two halves and, silently, an intermediate state.",
        "One <code>cases</code> is not enough: after the first, one of <code>h₁</code>, <code>h₂</code> is itself a <code>seq</code>, so case on it too. Then rebuild with <code>Exec.seq</code> — you can write it as <code>.seq</code>, since the expected type tells Lean which namespace to look in."
      ],
      "sol": "theorem exec_seq_assoc {c₁ c₂ c₃ : Cmd} {s s' : State} :\n    Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; (c₂ ;; c₃)) s s' := by\n  constructor\n  · intro h\n    cases h with | seq h₁ h₂ => cases h₁ with | seq ha hb => exact .seq ha (.seq hb h₂)\n  · intro h\n    cases h with | seq h₁ h₂ => cases h₂ with | seq ha hb => exact .seq (.seq h₁ ha) hb",
      "expl": "Sequencing is associative <i>semantically</i> but not syntactically. This lemma is what lets you regroup when a specification you want to reuse has the other bracketing.",
      "walk": [
        {
          "tac": "constructor",
          "h": "<code>Iff</code> is a structure with fields <code>mp</code> and <code>mpr</code>, so <code>constructor</code> applies <code>Iff.intro</code> and leaves one goal per field, labelled <code>case mp</code> and <code>case mpr</code>. Nothing about <code>↔</code> is primitive here."
        },
        {
          "tac": "· intro h",
          "h": "Focus the forward direction and name the hypothesis. The goal is now <code>Exec (c₁ ;; c₂ ;; c₃) s s'</code> — printed without brackets, because <code>;;</code> is right-associative and that is the right-nested form."
        },
        {
          "tac": "cases h with | seq h₁ h₂ => cases h₁ with | seq ha hb => exact .seq ha (.seq hb h₂)",
          "h": "Two inversions and a rebuild, on one line. The first <code>cases</code> splits the run of <code>(c₁ ;; c₂) ;; c₃</code> into a run of <code>c₁ ;; c₂</code> and a run of <code>c₃</code>; the second splits the former again. The three pieces <code>ha : Exec c₁ s s'✝</code>, <code>hb : Exec c₂ s'✝ s'✝¹</code>, <code>h₂ : Exec c₃ s'✝¹ s'</code> are then reassembled with the other bracketing. <code>.seq</code> is <code>Exec.seq</code>: when the expected type is known to be <code>Exec …</code>, a leading dot means “look this name up in that type’s namespace”."
        },
        {
          "tac": "· intro h",
          "h": "The reverse direction, opened the same way."
        },
        {
          "tac": "cases h with | seq h₁ h₂ => cases h₂ with | seq ha hb => exact .seq (.seq h₁ ha) hb",
          "h": "Mirror image: this time it is the <i>second</i> component that is a <code>seq</code>, so you case on <code>h₂</code>, and the rebuild nests to the left. The symmetry is exact, which is a good sign that no hidden condition is lurking in either direction."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "The forward direction, one inversion at a time",
          "start": "c₁ c₂ c₃ : Cmd\ns s' : State\n⊢ Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; c₂ ;; c₃) s s'",
          "steps": [
            {
              "tac": "constructor",
              "state": "case mp\nc₁ c₂ c₃ : Cmd\ns s' : State\n⊢ Exec ((c₁ ;; c₂) ;; c₃) s s' → Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "Two goals, <code>mp</code> and <code>mpr</code>. Note how the two sides print: <code>((c₁ ;; c₂) ;; c₃)</code> keeps its brackets because they are not the default association, while <code>c₁ ;; c₂ ;; c₃</code> has lost them. Same statement, and the asymmetry in the printing <i>is</i> the content of the lemma."
            },
            {
              "tac": "intro h",
              "state": "case mp\nc₁ c₂ c₃ : Cmd\ns s' : State\nh : Exec ((c₁ ;; c₂) ;; c₃) s s'\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "Nothing surprising. The whole proof is a change of shape of <code>h</code>."
            },
            {
              "tac": "cases h with | seq h₁ h₂ => …",
              "state": "case mp.seq\nc₁ c₂ c₃ : Cmd\ns s' s'✝ : State\nh₁ : Exec (c₁ ;; c₂) s s'✝\nh₂ : Exec c₃ s'✝ s'\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "There is exactly one constructor of <code>Exec</code> that can produce a run of a <code>;;</code>, so there is exactly one case, <code>mp.seq</code>. Notice <code>s'✝</code>: the intermediate state appeared out of nowhere and is <i>inaccessible</i> — the <code>with | seq h₁ h₂</code> pattern named the two proofs but not the state. You cannot mention it, and you do not need to."
            },
            {
              "tac": "cases h₁ with | seq ha hb => …",
              "state": "case mp.seq.seq\nc₁ c₂ c₃ : Cmd\ns s' s'✝¹ : State\nh₂ : Exec c₃ s'✝¹ s'\ns'✝ : State\nha : Exec c₁ s s'✝\nhb : Exec c₂ s'✝ s'✝¹\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "A second inaccessible state, distinguished by a superscript. Read the three hypotheses as a chain: <code>s → s'✝ → s'✝¹ → s'</code>. The goal wants that same chain grouped as <code>c₁</code> then <code>(c₂ ;; c₃)</code>, so the rebuild is <code>.seq ha (.seq hb h₂)</code> — Lean infers both intermediate states from the types of the pieces."
            },
            {
              "tac": "exact .seq ha (.seq hb h₂)",
              "state": "No goals.",
              "h": "Forward direction done. The backward direction is the same four moves with <code>h₂</code> in place of <code>h₁</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "The lemma is about <code>Exec</code>, but what you usually want is to move a <i>triple</i> across the regrouping. That is three lines, and it is the only place in the chapter where unfolding <code>Hoare</code> is the right thing to do:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "example {P Q : Assertion} {c₁ c₂ c₃ : Cmd}\n    (h : Hoare P ((c₁ ;; c₂) ;; c₃) Q) : Hoare P (c₁ ;; (c₂ ;; c₃)) Q := by\n  intro σ hh hp\n  obtain ⟨s', hex, hq⟩ := h σ hh hp\n  exact ⟨s', exec_seq_assoc.mp hex, hq⟩",
          "cap": "The witness state and the postcondition are reused unchanged; only the execution derivation is re-bracketed."
        },
        {
          "t": "p",
          "h": "And here is the negative half of the same coin, so that “the two bracketings are different <code>Cmd</code> terms” is a theorem rather than a remark. The equation fails for <i>every</i> triple of commands, because it forces <code>c₁ ;; c₂ = c₁</code>:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem seq_ne_left (a : Cmd) : ∀ b, (a ;; b) ≠ a := by\n  induction a with\n  | seq x y ihx ihy => intro b h; injection h with p q; exact ihx y p\n  | _ => intro b h; exact Cmd.noConfusion h\n\nexample (c₁ c₂ c₃ : Cmd) : ((c₁ ;; c₂) ;; c₃) ≠ (c₁ ;; (c₂ ;; c₃)) := by\n  intro h\n  injection h with p q\n  exact seq_ne_left c₁ c₂ p",
          "cap": "injection is the tactic form of constructor injectivity: from Cmd.seq A c₃ = Cmd.seq c₁ B it produces p : A = c₁ and q : c₃ = B."
        },
        {
          "t": "p",
          "h": "Two pieces of syntax in that snippet are new. <code>| _ =></code> is a catch-all branch in an <code>induction</code>: <code>Cmd</code> has eight constructors and seven of them need the same one-line argument, so rather than write seven identical branches you write one wildcard. And <code>Cmd.noConfusion</code> is the eliminator Lean generates for every inductive type, saying that distinct constructors build distinct terms: applied to a proof of <code>Cmd.seq … = Cmd.skip</code> it yields anything at all, which is why it closes those seven goals. It is the same principle <code>cases</code> uses silently when it discards impossible branches — here you have to name it, because the impossible equation is a hypothesis rather than the thing being cased on."
        }
      ],
      "pitfall": "Writing <code>cases h</code> without the <code>with | seq …</code> clause. It works, but the two components come back inaccessible — Lean names them <code>h₁✝</code> and <code>h₂✝</code>, reusing the constructor’s own argument names and daggering them — and a daggered name cannot be written in your source, so the <code>exact</code> has nothing to refer to. (Expect <code>a✝</code>-style names only when the constructor’s arguments were anonymous in its declaration; <code>Exec.seq</code> declares <code>h₁</code> and <code>h₂</code>, so those are what you see.) The other common slip is expecting <code>rfl</code> or <code>simp</code> to do this: the two commands are genuinely different terms of type <code>Cmd</code>, distinct constructors applied to distinct arguments, so no amount of computation identifies them. Only the semantics does.",
      "variants": "The corresponding statement for <code>Cmd</code> itself — <code>(c₁ ;; c₂) ;; c₃ = c₁ ;; (c₂ ;; c₃)</code> — is <b>false</b>, and that is the whole reason this lemma exists. It is worth being precise about <i>how</i> false: not “false for generic <code>c₁</code>”, but false for <b>every</b> <code>c₁</code>, <code>c₂</code>, <code>c₃</code> without exception. Injectivity of <code>Cmd.seq</code> turns the equation into <code>c₁ ;; c₂ = c₁</code>, and no term of an inductive type is a proper subterm of itself; the compiled proof is in the panel above. Associativity holds only after you pass to the relation the two trees denote. <b>Drop either <code>cases</code></b> and you are stuck for a concrete reason rather than a vague one: after the first, <code>h₁ : Exec (c₁ ;; c₂) s s'✝</code> is still a compound run, and <code>.seq ha (.seq hb h₂)</code> needs its two halves as separate terms — there is nothing else in context they could come from."
    },
    {
      "t": "ex",
      "id": "m9-3",
      "name": "moveCell_spec",
      "hard": false,
      "why": "Copy, then give back the source. The postcondition owns strictly less memory than the precondition — the logic is tracking the deallocation for you. It is also the first proof that reuses a previous specification wholesale rather than a primitive rule, which is what compositionality was supposed to buy.",
      "goal": "theorem moveCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCell tmp src dst) (dst ↦ a)",
      "hints": [
        "<code>moveCell</code> is <code>copyCell … ;; .free src</code>, so the cut is already chosen for you: it has to be <code>copyCell_spec</code>’s postcondition.",
        "For the second half: the free’s footprint is <code>src ↦ a</code>, which is already the left factor, so no reshaping is needed <i>before</i> the frame rule — only after. <code>hoare_free</code>’s postcondition is <code>emp</code>, so what comes out of the frame rule is <code>emp ∗ (dst ↦ a)</code>.",
        "<code>hoare_seq</code> with <code>copyCell_spec</code>, then frame <code>dst ↦ a</code> around <code>hoare_free</code>, then <code>star_emp_left</code> to clean up."
      ],
      "sol": "theorem moveCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCell tmp src dst) (dst ↦ a) := by\n  refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_\n  have step : Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a)) :=\n    hoare_frame (hoare_free src a) (heapLocal_free src)\n      (preserves_of_storeStable (storeStable_free src) _)\n  exact hoare_consequence (entails_refl _) step (star_emp_left _)",
      "expl": "Four lines, entirely by composition. The <code>emp ∗ (dst ↦ a) ⊢ dst ↦ a</code> at the end is exactly why you proved the unit laws in M4 — this kind of tidying-up is most of what <code>hoare_consequence</code> does in practice.",
      "walk": [
        {
          "tac": "refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_",
          "h": "The cut is <code>copyCell_spec</code>’s postcondition, so the first argument can be given directly rather than as a hole. Only one <code>?_</code> is left, for the <code>free</code>. This is the moment the previous exercise pays: a whole two-command program has become a single citation."
        },
        {
          "tac": "have step : Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a)) :=",
          "h": "The framed triple, stated first. The postcondition is <code>emp ∗ (dst ↦ a)</code> and not <code>dst ↦ a</code>, because that is literally what <code>hoare_frame</code> produces: <code>hoare_free</code>’s <code>emp</code>, with the frame stuck on the right. Writing the true type here rather than the type you wish it had is what makes the last line trivial."
        },
        {
          "tac": "hoare_frame (hoare_free src a) (heapLocal_free src)",
          "h": "Small rule plus heap locality, both from earlier chapters. Note that <code>src ↦ a</code> is already the left factor of the precondition, so no reshaping is needed on the way <i>in</i>; the only entailment in this half of the proof is the one on the way out."
        },
        {
          "tac": "(preserves_of_storeStable (storeStable_free src) _)",
          "h": "<code>free</code> does not touch the store, so the frame <code>dst ↦ a</code> survives for free. <code>preserves_of_heapOnly _ (heapOnly_pointsTo dst a)</code> would have worked equally well here; the store-stable route is the one that keeps working when the frame is a pure fact."
        },
        {
          "tac": "exact hoare_consequence (entails_refl _) step (star_emp_left _)",
          "h": "Precondition already matches, so <code>entails_refl</code>. The postcondition needs <code>emp ∗ (dst ↦ a) ⊢ dst ↦ a</code>, which is the left unit law from M4. The proof ends on a bookkeeping lemma, as most of them do."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "moveCell_spec, three states",
          "start": "tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (moveCell tmp src dst) (dst ↦ a)",
          "steps": [
            {
              "tac": "refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_",
              "state": "tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
              "h": "One goal, not two: the first component was supplied as a term, so only the hole remains. <code>moveCell</code> unfolded and split at exactly the point where <code>copyCell_spec</code> applies — which is why the definition had to be written with that bracketing."
            },
            {
              "tac": "have step : … := hoare_frame (hoare_free src a) …",
              "state": "tmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (emp ∗ dst ↦ a)\n⊢ Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
              "h": "The precondition of <code>step</code> already matches the goal on the nose. The only difference is the leftover <code>emp ∗</code> in the postcondition — one unit law away."
            },
            {
              "tac": "exact hoare_consequence (entails_refl _) step (star_emp_left _)",
              "state": "No goals.",
              "h": "Done. Four lines, and not one of them mentions <code>Heap</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "M7 closed with a promise: <code>readAndFree_spec</code>, which you proved there by building an <code>Exec.seq</code> derivation by hand, would come back as a pure composition once you had the frame rule. Here it is, with the same statement — one <code>hoare_seq</code>, one framed triple, one <code>hoare_consequence</code>:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "example (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) := by\n  refine hoare_seq (Q := pure (fun σ => σ x = v) ∗ (l ↦ v)) (hoare_load x l v) ?_\n  have step : Hoare ((l ↦ v) ∗ pure (fun σ => σ x = v)) (.free l)\n      (emp ∗ pure (fun σ => σ x = v)) :=\n    hoare_frame (hoare_free l v) (heapLocal_free l)\n      (preserves_of_storeStable (storeStable_free l) _)\n  exact hoare_consequence (star_comm _ _) step (star_emp_left _)",
          "cap": "The frame here is a pure fact, not a cell — which is exactly the case preserves_of_heapOnly cannot handle and preserves_of_storeStable can."
        },
        {
          "t": "p",
          "h": "Compare it with the M7 proof. There, the precondition’s heap had to be <code>subst</code>ed, the two <code>Exec</code> side conditions discharged by hand with <code>singleton_same</code>, and the final heap shown to be empty with <code>erase_singleton</code>. Here none of that appears; instead there is one <code>star_comm</code> to put the footprint on the left and one <code>star_emp_left</code> to clean up. The work did not vanish — it was done once, in M8, for all commands at once."
        },
        {
          "t": "p",
          "h": "One error message is worth reading in advance, because you will produce it. Write the <code>have</code> with the postcondition you <i>want</i> — <code>dst ↦ a</code> — rather than the one <code>hoare_frame</code> produces:"
        },
        {
          "t": "state",
          "src": "error: Type mismatch\n  hoare_frame (hoare_free src a) (heapLocal_free src) (preserves_of_storeStable (storeStable_free src) ?m.12)\nhas type\n  Hoare (src ↦ a ∗ ?m.12) (Cmd.free src) (emp ∗ ?m.12)\nbut is expected to have type\n  Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
          "cap": "?m.12 is the frame R, still an unsolved metavariable: hoare_frame never determines R by itself, the ascribed type of the `have` does. When the ascribed type cannot be matched, R has nothing to be solved from and Lean prints it raw."
        }
      ],
      "pitfall": "Stating <code>step</code> with the postcondition you want (<code>dst ↦ a</code>) instead of the one <code>hoare_frame</code> actually produces (<code>emp ∗ (dst ↦ a)</code>). Lean rejects the <code>have</code> itself, and the message — reproduced in the panel above — takes a moment to parse, because the frame appears in it as a bare metavariable <code>?m.12</code> rather than as an assertion. Read the <i>has type</i> line and ignore the metavariable: it says <code>emp ∗ ?m.12</code>, and that <code>emp</code> is <code>hoare_free</code>’s postcondition, which is not going away. Rule of thumb: write the type of a <code>have</code> as the rule produces it, and do all the wishful thinking afterwards in <code>hoare_consequence</code>.",
      "variants": "<b>Ask for <code>(src ↦ ?) ∗ (dst ↦ a)</code> as the postcondition</b> and it becomes unprovable: after <code>free src</code> you own nothing at <code>src</code>, and there is no value <code>?</code> making <code>src ↦ ?</code> true of the empty heap — that is precisely what <code>pointsTo_not_emp</code> from M3 says. <b>Free <code>dst</code> instead of <code>src</code></b> and the proof still goes through with the mirror-image reshaping, giving postcondition <code>src ↦ a</code>: nothing about the argument is specific to which cell you keep. <b>Free <code>src</code> twice</b> and the second free is unprovable, because after the first you no longer own the cell and <code>Exec.free</code> demands <code>s.heap src = some v</code>. Double-free is not an axiom we ruled out; it is a triple we cannot prove."
    },
    {
      "t": "sec",
      "s": "Exercise · swap (open)"
    },
    {
      "t": "p",
      "h": "Swap is the first program where two pure facts have to be alive at the same time, and where one of them has to survive a command that writes to the store. That is the whole difficulty, and it is a real one: it is where the store-side analogue of disjointness finally has to be stated."
    },
    {
      "t": "p",
      "h": "The extra ingredient is <code>preserves_load_fact</code>: a load into <code>x</code> preserves a pure fact about <code>y</code>, provided <code>y ≠ x</code>. Compare it with heap disjointness — <code>l₁ ↦ a ∗ l₂ ↦ b</code> guarantees the cells are distinct, so a write to one cannot disturb the other. On the store there is no <code>∗</code>, no ownership, and therefore no automatic distinctness: variables are shared, and the only way to know that a load does not clobber a fact is to be told that the names differ. That asymmetry is not an accident of our encoding — it is why separation logic separates the heap and not the store."
    },
    {
      "t": "steps",
      "title": "The shape of the swap proof",
      "items": [
        {
          "k": "Four commands, three cuts",
          "h": "<code>swap</code> is right-nested, so the proof is <code>hoare_seq</code> applied three times, each time peeling one command off the front. Four assertions are listed in the solution panel, but only the first three are cuts you have to invent — the fourth is the postcondition you were given. Write all four out before you write any tactic."
        },
        {
          "k": "Each step is frame · apply · reshape",
          "h": "Exactly as in <code>copyCell_spec</code>. The only new wrinkle is that from the second command onwards the frame contains a <code>pure</code> factor as well as cells, so you frame twice: once for the untouched cell, once for the carried fact."
        },
        {
          "k": "The two loads differ",
          "h": "The first load has nothing to carry, so <code>preserves_of_heapOnly</code> suffices. The second load must carry <code>pure (σ tmp₁ = a)</code> past a write to <code>tmp₂</code>, and that is the one place <code>preserves_load_fact</code> — and the hypothesis <code>tmp₁ ≠ tmp₂</code> — is used."
        },
        {
          "k": "The two writes are easy",
          "h": "<code>preserves_of_storeStable (storeStable_write …) _</code> discharges the obligation for any frame at all, cells and facts alike. Both writes use <code>hoare_write_val</code>, and both need <code>pure_star_regroup</code> to put the fact next to the cell being written."
        }
      ]
    },
    {
      "t": "ex",
      "id": "m9-4",
      "name": "swap_spec",
      "hard": false,
      "why": "Deliberately left for you. Everything you need is proved; the work is choosing four intermediate assertions and carrying two pure facts past two loads. It is also the exercise that shows you what a verification of a non-trivial program actually costs in this style — roughly ten lines per command, all of it mechanical.",
      "setup": "You will need to state the specification yourself. It takes an extra hypothesis <code>hne : tmp₁ ≠ tmp₂</code> (see the hint), and the conclusion is <code>Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap tmp₁ tmp₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a))</code>. Everything else — <code>hoare_frame</code>, the small rules, <code>hoare_write_val</code>, <code>pure_star_regroup</code>, the M4 algebra — you already have.",
      "goal": "def swap (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) : Cmd :=\n  .load tmp₁ l₁ ;;\n  (.load tmp₂ l₂ ;;\n   (.write l₁ (.var tmp₂) ;; .write l₂ (.var tmp₁)))\n\n-- { l₁ ↦ a ∗ l₂ ↦ b }  swap tmp₁ tmp₂ l₁ l₂  { l₁ ↦ b ∗ l₂ ↦ a }",
      "hints": [
        "Do <code>preserves_load_fact</code> first, on its own — it is five tactics and it is the only genuinely new content. Start with <code>intro s s' hex hFrame hr</code>, then <code>cases hex with | load hl =></code>, and remember that <code>pure φ</code> is an <code>aAnd</code>, so both the hypothesis and the goal split in two.",
        "For the program: the whole proof is three nested <code>hoare_seq</code>s, because <code>swap</code> is right-nested. Peel one command at a time and never look at more than one command’s worth of assertion.",
        "From the second command onwards you frame twice. Build the inner triple (command plus untouched cell) as one <code>have</code>, then frame the carried <code>pure</code> fact around <i>that</i> as a second <code>have</code>. Since <code>hoare_frame</code> always puts the frame on the right and the plan keeps the fact on the left, each of those two steps is bracketed by a <code>star_comm</code>.",
        "You will need one extra lemma: that a load into <code>tmp₂</code> preserves a pure fact about <code>tmp₁</code>, which requires <code>tmp₁ ≠ tmp₂</code>. That lemma is <code>preserves_load_fact</code> below. Note also that no hypothesis <code>l₁ ≠ l₂</code> is needed — the precondition <code>l₁ ↦ a ∗ l₂ ↦ b</code> already implies it, by <code>two_cells_distinct</code>."
      ],
      "sol": "theorem preserves_load_fact {x y : Var} {v : Val} (l : Loc) (hne : y ≠ x) :\n    Preserves (.load x l) (pure (fun σ => σ y = v)) := by\n  intro s s' hex hFrame hr\n  cases hex with\n  | load hl =>\n      obtain ⟨hy, he⟩ := hr\n      refine ⟨?_, he⟩\n      show Store.set s.store x _ y = v\n      simp [Store.set, hne]\n      exact hy\n\n-- The remaining work: four applications of hoare_seq, each of the form\n--   frame the untouched cell  →  apply the small rule  →  renormalise.\n-- The intermediate assertions, in order:\n--   pure (tmp₁ = a) ∗ (l₁ ↦ a ∗ l₂ ↦ b)\n--   pure (tmp₁ = a) ∗ (pure (tmp₂ = b) ∗ (l₁ ↦ a ∗ l₂ ↦ b))\n--   pure (tmp₁ = a) ∗ (l₁ ↦ b ∗ l₂ ↦ b)\n--   l₁ ↦ b ∗ l₂ ↦ a",
      "expl": "<code>preserves_load_fact</code> is the one genuinely new ingredient, and it is where the hypothesis <code>tmp₁ ≠ tmp₂</code> is consumed: the load overwrites <code>tmp₂</code>, and the framed fact talks about <code>tmp₁</code>, so they must be different variables. This is the store-side analogue of heap disjointness, and it is a good illustration of why <code>Preserves</code> is a <i>semantic</i> condition rather than a syntactic “<code>R</code> does not mention modified variables”: the semantic version is easier to prove and strictly more permissive.",
      "walk": [
        {
          "tac": "intro s s' hex hFrame hr",
          "h": "<code>Preserves c R</code> is <code>∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame</code>, so five <code>intro</code>s put you in front of the conclusion. Note the order: the frame heap comes <i>after</i> the execution."
        },
        {
          "tac": "cases hex with",
          "h": "Invert the execution. Only <code>Exec.load</code> can produce a run of <code>.load x l</code>, so there is one case — but the inversion is what replaces <code>s'</code> by the concrete state <code>⟨Store.set s.store x v✝, s.heap⟩</code> in the goal, which is the only reason to do it."
        },
        {
          "tac": "| load hl =>",
          "h": "Name the side condition <code>hl : s.heap l = some v✝</code>. You will not use it: whether the load succeeded is irrelevant to whether a fact about a <i>different</i> variable survives. Naming it anyway is required by the <code>with</code> syntax."
        },
        {
          "tac": "obtain ⟨hy, he⟩ := hr",
          "h": "<code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so the hypothesis splits into the fact <code>hy</code> and the emptiness <code>he</code>. <code>he</code> is about <code>hFrame</code>, which the command cannot touch, so it can be handed straight back."
        },
        {
          "tac": "refine ⟨?_, he⟩",
          "h": "The goal is also a <code>pure</code>, so it is also a conjunction. Supply the second component immediately — the heap is unchanged — and leave the interesting half as a hole."
        },
        {
          "tac": "show Store.set s.store x _ y = v",
          "h": "The goal at this point is <code>fact (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame</code>, which is unreadable and, worse, not in a form <code>simp</code> will attack. <code>show</code> restates it as the equation it definitionally is. The <code>_</code> is the loaded value, which is inaccessible — you cannot name it, so you let Lean fill it in."
        },
        {
          "tac": "simp [Store.set, hne]",
          "h": "Unfold <code>Store.set</code> to <code>if y = x then v✝ else s.store y</code> and use <code>hne : y ≠ x</code> to take the else branch. <b>This is the only line where the hypothesis is used</b>, and if you delete <code>hne</code> from the <code>simp</code> set the goal simply does not close. The result is <code>s.store y = v</code>."
        },
        {
          "tac": "exact hy",
          "h": "<code>hy : fact (fun σ => σ y = v) s.store hFrame</code> unfolds definitionally to <code>s.store y = v</code>, so it closes the goal directly. (<code>simp</code> left the goal in exactly that form — see the trace.)"
        },
        {
          "tac": "-- The remaining work: four applications of hoare_seq …",
          "h": "The rest of the exercise. Each of the four steps has the shape you already used twice in <code>copyCell_spec</code>; nothing new appears."
        },
        {
          "tac": "--   pure (tmp₁ = a) ∗ (l₁ ↦ a ∗ l₂ ↦ b)",
          "h": "After the first load. Obtained from <code>hoare_load tmp₁ l₁ a</code> framed by <code>l₂ ↦ b</code>, then a single <code>star_assoc_left</code>. The pure fact is kept on the far left throughout — that is the invariant of the whole layout."
        },
        {
          "tac": "--   pure (tmp₁ = a) ∗ (pure (tmp₂ = b) ∗ (l₁ ↦ a ∗ l₂ ↦ b))",
          "h": "After the second load. Two facts alive at once. Getting here needs the inner load framed by <code>l₁ ↦ a</code>, and then <i>that</i> whole triple framed by <code>pure (tmp₁ = a)</code> — which is where <code>preserves_load_fact l₂ hne</code> is passed."
        },
        {
          "tac": "--   pure (tmp₁ = a) ∗ (l₁ ↦ b ∗ l₂ ↦ b)",
          "h": "After the first write. <code>pure (tmp₂ = b)</code> has been consumed: <code>pure_star_regroup</code> turned it into the <code>aAnd</code> that <code>hoare_write_val l₁ (.var tmp₂) a b</code> demands, and the rule ate it. Facts are used up exactly when the value they describe is stored."
        },
        {
          "tac": "--   l₁ ↦ b ∗ l₂ ↦ a",
          "h": "After the second write, <code>pure (tmp₁ = a)</code> is consumed the same way and nothing is left over. A verification that ends with a leftover <code>pure</code> is usually a sign you framed something you should have used."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "preserves_load_fact, tactic by tactic",
          "start": "x y : Var\nv : Val\nl : Loc\nhne : y ≠ x\n⊢ Preserves (Cmd.load x l) (_root_.pure fun σ => σ y = v)",
          "steps": [
            {
              "tac": "intro s s' hex hFrame hr",
              "state": "x y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns s' : State\nhex : Exec (Cmd.load x l) s s'\nhFrame : Heap\nhr : _root_.pure (fun σ => σ y = v) s.store hFrame\n⊢ _root_.pure (fun σ => σ y = v) s'.store hFrame",
              "h": "Hypothesis and goal are the same assertion at two different stores. Everything that follows is about the relationship between <code>s.store</code> and <code>s'.store</code>."
            },
            {
              "tac": "cases hex with | load hl =>",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nhr : _root_.pure (fun σ => σ y = v) s.store hFrame\nv✝ : Val\nhl : s.heap l = some v✝\n⊢ _root_.pure (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame",
              "h": "<code>s'</code> is gone, replaced everywhere by the state <code>Exec.load</code> produces. The loaded value <code>v✝</code> is inaccessible — the pattern <code>| load hl</code> named the side condition but not the value. That is exactly why the <code>show</code> two steps later has to write <code>_</code> in its place."
            },
            {
              "tac": "obtain ⟨hy, he⟩ := hr",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ _root_.pure (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame",
              "h": "The two halves of <code>pure</code>. <code>he : emp s.store hFrame</code> says <code>hFrame = Heap.empty</code>; it survives untouched because the command changes the store, not the frame heap."
            },
            {
              "tac": "refine ⟨?_, he⟩",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ fact (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame",
              "h": "<code>he</code> is reused verbatim — note that <code>emp</code> ignores its store argument, so the same proof serves at the old store and the new one. Only the <code>fact</code> half is left."
            },
            {
              "tac": "show Store.set s.store x _ y = v",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ s.store.set x v✝ y = v",
              "h": "Three definitions unfolded at once — <code>fact</code>, the structure projection, and the application — and the goal is now a plain equation about stores. <code>show</code> proved nothing; it made the goal legible and, crucially, made it match the shape <code>simp [Store.set]</code> knows how to attack."
            },
            {
              "tac": "simp [Store.set, hne]",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ s.store y = v",
              "h": "<b>The whole content of the lemma is this line.</b> <code>Store.set s.store x v✝ y</code> is <code>if y = x then v✝ else s.store y</code>; <code>hne</code> discharges the condition, the <code>if</code> collapses to the else branch, and the new store’s value at <code>y</code> is the old store’s value at <code>y</code>. Drop <code>hne</code> from the bracket and <code>simp [Store.set]</code> unfolds the definition but can go no further: it leaves you looking at <code>⊢ (if y = x then v✝ else s.store y) = v</code>, which is unprovable, since for <code>y = x</code> it is false."
            },
            {
              "tac": "exact hy",
              "state": "No goals.",
              "h": "<code>hy</code>’s type <code>fact (fun σ => σ y = v) s.store hFrame</code> unfolds to precisely <code>s.store y = v</code>. Definitional unfolding, not a rewrite."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "Here is the top of the program proof, so you can see the layout the four intermediate assertions describe. The goal after the first <code>hoare_seq</code>:"
        },
        {
          "t": "state",
          "src": "case refine_1\ntmp₁ tmp₂ : Var\nl₁ l₂ : Loc\na b : Val\nhne : tmp₁ ≠ tmp₂\n⊢ Hoare (l₁ ↦ a ∗ l₂ ↦ b) (Cmd.load tmp₁ l₁) ((_root_.pure fun σ => σ tmp₁ = a) ∗ l₁ ↦ a ∗ l₂ ↦ b)\n\ncase refine_2\ntmp₁ tmp₂ : Var\nl₁ l₂ : Loc\na b : Val\nhne : tmp₁ ≠ tmp₂\n⊢ Hoare ((_root_.pure fun σ => σ tmp₁ = a) ∗ l₁ ↦ a ∗ l₂ ↦ b)\n    (Cmd.load tmp₂ l₂ ;; Cmd.write l₁ (Atom.var tmp₂) ;; Cmd.write l₂ (Atom.var tmp₁)) (l₁ ↦ b ∗ l₂ ↦ a)",
          "cap": "The first goal is one command; the second is the rest of the program with the first intermediate assertion as its precondition. Recurse."
        },
        {
          "t": "detail",
          "title": "Why tmp₁ ≠ tmp₂ is not bureaucracy — the aliased run, mechanised",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "A side condition you cannot break is a side condition you have not understood, so here is the break. Take <code>tmp₁ = tmp₂ = 0</code>, <code>l₁ = 0</code>, <code>l₂ = 1</code>, <code>a = 1</code>, <code>b = 2</code>. The second load clobbers the variable the first load filled, so at the writes both <code>.var tmp₁</code> and <code>.var tmp₂</code> evaluate to <code>2</code>, and the run ends with <b>both</b> cells holding <code>2</code> instead of the two cells exchanged. The specification, quantified over all variables, therefore has no proof at all:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "example : ¬ ∀ (t₁ t₂ : Var) (l₁ l₂ : Loc) (a b : Val),\n    Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap t₁ t₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a)) := by\n  intro H\n  have hpre : ((0 ↦ 1) ∗ (1 ↦ 2)) (fun _ => 0)\n      (Heap.union (Heap.singleton 0 1) (Heap.singleton 1 2)) :=\n    ⟨Heap.singleton 0 1, Heap.singleton 1 2, singleton_disjoint 1 2 (by decide), rfl, rfl, rfl⟩\n  obtain ⟨s', hex, hq⟩ := H 0 0 0 1 1 2 _ _ hpre\n  rw [swap] at hex\n  cases hex with | seq hA hB =>\n  cases hA with | load hl1 =>\n  cases hB with | seq hC hD =>\n  cases hC with | load hl2 =>\n  cases hD with | seq hE hF =>\n  cases hE with | write _ =>\n  cases hF with | write _ =>\n  obtain ⟨ha, hb, -, hu, hea, heb⟩ := hq\n  subst hea; subst heb\n  have h1 := congrFun hu 1\n  simp [Heap.union, Heap.singleton, Heap.write, Store.set, Atom.eval] at h1 hl2\n  exact absurd (hl2.trans h1) (by decide)",
              "cap": "Compiles against lean/prelude/m9.lean together with the def of swap from the exercise statement."
            },
            {
              "t": "p",
              "h": "Read the shape of it, because this is what refuting a triple always looks like here. <code>Hoare</code> is <i>total</i> correctness — <code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ,h⟩ s' ∧ Q s'.store s'.heap</code> — so to refute it you supply a concrete <code>σ</code> and <code>h</code> satisfying <code>P</code>, take the <code>s'</code> the triple promises, and then use the fact that the program is deterministic to pin <code>s'</code> down. The seven <code>cases</code> are that pinning: each one inverts one command and replaces <code>s'</code> a little further by an explicit state, until <code>hq</code> is a statement about a heap you can evaluate. The last three lines evaluate it at location <code>1</code>: the postcondition demands <code>some 1</code> there, the run delivers <code>some 2</code>."
            },
            {
              "t": "p",
              "h": "Note which hypothesis does the work at the end. <code>hl2</code> is the second load’s side condition, <code>h1</code> is the postcondition read off at location <code>1</code>, and after <code>simp</code> they say <code>2 = v✝</code> and <code>v✝ = 1</code>. Chaining them gives <code>2 = 1</code>. The aliasing never appears as an error; it appears as an arithmetic contradiction three commands later. That is exactly why you want the side condition stated up front, where it is one hypothesis, rather than discovered here, where it is a counterexample."
            },
            {
              "t": "dl",
              "items": [
                {
                  "k": "rw [swap] at hex",
                  "h": "Rewriting with a <i>definition</i>’s name rather than a theorem’s. Lean generates an equation lemma for every <code>def</code>, and <code>rw [swap]</code> uses it to replace <code>swap 0 0 0 1</code> by its body. You need this here because <code>cases</code> looks at the head symbol of <code>hex</code>’s type: until <code>swap</code> is unfolded, that head is <code>swap</code>, not <code>;;</code>, and there is no constructor to case on."
                },
                {
                  "k": "⟨ha, hb, -, hu, hea, heb⟩",
                  "h": "The <code>-</code> in an <code>obtain</code> pattern means “this component exists, name it nothing, discard it”. Here it drops the disjointness proof, which the argument never uses. Writing <code>_</code> instead would keep it in the context under an inaccessible name; <code>-</code> clears it outright."
                },
                {
                  "k": "by decide",
                  "h": "A proof by evaluation. It applies to a decidable proposition with no free variables — here <code>(1 : Loc) ≠ 2</code> and <code>¬ (2 = 1)</code> — and closes it by running the decision procedure and checking the answer is <code>true</code>. It is not <code>simp</code> and not <code>rfl</code>: it is the <code>Decidable</code> instance doing the work. It fails, sometimes very slowly, on anything with a variable in it."
                },
                {
                  "k": "congrFun hu 1",
                  "h": "<code>hu</code> is an equation between two <i>heaps</i>, that is between two functions. <code>congrFun hu 1</code> applies both sides to the location <code>1</code>, turning it into an equation between two <code>Option Val</code>s that <code>simp</code> can evaluate. This is <code>funext</code> run backwards, and it is the standard way to get from a heap equation to a fact about one cell."
                }
              ]
            }
          ]
        },
        {
          "t": "detail",
          "title": "The complete proof — open it after you have written your own",
          "tag": "spoiler",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Around forty lines, of which the only interesting choices are the three <code>Q</code>s. Everything else is the frame–apply–reshape loop. It compiles against the M9 prelude as written."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem swap_spec (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) (a b : Val) (hne : tmp₁ ≠ tmp₂) :\n    Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap tmp₁ tmp₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a)) := by\n  refine hoare_seq (Q := pure (fun σ => σ tmp₁ = a) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b))) ?_ ?_\n  · -- load tmp₁ l₁, framed by l₂ ↦ b\n    have step : Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (.load tmp₁ l₁)\n        ((pure (fun σ => σ tmp₁ = a) ∗ (l₁ ↦ a)) ∗ (l₂ ↦ b)) :=\n      hoare_frame (hoare_load tmp₁ l₁ a) (heapLocal_load tmp₁ l₁)\n        (preserves_of_heapOnly _ (heapOnly_pointsTo l₂ b))\n    exact hoare_consequence (entails_refl _) step (star_assoc_left _ _ _)\n  refine hoare_seq (Q := pure (fun σ => σ tmp₁ = a) ∗\n      (pure (fun σ => σ tmp₂ = b) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b)))) ?_ ?_\n  · -- load tmp₂ l₂, framed by l₁ ↦ a inside and by the pure fact outside\n    have inner : Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (.load tmp₂ l₂)\n        (pure (fun σ => σ tmp₂ = b) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b))) := by\n      have base : Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.load tmp₂ l₂)\n          ((pure (fun σ => σ tmp₂ = b) ∗ (l₂ ↦ b)) ∗ (l₁ ↦ a)) :=\n        hoare_frame (hoare_load tmp₂ l₂ b) (heapLocal_load tmp₂ l₂)\n          (preserves_of_heapOnly _ (heapOnly_pointsTo l₁ a))\n      refine hoare_consequence (star_comm _ _) base ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (star_comm _ _)\n    have framed : Hoare (((l₁ ↦ a) ∗ (l₂ ↦ b)) ∗ pure (fun σ => σ tmp₁ = a)) (.load tmp₂ l₂)\n        ((pure (fun σ => σ tmp₂ = b) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b))) ∗ pure (fun σ => σ tmp₁ = a)) :=\n      hoare_frame inner (heapLocal_load tmp₂ l₂) (preserves_load_fact l₂ hne)\n    exact hoare_consequence (star_comm _ _) framed (star_comm _ _)\n  refine hoare_seq (Q := pure (fun σ => σ tmp₁ = a) ∗ ((l₁ ↦ b) ∗ (l₂ ↦ b))) ?_ ?_\n  · -- write l₁ (.var tmp₂), framed by l₂ ↦ b inside and by the pure fact outside\n    have inner : Hoare ((aAnd (fact (fun σ => σ tmp₂ = b)) (l₁ ↦ a)) ∗ (l₂ ↦ b))\n        (.write l₁ (.var tmp₂)) ((l₁ ↦ b) ∗ (l₂ ↦ b)) :=\n      hoare_frame (hoare_write_val l₁ (.var tmp₂) a b) (heapLocal_write l₁ (.var tmp₂))\n        (preserves_of_storeStable (storeStable_write l₁ (.var tmp₂)) _)\n    have framed : Hoare (((aAnd (fact (fun σ => σ tmp₂ = b)) (l₁ ↦ a)) ∗ (l₂ ↦ b))\n          ∗ pure (fun σ => σ tmp₁ = a))\n        (.write l₁ (.var tmp₂)) (((l₁ ↦ b) ∗ (l₂ ↦ b)) ∗ pure (fun σ => σ tmp₁ = a)) :=\n      hoare_frame inner (heapLocal_write l₁ (.var tmp₂))\n        (preserves_of_storeStable (storeStable_write l₁ (.var tmp₂)) _)\n    refine hoare_consequence ?_ framed (star_comm _ _)\n    refine entails_trans (star_comm _ _) ?_\n    exact star_mono_left _ (pure_star_regroup _ _ _)\n  · -- write l₂ (.var tmp₁), framed by l₁ ↦ b\n    have step : Hoare ((aAnd (fact (fun σ => σ tmp₁ = a)) (l₂ ↦ b)) ∗ (l₁ ↦ b))\n        (.write l₂ (.var tmp₁)) ((l₂ ↦ a) ∗ (l₁ ↦ b)) :=\n      hoare_frame (hoare_write_val l₂ (.var tmp₁) b a) (heapLocal_write l₂ (.var tmp₁))\n        (preserves_of_storeStable (storeStable_write l₂ (.var tmp₁)) _)\n    refine hoare_consequence ?_ step (star_comm _ _)\n    refine entails_trans (star_mono_right _ (star_comm _ _)) ?_\n    exact pure_star_regroup _ _ _",
              "cap": "Verified against lean/prelude/m9.lean with the def of swap from the exercise statement. Not part of the corpus — this is one solution among many."
            },
            {
              "t": "p",
              "h": "Two details worth extracting. First, the double framing in the middle two steps: <code>inner</code> handles the command and its untouched cell, <code>framed</code> wraps the carried fact around the whole of <code>inner</code>. That nesting is forced, because <code>hoare_frame</code> takes one frame at a time and always puts it on the right. Second, every single <code>hoare_consequence</code> in the proof has a <code>star_comm</code> in it somewhere; that is the tax for keeping the pure facts on the left while the frame rule insists on the right. Choosing the opposite convention — facts on the right — would move the commutations around but not remove them."
            }
          ]
        }
      ],
      "pitfall": "Writing the hypothesis the wrong way round. <code>preserves_load_fact</code> demands <code>hne : y ≠ x</code>, where <code>x</code> is the variable being loaded into and <code>y</code> is the one the fact is about. In the swap proof you are loading into <code>tmp₂</code> and carrying a fact about <code>tmp₁</code>, so what is needed is <code>tmp₁ ≠ tmp₂</code> — which happens to be the natural way to state the hypothesis, but only by luck. Hand it <code>hne : x ≠ y</code> instead and <code>simp [Store.set, hne]</code> stops working: <code>simp</code> orients <code>hne</code> into the rewrite <code>(x = y) = False</code>, the condition in the goal is <code>y = x</code>, and the two do not match, so the <code>if</code> is never resolved. Lean says so twice — the goal is left as <code>⊢ (if y = x then v✝ else s.store y) = v</code>, and the linter adds <code>This simp argument is unused: hne</code>. The fix is <code>hne.symm</code>, which compiles unchanged; not a different proof.",
      "variants": "<b>Drop <code>hne</code></b> and the theorem is false, not merely unprovable — and it is worth having that as a compiled fact rather than a hand-trace, so it is proved in the panel above. Take <code>tmp₁ = tmp₂</code>: the second load overwrites the variable the first fact was about, so after it you know <code>σ tmp₁ = b</code>; the first write stores <code>b</code> into <code>l₁</code> — correct by accident — and the second stores <code>b</code> into <code>l₂</code> as well. You end with both cells holding <code>b</code>. The single point of failure inside the proof is the <code>simp [Store.set, hne]</code> line: with <code>y = x</code> the <code>if</code> takes the <i>then</i> branch, and the surviving fact is about the newly loaded value, not the old one. <b>Drop the requirement that the two loads come before the two writes</b> and the same collision appears on the heap side instead: writing <code>l₁</code> before reading <code>l₂</code> is fine here only because they are different cells, which <code>two_cells_distinct</code> gives you — but if the program wrote and then read the <i>same</i> cell you would need the value-tracking that <code>hoare_write_val</code> provides, in the other direction. <b>Weaken <code>Preserves</code> to a syntactic side condition</b> (“<code>R</code> mentions no variable modified by <code>c</code>”) and this exercise still works, but you lose every case where a command modifies a variable and re-establishes the fact anyway — the example in the aside near the top of the chapter is one. The semantic condition is strictly more permissive and, here, strictly easier to prove."
    },
    {
      "t": "sec",
      "s": "What carries forward"
    },
    {
      "t": "p",
      "h": "Everything in this chapter described a bounded number of cells, and every assertion could be written out in full. M10 removes that restriction: <code>listRep</code> and <code>lseg</code> are recursive assertions describing an unbounded structure, and the striking thing is that the frame-apply-reshape loop does not change at all. What changes is the algebra you reshape with — <code>lseg_append</code> takes the place of <code>star_assoc_left</code> as the workhorse — and the fact that unfolding a recursive predicate hands you non-aliasing of the whole structure for free, in the same way that <code>two_cells_distinct</code> handed you <code>src ≠ dst</code> here."
    },
    {
      "t": "p",
      "h": "If you found the reshaping tedious, that is the correct reaction, and it is the motivation for M12: a weakest-precondition calculus computes the intermediate assertions instead of making you invent them. But the calculus is justified by the rules you have just been using by hand, so the tedium was not wasted — it was the specification of the tool."
    },
    {
      "t": "dod",
      "h": "You can verify small heap-manipulating programs compositionally, without unfolding <code>Exec</code> outside of the primitive rules."
    }
  ]
});
