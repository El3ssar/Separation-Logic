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
      "Verify a complete heap-manipulating program without writing <code>Heap</code>, <code>union</code> or <code>disjoint</code> anywhere in the proof.",
      "Discharge <code>Preserves c R</code> from either end: <code>preserves_of_heapOnly</code> when the frame ignores the store, <code>preserves_of_storeStable</code> when the command does.",
      "Read <code>hoare_seq</code>’s intermediate assertion off the <i>next</i> command’s footprint instead of guessing it.",
      "Bend an assertion into the exact syntactic shape <code>hoare_frame</code> matches, using <code>star_assoc_left</code>, <code>star_comm</code>, <code>star_mono_left</code>, <code>star_mono_right</code> and <code>pure_star_regroup</code>.",
      "Say where a hypothesis like <code>tmp₁ ≠ tmp₂</code> is spent, and why the store needs one where the heap does not."
    ],
    "needs": [
      "<code>hoare_seq</code> with its intermediate assertion supplied as <code>(Q := …)</code>, and <code>hoare_consequence</code>.",
      "The three small rules <code>hoare_load</code>, <code>hoare_write</code>, <code>hoare_free</code>.",
      "<code>hoare_frame</code>, its two side conditions, and <code>preserves_of_heapOnly</code>.",
      "M4’s <code>entails_trans</code>, <code>star_comm</code>, <code>star_assoc_left</code>, <code>star_mono_left</code>, <code>star_mono_right</code>, <code>star_emp_left</code>. All six are used below."
    ],
    "payoff": "A verification becomes a short readable term, and the same term works whether the untouched part of the heap is one cell or ten thousand."
  },

  "blocks": [
    { "t": "h3", "s": "One lemma, and the sorry goes" },

    { "t": "p",
      "h": "<code>Preserves (.free l) (pure (fun σ => σ x = v))</code> holds for a reason that never mentions the assertion. So write the reason down as a property of the command alone, and every obligation of that shape closes at the same time." },

    { "t": "anat",
      "src": "def StoreStable (c : Cmd) : Prop := ∀ s s', Exec c s s' → s'.store = s.store\n\ntheorem storeStable_write (l : Loc) (e : Atom) : StoreStable (.write l e) := by\n  intro s s' hex; cases hex; rfl\n\ntheorem storeStable_free (l : Loc) : StoreStable (.free l) := by\n  intro s s' hex; cases hex; rfl\n\ntheorem preserves_of_storeStable {c : Cmd} (h : StoreStable c) (R : Assertion) :\n    Preserves c R := by\n  intro s s' hex hFrame hr\n  rw [h s s' hex]; exact hr",
      "parts": [
        { "m": "∀ s s', Exec c s s' → s'.store = s.store",
          "h": "No heap, no assertion, no frame. One proof per command, three tactics long, because inversion on <code>Exec</code> pins the final state and the store field of that state is <code>s.store</code> written out." },
        { "m": "(R : Assertion)",
          "h": "A parameter, not a hypothesis with conditions attached. That is the whole content: store stability gives you <code>Preserves c R</code> for <b>every</b> <code>R</code> at once, pure facts about program variables included." },
        { "m": "rw [h s s' hex]; exact hr",
          "h": "<code>h s s' hex</code> is the equation <code>s'.store = s.store</code>. The goal <code>R s'.store hFrame</code> becomes <code>R s.store hFrame</code>, which is <code>hr</code>. The equation does everything; there is no case analysis on <code>R</code> because there is nothing to analyse." }
      ] },

    { "t": "trace",
      "title": "storeStable_write, tactic by tactic",
      "start": "l : Loc\ne : Atom\n⊢ StoreStable (Cmd.write l e)",
      "steps": [
        { "tac": "intro s s' hex",
          "state": "l : Loc\ne : Atom\ns s' : State\nhex : Exec (Cmd.write l e) s s'\n⊢ s'.store = s.store",
          "h": "The goal is an equation between two stores, and <code>hex</code> is the only thing in the context that relates them." },
        { "tac": "cases hex",
          "state": "case write\nl : Loc\ne : Atom\ns : State\nold✝ : Val\nhl✝ : s.heap l = some old✝\n⊢ { store := s.store, heap := s.heap.write l (Atom.eval s.store e) }.store = s.store",
          "h": "<code>s'</code> has left the context: <code>cases</code> replaced it by the state <code>Exec.write</code> builds. <code>old✝</code> and <code>hl✝</code> are inaccessible because no names were given, and neither is needed." },
        { "tac": "rfl",
          "state": "No goals.",
          "h": "The projection out of the literal structure computes to <code>s.store</code>, so both sides are the same term. The two sides were not syntactically equal before this line — they become so." }
      ],
      "done": "No goals." },

    { "t": "p",
      "h": "M8’s term compiles now, with the hole filled and nothing else touched:" },

    { "t": "code", "tag": "illustration",
      "src": "theorem readAndFree_framed (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=\n  hoare_seq\n    (hoare_consequence (entails_refl _) (hoare_load x l v) (star_comm _ _))\n    (hoare_consequence (entails_refl _)\n      (hoare_frame (hoare_free l v) (heapLocal_free l)\n        (preserves_of_storeStable (storeStable_free l) _))\n      (star_emp_left _))",
      "cap": "not in the corpus — compiles against prelude/m9.lean" },

    { "t": "p",
      "h": "The store obligation is now covered from both ends. <code>preserves_of_heapOnly</code> fixes the assertion and quantifies over commands; <code>preserves_of_storeStable</code> fixes the command and quantifies over assertions. Between them they discharge every <code>Preserves</code> in this chapter but one, and that one waits for the last program." },

    { "t": "detail", "title": "The witness for “strictly weaker”", "tag": "aside", "open": false,
      "blocks": [
        { "t": "p",
          "h": "<code>Preserves</code> was chosen over the classical “<code>R</code> mentions no variable modified by <code>c</code>” partly on the claim that it is strictly weaker. Here is the witness. <code>x := x</code> modifies <code>x</code>, so syntactically it is out of bounds for every frame mentioning <code>x</code>; semantically it preserves everything there is:" },
        { "t": "code", "tag": "illustration",
          "src": "example (x : Var) (R : Assertion) : Preserves (.assign x (.var x)) R := by\n  intro s s' hex hFrame hr\n  cases hex with\n  | assign =>\n      have : Store.set s.store x (Atom.eval s.store (.var x)) = s.store := by\n        funext y; by_cases hy : y = x <;> simp [Store.set, Atom.eval, hy]\n      show R (Store.set s.store x (Atom.eval s.store (.var x))) hFrame\n      rw [this]; exact hr",
          "cap": "not in the corpus. The funext is the point: Store.set σ x (σ x) and σ agree at every variable but are not the same term, so the equation must be proved pointwise before rw can use it." },
        { "t": "p",
          "h": "This particular command is also <code>StoreStable</code>, so the same fact could have come through <code>preserves_of_storeStable</code>. That costs the witness nothing: the syntactic condition rejects it and <code>Preserves</code> accepts it, which is the whole claim." }
      ] },

    { "t": "h3", "s": "Four rules, and one thing you have to invent" },

    { "t": "p",
      "h": "Every verification below is built from four theorems." },

    { "t": "txt",
      "src": "  hoare_seq          cut the program at an assertion you choose\n  hoare_frame        set aside the cells this command does not touch\n  hoare_load  hoare_write_val  hoare_free      fire the rule on the footprint\n  hoare_consequence  reshape an assertion so the next rule's pattern fits" },

    { "t": "p",
      "h": "One command is discharged by one term, always the same term — a <code>hoare_frame</code> sandwiched between two reshapings:" },

    { "t": "txt",
      "src": "  hoare_consequence  hin  (hoare_frame  small  hlocal  hpres)  hout\n\n     hin     :  P ⊢ footprint ∗ frame\n     small   :  Hoare footprint c result\n     hlocal  :  HeapLocal c            — cited from M8\n     hpres   :  Preserves c frame      — one of the two helpers\n     hout    :  result ∗ frame ⊢ Q" },

    { "t": "p",
      "h": "A program is those terms chained by <code>hoare_seq</code>. <code>hin</code> and <code>hout</code> mention no command: they are entailments between assertions, and proving them is pure ∗-algebra. So you carry an assertion forward through the program, one command at a time, and what it becomes is fixed by the rule for that command. That is what <i>symbolic execution</i> names, and the assertion is the only state left to look at." },

    { "t": "note", "kind": "key", "title": "The frame goes on the right, so the footprint goes on the left",
      "h": "<code>hoare_frame</code> turns <code>Hoare P c Q</code> into <code>Hoare (P ∗ R) c (Q ∗ R)</code>. Handed an assertion, it matches the pattern <code>?P ∗ ?R</code> against it syntactically, and <code>∗</code> is right-associative. So the cell the command touches must be the leftmost factor, literally, before the rule will fire; <code>hin</code> and <code>hout</code> exist to put it there and to put it back. When one of these proofs is hard, the parentheses are in the wrong place — nothing is mathematically unclear." },

    { "t": "cmp",
      "left": { "t": "What you would write on paper", "kind": "good",
        "h": "“Load <code>src</code> into <code>tmp</code>; <code>dst</code> is untouched, so it is still <code>dst ↦ b</code>, and now <code>tmp = a</code>. Write <code>tmp</code> to <code>dst</code>; <code>src</code> is untouched.” Two sentences. The reassociations are invisible because <code>∗</code> is silently associative and commutative." },
      "right": { "t": "What Lean makes you write",
        "h": "A syntactic match does not care that <code>star_assoc_left</code> exists, so every rearrangement the paper proof performed silently is applied by hand, as an entailment. Two of them, for two sentences:",
        "tag": "sketch",
        "src": "refine entails_trans (star_assoc_left _ _ _) ?_\nrefine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_" } },

    { "t": "sec", "s": "Program 1 · copy one cell into another" },

    { "t": "code",
      "src": "def copyCell (tmp : Var) (src dst : Loc) : Cmd :=\n  .load tmp src ;; .write dst (.var tmp)" },

    { "t": "txt",
      "src": "  { src ↦ a ∗ dst ↦ b }\n      copyCell tmp src dst\n  { src ↦ a ∗ dst ↦ a }" },

    { "t": "p",
      "h": "The write has to store the value the load read, and nothing in the program connects the two commands. The connection is the pure fact <code>σ tmp = a</code> that <code>hoare_load</code> leaves behind, so the proof is entirely about getting that fact to the one place a write rule can consume it. Two of the rules you have refuse to cooperate." },

    { "t": "h4", "s": "The write rule has no postcondition you can name" },

    { "t": "p",
      "h": "Feed M7’s <code>hoare_write</code> to <code>hoare_frame</code> at the point the copy proof needs it:" },

    { "t": "state",
      "src": "error: Application type mismatch: The argument\n  hoare_write dst (Atom.var tmp) b\nhas type\n  Hoare (dst ↦ b) (Cmd.write dst (Atom.var tmp)) fun σ h => (dst ↦ Atom.eval σ (Atom.var tmp)) σ h\nbut is expected to have type\n  Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b)) (Cmd.write dst (Atom.var tmp)) (dst ↦ a)\nin the application\n  hoare_frame (hoare_write dst (Atom.var tmp) b)",
      "cap": "Both ends are wrong: the precondition is missing the fact, and the postcondition is a lambda where a points-to is wanted." },

    { "t": "cmp",
      "left": { "t": "M7’s rule", "kind": "bad",
        "h": "The value stored is whatever <code>e</code> evaluates to in the final store, so the postcondition has to be a lambda. To specialise it to <code>dst ↦ a</code> you need <code>Atom.eval σ (.var tmp) = a</code>, and the statement has nowhere to put that.",
        "tag": "sketch",
        "src": "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h)" },
      "right": { "t": "The variant", "kind": "good",
        "h": "Take the stored value as a parameter, and move the obligation “<code>e</code> really evaluates to <code>v</code>” into the precondition as a <code>fact</code>. The postcondition is then the flat <code>l ↦ v</code>, and the <code>fact</code> is exactly what the preceding load left lying around.",
        "tag": "sketch",
        "src": "theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :\n    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v)" } },

    { "t": "code",
      "src": "theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :\n    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v) := by\n  intro σ h hpre\n  obtain ⟨hv, hp⟩ := hpre\n  subst hp\n  refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,\n          Exec.write (singleton_same l old), ?_⟩\n  show Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l v\n  rw [write_singleton]\n  have : e.eval σ = v := hv\n  rw [this]" },

    { "t": "p",
      "h": "The <code>fact</code> sits under an <code>aAnd</code> rather than to the left of a <code>∗</code> because the write needs the cell and the knowledge at the same heap; a <code>∗</code> there would cut the heap in two and hand the empty half to the fact, which is a different statement." },

    { "t": "trace",
      "title": "hoare_write_val, tactic by tactic",
      "start": "l : Loc\ne : Atom\nold v : Val\n⊢ Hoare (aAnd (fact fun σ => Atom.eval σ e = v) (l ↦ old)) (Cmd.write l e) (l ↦ v)",
      "steps": [
        { "tac": "intro σ h hpre",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nh : Heap\nhpre : aAnd (fact fun σ => Atom.eval σ e = v) (l ↦ old) σ h\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (l ↦ v) s'.store s'.heap",
          "h": "Three <code>intro</code>s put you in front of the existential." },
        { "tac": "obtain ⟨hv, hp⟩ := hpre",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nh : Heap\nhv : fact (fun σ => Atom.eval σ e = v) σ h\nhp : (l ↦ old) σ h\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (l ↦ v) s'.store s'.heap",
          "h": "<code>hv</code> is the evaluation fact, <code>hp</code> the ownership. Only <code>hp</code> says anything about <code>h</code>." },
        { "tac": "subst hp",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old } s' ∧ (l ↦ v) s'.store s'.heap",
          "h": "<code>hp</code> is the equation <code>h = Heap.singleton l old</code>, so <code>h</code> is gone from the goal and the heap the command runs in is now written out." },
        { "tac": "refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩, Exec.write (singleton_same l old), ?_⟩",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ (l ↦ v) { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.store\n    { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.heap",
          "h": "Witness state and derivation supplied; <code>singleton_same l old</code> is the cell-exists premise <code>Exec.write</code> demands. What is left is the postcondition, stated through projections out of the literal state." },
        { "tac": "show Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l v",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ (Heap.singleton l old).write l (Atom.eval σ e) = Heap.singleton l v",
          "h": "The projections compute away and <code>(l ↦ v) σ' h'</code> unfolds to <code>h' = Heap.singleton l v</code>, both for free. The goal is now a heap equation, which M1 has lemmas about." },
        { "tac": "rw [write_singleton]",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\n⊢ Heap.singleton l (Atom.eval σ e) = Heap.singleton l v",
          "h": "All that remains is that the two stored values agree." },
        { "tac": "have : e.eval σ = v := hv",
          "state": "l : Loc\ne : Atom\nold v : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ (Heap.singleton l old)\nthis : Atom.eval σ e = v\n⊢ Heap.singleton l (Atom.eval σ e) = Heap.singleton l v",
          "h": "<code>fact φ</code> is <code>fun σ _ => φ σ</code>, so <code>hv</code>’s type <i>is</i> that equation. Nothing is proved on this line, and it is not needed either — <code>rw [hv]</code> finds the equation through the unfolding on its own. The ascription puts the fact on the page instead of leaving it inside a <code>fact</code>." },
        { "tac": "rw [this]",
          "state": "No goals.",
          "h": "Both sides become <code>Heap.singleton l v</code> and <code>rw</code>’s trailing <code>rfl</code> closes it." }
      ],
      "done": "No goals." },

    { "t": "h4", "s": "The fact arrives on the wrong side of the star" },

    { "t": "p",
      "h": "<code>hoare_load</code> hands you <code>pure φ ∗ (src ↦ a)</code>, and <code>hoare_write_val</code> wants <code>aAnd (fact φ) (dst ↦ b)</code> as the left factor of a <code>∗</code>. M4’s <code>star_pure_left</code> converts <code>pure φ ∗ P ⊢ aAnd (fact φ) P</code>, which looks like the right move; instantiate it at <code>P := (dst ↦ b) ∗ (src ↦ a)</code> and you land on <code>aAnd (fact φ) ((dst ↦ b) ∗ (src ↦ a))</code>. That has an <code>aAnd</code> at the top and no <code>∗</code>, so <code>?P ∗ ?R</code> does not match and the frame rule is dead. Getting unstuck from there means proving <code>aAnd (fact φ) (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R</code>, which is this lemma the long way round:" },

    { "t": "code",
      "src": "theorem pure_star_regroup (φ : Store → Prop) (P R : Assertion) :\n    pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by\n  intro σ h hstar\n  obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar\n  subst he\n  refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩\n  rw [hu, union_empty_left, huPR]" },

    { "t": "p",
      "h": "The fact lands inside the left factor and a top-level <code>∗</code> survives for the frame rule to bite on. What makes it true is that <code>pure</code> owns the empty heap, so the three-way split <code>h = h₀ ∪ (hP ∪ hR)</code> collapses to the two-way split the conclusion needs." },

    { "t": "detail", "title": "pure_star_regroup, tactic by tactic", "tag": "aside", "open": false,
      "blocks": [
        { "t": "p", "h": "The only proof in the chapter that takes a <code>∗</code> apart by hand. Worth reading once, then forgetting." },
        { "t": "trace",
          "title": "pure_star_regroup",
          "start": "φ : Store → Prop\nP R : Assertion\n⊢ _root_.pure φ ∗ P ∗ R ⊢ aAnd (fact φ) P ∗ R",
          "steps": [
            { "tac": "intro σ h hstar",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh : Heap\nhstar : (_root_.pure φ ∗ P ∗ R) σ h\n⊢ (aAnd (fact φ) P ∗ R) σ h",
              "h": "The star to be taken apart is <code>hstar</code>, the star to be built is the goal, and nothing else is in play." },
            { "tac": "obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh h₀ hPR : Heap\nhd : h₀.disjoint hPR\nhu : h = h₀.union hPR\nhφ : fact φ σ h₀\nhe : emp σ h₀\nhP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\n⊢ (aAnd (fact φ) P ∗ R) σ h",
              "h": "One nested pattern destroys both stars and the <code>aAnd</code> inside <code>pure</code>, in one tactic." },
            { "tac": "subst he",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh hPR hP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\nhd : Heap.empty.disjoint hPR\nhu : h = Heap.empty.union hPR\nhφ : fact φ σ Heap.empty\n⊢ (aAnd (fact φ) P ∗ R) σ h",
              "h": "<code>he</code> is <code>h₀ = Heap.empty</code>. Watch <code>hd</code>, <code>hu</code> and <code>hφ</code> get rewritten and re-ordered to the bottom of the context: normal, harmless, and a reason not to rely on hypothesis order in a printed goal." },
            { "tac": "refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩",
              "state": "φ : Store → Prop\nP R : Assertion\nσ : Store\nh hPR hP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\nhd : Heap.empty.disjoint hPR\nhu : h = Heap.empty.union hPR\nhφ : fact φ σ Heap.empty\n⊢ h = hP.union hR",
              "h": "The new cut is the inner one. Five of the six slots are already in context; only the heap equation is left open." },
            { "tac": "rw [hu, union_empty_left, huPR]",
              "state": "No goals.",
              "h": "<code>h</code> becomes <code>Heap.empty ∪ hPR</code>, that becomes <code>hPR</code>, that becomes <code>hP ∪ hR</code>, and the trailing <code>rfl</code> finishes." }
          ],
          "done": "No goals." }
      ] },

    { "t": "h4", "s": "Everything the two programs need" },

    { "t": "dl",
      "items": [
        { "k": "hoare_seq (Q := …) h₁ h₂",
          "h": "The cut. <code>Q</code> appears in neither the conclusion nor the other arguments, so Lean cannot infer it and you always supply it by name." },
        { "k": "hoare_frame hc hlocal hpres",
          "h": "Small triple, heap locality, store preservation. The frame <code>R</code> is implicit and is determined by <i>nothing in the arguments</i> — it comes from the expected type, which is why these are written as an ascribed <code>have</code>." },
        { "k": "heapLocal_load · heapLocal_write · heapLocal_free",
          "h": "Cited, never proved again." },
        { "k": "preserves_of_heapOnly _ (heapOnly_pointsTo l v)",
          "h": "When the frame is a points-to. <code>heapOnly_star</code> combines them when it is a <code>∗</code> of several cells." },
        { "k": "preserves_of_storeStable (storeStable_write l e) _",
          "h": "When the command is a <code>write</code> or a <code>free</code>. Any frame at all, facts included." },
        { "k": "hoare_consequence hpre hc hpost",
          "h": "Reshape. Pass <code>entails_refl _</code> on the side you are not changing; you will write that a lot." },
        { "k": "star_comm · star_assoc_left · star_mono_left · star_mono_right · star_emp_left · pure_star_regroup",
          "h": "The reshaping vocabulary, chained with <code>entails_trans</code>. Six lemmas cover every rearrangement in the chapter." }
      ] },

    { "t": "p",
      "h": "Here is the copy proof as the assertion Lean carries at each point. Read the right-hand column downwards and you have the proof:" },

    { "t": "tbl",
      "head": ["where you are", "the assertion in hand"],
      "rows": [
        ["start", "<code>(src ↦ a) ∗ (dst ↦ b)</code>"],
        ["after <code>hoare_load</code> on the footprint alone", "<code>pure (σ tmp = a) ∗ (src ↦ a)</code>"],
        ["…re-attaching the frame <code>dst ↦ b</code>", "<code>(pure (σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)</code>"],
        ["…<code>star_assoc_left</code>", "<code>pure (σ tmp = a) ∗ ((src ↦ a) ∗ (dst ↦ b))</code>"],
        ["…<code>star_mono_right _ (star_comm …)</code>", "<code>pure (σ tmp = a) ∗ ((dst ↦ b) ∗ (src ↦ a))</code>"],
        ["…<code>pure_star_regroup</code>", "<code>(aAnd (fact (σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code>"],
        ["after <code>hoare_write_val</code>, frame <code>src ↦ a</code>", "<code>(dst ↦ a) ∗ (src ↦ a)</code>"],
        ["…<code>star_comm</code>", "<code>(src ↦ a) ∗ (dst ↦ a)</code>"]
      ],
      "cap": "Eight lines, of which two are rule applications and five are reshaping. That ratio is typical." },

    { "t": "note", "kind": "tip", "title": "How the intermediate assertion was found",
      "h": "Not by pushing forward from the precondition. Work backwards from the second command: its footprint is <code>aAnd (fact (…= a)) (dst ↦ b)</code>, which is <code>hoare_write_val</code>’s precondition verbatim, and everything else has to sit to the right of a top-level <code>∗</code>. That fixes <code>Q = (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code> with no freedom left, and the first half of the proof becomes “get from the load’s output to <code>Q</code>”." },

    {
      "t": "ex",
      "id": "m9-1",
      "name": "copyCell_spec",
      "hard": true,
      "why": "The first compositional verification, and the template for every proof after it. No heap, no union, no disjointness appears anywhere in it.",
      "setup": "Everything is in scope: <code>hoare_seq</code>, <code>hoare_consequence</code>, <code>hoare_frame</code>, <code>hoare_load</code>, <code>hoare_write_val</code>, <code>heapLocal_load</code>, <code>heapLocal_write</code>, <code>preserves_of_heapOnly</code>, <code>heapOnly_pointsTo</code>, <code>preserves_of_storeStable</code>, <code>storeStable_write</code>, and <code>entails_refl</code>, <code>entails_trans</code>, <code>star_assoc_left</code>, <code>star_comm</code>, <code>star_mono_right</code>, <code>pure_star_regroup</code>.",
      "goal": "theorem copyCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst)\n      ((src ↦ a) ∗ (dst ↦ a))",
      "hints": [
        "Start from the <i>second</i> command. Write down the exact precondition <code>hoare_write_val dst (.var tmp) b a</code> demands, then put everything the write does not touch to the right of a top-level <code>∗</code>. That assertion is your <code>Q</code>.",
        "Both halves have the same shape: build the framed triple as <code>have step : … := hoare_frame …</code>, then fix the ends with <code>hoare_consequence</code>. For the load the frame is <code>dst ↦ b</code> and the preservation obligation is <code>preserves_of_heapOnly _ (heapOnly_pointsTo dst b)</code>; for the write the frame is <code>src ↦ a</code> and it is <code>preserves_of_storeStable (storeStable_write dst (.var tmp)) _</code>.",
        "In the first half you are handed <code>(pure (σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)</code> and you want <code>(aAnd (fact (σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code>. Three moves: reassociate, commute the inner pair, regroup the fact.",
        "Use <code>hoare_seq</code> with intermediate assertion <code>(aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)</code>. Getting there is three <code>entails_trans</code> steps: <code>star_assoc_left</code>, then <code>star_mono_right _ (star_comm …)</code>, then <code>pure_star_regroup</code>."
      ],
      "sol": "theorem copyCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst) ((src ↦ a) ∗ (dst ↦ a)) := by\n  refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_\n  · -- the load, framed by `dst ↦ b`, then renormalised\n    have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src)\n        ((pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)) :=\n      hoare_frame (hoare_load tmp src a) (heapLocal_load tmp src)\n        (preserves_of_heapOnly _ (heapOnly_pointsTo dst b))\n    refine hoare_consequence (entails_refl _) step ?_\n    refine entails_trans (star_assoc_left _ _ _) ?_\n    refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_\n    exact pure_star_regroup _ _ _\n  · -- the write, with the value known from the pure fact, framed by `src ↦ a`\n    have step : Hoare ((aAnd (fact (fun σ => (Atom.var tmp).eval σ = a)) (dst ↦ b)) ∗ (src ↦ a))\n        (.write dst (.var tmp)) ((dst ↦ a) ∗ (src ↦ a)) :=\n      hoare_frame (hoare_write_val dst (.var tmp) b a) (heapLocal_write dst (.var tmp))\n        (preserves_of_storeStable (storeStable_write dst (.var tmp)) _)\n    exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))",
      "expl": "The intermediate assertion is the only choice, and the write dictates it: the write’s footprint is <code>dst ↦ b</code>, it has to know the value it is about to store, so the fact must be conjoined with that cell and everything else must be to the right of a <code>∗</code>. The two <code>Preserves</code> obligations go through different helpers — <code>heapOnly</code> for the load, which changes the store but not anything <code>dst ↦ b</code> can see; <code>storeStable</code> for the write, which changes no store at all.",
      "walk": [
        { "tac": "refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_",
          "h": "Two goals, <code>refine_1</code> for the load and <code>refine_2</code> for the write. Note in the trace that <code>copyCell tmp src dst</code> has already become <code>Cmd.load tmp src</code>: matching <code>?c₁ ;; ?c₂</code> unfolded the definition, so no <code>unfold copyCell</code> is wanted." },
        { "tac": "· -- the load, framed by `dst ↦ b`, then renormalised",
          "h": "The bullet focuses the first goal, and everything indented under it must close that goal before the second bullet opens." },
        { "tac": "have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src)",
          "h": "Forward reasoning: build the triple, state its type in full, match it against the goal afterwards. The type is not decoration — it is what pins down <code>hoare_frame</code>’s implicit <code>R</code>." },
        { "tac": "((pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)) :=",
          "h": "The postcondition exactly as the frame rule produces it: the load’s output with <code>dst ↦ b</code> stuck on the right. The outer brackets matter — <code>∗</code> is right-associative, so dropping them would give <code>pure … ∗ ((src ↦ a) ∗ (dst ↦ b))</code>, which the frame rule would read as framing the wrong thing." },
        { "tac": "hoare_frame (hoare_load tmp src a) (heapLocal_load tmp src)",
          "h": "The small triple and the heap-locality proof, both cited." },
        { "tac": "(preserves_of_heapOnly _ (heapOnly_pointsTo dst b))",
          "h": "A load does change the store, so <code>storeStable</code> is unavailable; the argument instead comes from the frame, which never looks at a store. The <code>_</code> is the command." },
        { "tac": "refine hoare_consequence (entails_refl _) step ?_",
          "h": "Precondition unchanged, <code>step</code> in the middle, postcondition left open. The goal changes type here, from a <code>Hoare</code> to an <code>Entails</code>: this is where the proof leaves the program logic." },
        { "tac": "refine entails_trans (star_assoc_left _ _ _) ?_",
          "h": "<code>entails_trans</code> is composition: first leg supplied, the rest a hole. <code>(P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)</code> leaves the fact alone on the left." },
        { "tac": "refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_",
          "h": "<code>star_mono_right</code> rewrites under the right factor only, so the two cells swap and the fact stays put. This is the step that brings the write’s cell to the front." },
        { "tac": "exact pure_star_regroup _ _ _",
          "h": "The glue lemma in the position it was designed for, with <code>φ := (σ tmp = a)</code>, <code>P := dst ↦ b</code>, <code>R := src ↦ a</code>." },
        { "tac": "have step : Hoare ((aAnd (fact (fun σ => (Atom.var tmp).eval σ = a)) (dst ↦ b)) ∗ (src ↦ a))",
          "h": "The fact is written <code>(Atom.var tmp).eval σ = a</code>, not <code>σ tmp = a</code>, because that is the form <code>hoare_write_val</code> produces from its <code>e</code>. The two are definitionally equal and the closing <code>exact</code> reconciles them." },
        { "tac": "hoare_frame (hoare_write_val dst (.var tmp) b a) (heapLocal_write dst (.var tmp))",
          "h": "Location, expression, old value, new value. The fourth argument is what makes the postcondition come out as <code>dst ↦ a</code> instead of a lambda." },
        { "tac": "(preserves_of_storeStable (storeStable_write dst (.var tmp)) _)",
          "h": "<code>heapOnly</code> would also work here, since the frame is a cell. <code>storeStable</code> is the better habit: it keeps working when the frame is a fact, which happens in the swap proof." },
        { "tac": "exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))",
          "h": "One commutation and both goals are closed." }
      ],
      "deep": [
        { "t": "trace",
          "title": "copyCell_spec, goal by goal",
          "start": "tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (copyCell tmp src dst) (src ↦ a ∗ dst ↦ a)",
          "steps": [
            { "tac": "refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a)",
              "h": "The first of two goals. <code>copyCell tmp src dst</code> has become <code>Cmd.load tmp src</code>, and Lean has dropped the parentheses you wrote: <code>aAnd … (dst ↦ b) ∗ src ↦ a</code> is <code>(aAnd …) ∗ (src ↦ a)</code>, since <code>∗</code> binds looser than application." },
            { "tac": "have step : … := hoare_frame (hoare_load tmp src a) …",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a)",
              "h": "Same precondition, same command; the whole remaining problem is the distance between the two postconditions." },
            { "tac": "refine hoare_consequence (entails_refl _) step ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ ((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
              "h": "The command has left the goal. What is left is the distance between two assertions, and no rule of the program logic will help close it." },
            { "tac": "refine entails_trans (star_assoc_left _ _ _) ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ (_root_.pure fun σ => σ tmp = a) ∗ src ↦ a ∗ dst ↦ b ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
              "h": "A pair of brackets vanished from the left-hand side, which is the entire step: <code>(pure ∗ src ↦ a) ∗ dst ↦ b</code> became <code>pure ∗ (src ↦ a ∗ dst ↦ b)</code>, printed bare because that is the default association." },
            { "tac": "refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_",
              "state": "case refine_1\ntmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ (_root_.pure fun σ => σ tmp = a) ∗ dst ↦ b ∗ src ↦ a ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
              "h": "The cells have swapped under the star, and what is left is <code>pure_star_regroup</code>’s statement to the letter." },
            { "tac": "exact pure_star_regroup _ _ _",
              "state": "case refine_2\ntmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp)) (src ↦ a ∗ dst ↦ a)",
              "h": "First goal closed, second on display: precondition the <code>Q</code> you chose, postcondition the chapter’s target." },
            { "tac": "have step : … := hoare_frame (hoare_write_val dst (.var tmp) b a) …",
              "state": "case refine_2\ntmp : Var\nsrc dst : Loc\na b : Val\nstep :\n  Hoare (aAnd (fact fun σ => Atom.eval σ (Atom.var tmp) = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp))\n    (dst ↦ a ∗ src ↦ a)\n⊢ Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp)) (src ↦ a ∗ dst ↦ a)",
              "h": "<code>Atom.eval σ (Atom.var tmp) = a</code> against <code>σ tmp = a</code>: not the same term, but <code>Atom.eval</code> reduces on the constructor, so <code>exact</code> takes one for the other. Only the postconditions differ, by a commutation." },
            { "tac": "exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))",
              "state": "No goals.",
              "h": "Both goals closed." }
          ],
          "done": "No goals." },
        { "t": "p",
          "h": "Nothing anywhere in the proof assumes <code>src ≠ dst</code>, and nothing has to: the precondition already implies it." },
        { "t": "code", "tag": "illustration",
          "src": "example (src dst : Loc) (a b : Val) :\n    (src ↦ a) ∗ (dst ↦ b) ⊢ fact (fun _ => src ≠ dst) :=\n  two_cells_distinct src dst a b",
          "cap": "not in the corpus. Owning two cells separately is owning two different cells." },
        { "t": "p",
          "h": "A caller with <code>src = dst</code> cannot supply the precondition, and the specification then says nothing about them — correctly, since <code>copyCell tmp l l</code> does something perfectly well defined that this triple was never about." },
        { "t": "detail", "title": "What the same theorem costs without the frame rule", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p",
              "h": "Try it: <code>intro σ h hstar</code>, destructure the star, <code>subst</code> both singleton equations, build an <code>Exec.seq</code> whose two premises need <code>union_of_some</code>, then show that <code>Heap.write (Heap.union (Heap.singleton src a) (Heap.singleton dst b)) dst a</code> splits as a union of two singletons — a <code>funext</code> and a case split on the location. The line count depends on how you route it; what does not is that every line is about heaps and none is about the program." },
            { "t": "p",
              "h": "Then add a third cell to the precondition. The framed proof does not change; the direct one changes everywhere." }
          ] }
      ],
      "pitfall": "Putting the fact in the tidier-looking place: <code>Q = pure (fun σ => σ tmp = a) ∗ ((dst ↦ b) ∗ (src ↦ a))</code>. It is unusable. <code>hoare_frame</code> then matches <code>?P ∗ ?R</code> with <code>P = pure …</code>, so you owe a triple about the write whose footprint is empty — and none exists, because <code>pure φ</code> forces the heap to be <code>Heap.empty</code> while <code>Exec.write</code> demands <code>s.heap dst = some old</code>. The fact must be <i>conjoined</i> with <code>dst ↦ b</code> under an <code>aAnd</code>. The mirror mistake is choosing the wrong one of the pair: <code>fact φ</code> holds of any heap, <code>pure φ</code> additionally demands an empty one. Left of a <code>∗</code> you need <code>pure</code>, or the fact silently claims ownership of a cut; inside the <code>aAnd</code> you need <code>fact</code>, or you are demanding that <code>dst ↦ b</code> hold of the empty heap.",
      "variants": "<b>Reverse the two commands</b> and the specification becomes false: <code>dst</code> is overwritten with whatever <code>tmp</code> held before. No particular line breaks — you simply cannot choose a <code>Q</code>, because after the write you know nothing about <code>dst</code>. <b>Use <code>hoare_write</code> instead of <code>hoare_write_val</code></b> and the second half dies with the application type mismatch shown above. <b>Drop <code>dst ↦ b</code> from the precondition</b> and the write has no cell to write to; <code>Exec.write</code> requires <code>s.heap dst = some old</code>, and since the triple is total correctness it becomes unprovable rather than merely unproved."
    },

    { "t": "sec", "s": "Program 2 · move a cell and free the source" },

    { "t": "code",
      "src": "def moveCell (tmp : Var) (src dst : Loc) : Cmd :=\n  copyCell tmp src dst ;; .free src" },

    { "t": "txt",
      "src": "  { src ↦ a ∗ dst ↦ b }\n      moveCell tmp src dst\n  { dst ↦ a }" },

    { "t": "p",
      "h": "The precondition owns two cells and the postcondition owns one. In an ordinary Hoare logic that is not expressible at all: assertions there describe a state, and “I no longer own <code>src</code>” is not a statement about the state. Here it is the difference between two <code>∗</code>-expressions." },

    { "t": "note", "kind": "info", "title": "An associativity trap that will cost you ten minutes",
      "h": "<code>;;</code> is right-associative, so <code>a ;; b ;; c</code> is <code>a ;; (b ;; c)</code>. Reusing <code>copyCell_spec</code> needs the left-nested grouping, which is why <code>moveCell</code> is defined as <code>copyCell tmp src dst ;; .free src</code> rather than as three commands in a row. The two groupings denote the same relation — that is <code>exec_seq_assoc</code>, below — but they are different <code>Cmd</code> terms." },

    { "t": "code", "tag": "illustration",
      "src": "example (tmp : Var) (src dst : Loc) :\n    moveCell tmp src dst = ((.load tmp src ;; .write dst (.var tmp)) ;; .free src) := rfl\n\nexample (tmp : Var) (src dst : Loc) :\n    (Cmd.load tmp src ;; Cmd.write dst (.var tmp) ;; Cmd.free src)\n      = (Cmd.load tmp src ;; (Cmd.write dst (.var tmp) ;; Cmd.free src)) := rfl",
      "cap": "not in the corpus. Both close by rfl, and they are the two different terms: the first is what moveCell means, the second is what writing the three commands in a row gives you." },

    { "t": "p",
      "h": "Define the program the flat way and open the proof with the natural first line, and the trap springs:" },

    { "t": "state",
      "src": "error: Application type mismatch: The argument\n  copyCell_spec tmp src dst a b\nhas type\n  Hoare (src ↦ a ∗ dst ↦ b) (copyCell tmp src dst) (src ↦ a ∗ dst ↦ a)\nbut is expected to have type\n  Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (src ↦ a ∗ dst ↦ a)\nin the application\n  hoare_seq (copyCell_spec tmp src dst a b)",
      "cap": "hoare_seq split off only the load, because the program is load ;; (write ;; free). A two-command spec has nothing to attach to." },

    {
      "t": "ex",
      "id": "m9-2",
      "name": "exec_seq_assoc",
      "hard": false,
      "why": "The escape hatch for exactly that failure: it moves a specification between the two bracketings instead of making you restructure the program or re-prove the spec.",
      "goal": "theorem exec_seq_assoc {c₁ c₂ c₃ : Cmd} {s s' : State} :\n    Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; (c₂ ;; c₃)) s s'",
      "hints": [
        "Split with <code>constructor</code> and prove the two directions independently. They are mirror images.",
        "In each direction the hypothesis is <code>Exec (something ;; something) s s'</code>. Only one constructor can produce that, so <code>cases h with | seq h₁ h₂ => …</code> gives the two halves and, silently, an intermediate state.",
        "One <code>cases</code> is not enough: afterwards one of <code>h₁</code>, <code>h₂</code> is itself a <code>seq</code>, so case on it too. Rebuild with <code>.seq</code> — the expected type tells Lean which namespace the dot means."
      ],
      "sol": "theorem exec_seq_assoc {c₁ c₂ c₃ : Cmd} {s s' : State} :\n    Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; (c₂ ;; c₃)) s s' := by\n  constructor\n  · intro h\n    cases h with | seq h₁ h₂ => cases h₁ with | seq ha hb => exact .seq ha (.seq hb h₂)\n  · intro h\n    cases h with | seq h₁ h₂ => cases h₂ with | seq ha hb => exact .seq (.seq h₁ ha) hb",
      "expl": "Sequencing is associative semantically and not syntactically, and this is the lemma that bridges the two.",
      "walk": [
        { "tac": "constructor",
          "h": "Two goals, <code>mp</code> and <code>mpr</code>, closed independently." },
        { "tac": "· intro h",
          "h": "Forward direction. The goal prints without brackets, because right-nested is the default association." },
        { "tac": "cases h with | seq h₁ h₂ => cases h₁ with | seq ha hb => exact .seq ha (.seq hb h₂)",
          "h": "Two inversions and a rebuild on one line. The first splits the run of <code>(c₁ ;; c₂) ;; c₃</code>; the second splits the first half again. The three pieces <code>ha : Exec c₁ s s'✝</code>, <code>hb : Exec c₂ s'✝ s'✝¹</code>, <code>h₂ : Exec c₃ s'✝¹ s'</code> are then reassembled the other way round." },
        { "tac": "· intro h",
          "h": "Reverse direction, opened identically." },
        { "tac": "cases h with | seq h₁ h₂ => cases h₂ with | seq ha hb => exact .seq (.seq h₁ ha) hb",
          "h": "This time the <i>second</i> component is the compound one, so you case on <code>h₂</code> and the rebuild nests to the left. The symmetry is exact, which is a good sign that no hidden condition is hiding in either direction." }
      ],
      "deep": [
        { "t": "trace",
          "title": "The forward direction, one inversion at a time",
          "start": "c₁ c₂ c₃ : Cmd\ns s' : State\n⊢ Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; c₂ ;; c₃) s s'",
          "steps": [
            { "tac": "constructor",
              "state": "case mp\nc₁ c₂ c₃ : Cmd\ns s' : State\n⊢ Exec ((c₁ ;; c₂) ;; c₃) s s' → Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "Look at how the two sides print: <code>((c₁ ;; c₂) ;; c₃)</code> keeps its brackets because they are not the default, <code>c₁ ;; c₂ ;; c₃</code> loses them. The asymmetry in the printing <i>is</i> the content of the lemma." },
            { "tac": "intro h",
              "state": "case mp\nc₁ c₂ c₃ : Cmd\ns s' : State\nh : Exec ((c₁ ;; c₂) ;; c₃) s s'\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "The whole proof is a change of shape of <code>h</code>." },
            { "tac": "cases h with | seq h₁ h₂ => …",
              "state": "case mp.seq\nc₁ c₂ c₃ : Cmd\ns s' s'✝ : State\nh₁ : Exec (c₁ ;; c₂) s s'✝\nh₂ : Exec c₃ s'✝ s'\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "One constructor can conclude a run of a <code>;;</code>, so one case. <code>s'✝</code> appeared out of nowhere and is inaccessible: the pattern named the two derivations and not the state between them." },
            { "tac": "cases h₁ with | seq ha hb => …",
              "state": "case mp.seq.seq\nc₁ c₂ c₃ : Cmd\ns s' s'✝¹ : State\nh₂ : Exec c₃ s'✝¹ s'\ns'✝ : State\nha : Exec c₁ s s'✝\nhb : Exec c₂ s'✝ s'✝¹\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
              "h": "A second inaccessible state, distinguished by a superscript. Read the three hypotheses as the chain <code>s → s'✝ → s'✝¹ → s'</code>; the goal wants it grouped as <code>c₁</code> then <code>c₂ ;; c₃</code>, and both intermediate states are inferred from the pieces." },
            { "tac": "exact .seq ha (.seq hb h₂)",
              "state": "No goals.",
              "h": "Forward direction done, in four moves." }
          ],
          "done": "No goals." },
        { "t": "p",
          "h": "What you usually want to move across the regrouping is a triple, not a derivation. That costs three lines, all of them unpacking and repacking the existential:" },
        { "t": "code", "tag": "illustration",
          "src": "example {P Q : Assertion} {c₁ c₂ c₃ : Cmd}\n    (h : Hoare P ((c₁ ;; c₂) ;; c₃) Q) : Hoare P (c₁ ;; (c₂ ;; c₃)) Q := by\n  intro σ hh hp\n  obtain ⟨s', hex, hq⟩ := h σ hh hp\n  exact ⟨s', exec_seq_assoc.mp hex, hq⟩",
          "cap": "not in the corpus. The witness state and the postcondition are reused unchanged; only the derivation is re-bracketed." },
        { "t": "p",
          "h": "And the negative half, so that “different <code>Cmd</code> terms” is a theorem and not a remark. The equation fails for <i>every</i> triple of commands, because injectivity turns it into <code>c₁ ;; c₂ = c₁</code>:" },
        { "t": "code", "tag": "illustration",
          "src": "theorem seq_ne_left (a : Cmd) : ∀ b, (a ;; b) ≠ a := by\n  induction a with\n  | seq x y ihx ihy => intro b h; injection h with p q; exact ihx y p\n  | _ => intro b h; exact Cmd.noConfusion h\n\nexample (c₁ c₂ c₃ : Cmd) : ((c₁ ;; c₂) ;; c₃) ≠ (c₁ ;; (c₂ ;; c₃)) := by\n  intro h\n  injection h with p q\n  exact seq_ne_left c₁ c₂ p",
          "cap": "not in the corpus. injection is the tactic form of constructor injectivity: from Cmd.seq A c₃ = Cmd.seq c₁ B it produces p : A = c₁ and q : c₃ = B." },
        { "t": "p",
          "h": "Two new pieces of syntax there. <code>| _ =></code> is a catch-all branch in an <code>induction</code>: seven of <code>Cmd</code>’s eight constructors need the same one-line argument, so one wildcard replaces seven identical branches. <code>Cmd.noConfusion</code> is the eliminator Lean generates for every inductive type, saying distinct constructors build distinct terms; applied to a proof of <code>Cmd.seq … = Cmd.skip</code> it yields anything at all. It is the principle <code>cases</code> uses silently when it discards impossible branches — here the impossible equation is a hypothesis rather than the thing being cased on, so you have to name it." }
      ],
      "pitfall": "Writing <code>cases h</code> without the <code>with | seq …</code> clause. It works, but the two components come back inaccessible as <code>h₁✝</code> and <code>h₂✝</code> — <code>Exec.seq</code>’s own argument names, daggered — and a daggered name cannot be written down, so the <code>exact</code> has nothing to refer to. The other slip is expecting <code>rfl</code> or <code>simp</code> to do this: the two commands are distinct constructors applied to distinct arguments, so no amount of computation identifies them. Only the semantics does.",
      "variants": "The corresponding statement for <code>Cmd</code> itself is <b>false</b>, and not merely for generic <code>c₁</code>: false for <b>every</b> <code>c₁</code>, <code>c₂</code>, <code>c₃</code>, since no term of an inductive type is a proper subterm of itself. The compiled proof is in the panel above. <b>Drop either <code>cases</code></b> and you are stuck concretely: after the first, <code>h₁ : Exec (c₁ ;; c₂) s s'✝</code> is still compound, and the rebuild needs its two halves as separate terms with nothing else in context they could come from."
    },

    {
      "t": "ex",
      "id": "m9-3",
      "name": "moveCell_spec",
      "hard": false,
      "why": "The first proof that reuses a whole specification rather than a primitive rule, which is what compositionality was supposed to buy. The postcondition also owns strictly less memory than the precondition, and the logic does that accounting on its own.",
      "goal": "theorem moveCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCell tmp src dst) (dst ↦ a)",
      "hints": [
        "<code>moveCell</code> is <code>copyCell … ;; .free src</code>, so the cut is chosen for you: it has to be <code>copyCell_spec</code>’s postcondition.",
        "The free’s footprint is <code>src ↦ a</code>, already the left factor, so nothing needs reshaping on the way in. <code>hoare_free</code>’s postcondition is <code>emp</code>, so what comes out of the frame rule is <code>emp ∗ (dst ↦ a)</code>.",
        "<code>hoare_seq</code> with <code>copyCell_spec</code>, then frame <code>dst ↦ a</code> around <code>hoare_free</code>, then <code>star_emp_left</code> to tidy."
      ],
      "sol": "theorem moveCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCell tmp src dst) (dst ↦ a) := by\n  refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_\n  have step : Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a)) :=\n    hoare_frame (hoare_free src a) (heapLocal_free src)\n      (preserves_of_storeStable (storeStable_free src) _)\n  exact hoare_consequence (entails_refl _) step (star_emp_left _)",
      "expl": "Entirely by composition, and the <code>emp ∗ (dst ↦ a) ⊢ dst ↦ a</code> at the end is what the unit laws of M4 were for. Tidying of that kind is most of what <code>hoare_consequence</code> does in practice.",
      "walk": [
        { "tac": "refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_",
          "h": "The cut is <code>copyCell_spec</code>’s postcondition, so the first argument is a term and not a hole. A two-command program has become a single citation." },
        { "tac": "have step : Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a)) :=",
          "h": "The postcondition is <code>emp ∗ (dst ↦ a)</code>, not <code>dst ↦ a</code>, because that is literally what the frame rule produces. Writing the true type here rather than the one you wish for is what makes the last line trivial." },
        { "tac": "hoare_frame (hoare_free src a) (heapLocal_free src)",
          "h": "Small rule and heap locality. <code>src ↦ a</code> is already the left factor, so the only entailment in this half is the one on the way out." },
        { "tac": "(preserves_of_storeStable (storeStable_free src) _)",
          "h": "<code>free</code> touches no store, so <code>dst ↦ a</code> survives without an argument about what it looks at. <code>preserves_of_heapOnly _ (heapOnly_pointsTo dst a)</code> also works here." },
        { "tac": "exact hoare_consequence (entails_refl _) step (star_emp_left _)",
          "h": "Precondition already matches; the postcondition is one unit law away." }
      ],
      "deep": [
        { "t": "trace",
          "title": "moveCell_spec, three states",
          "start": "tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (moveCell tmp src dst) (dst ↦ a)",
          "steps": [
            { "tac": "refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_",
              "state": "tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
              "h": "One goal, not two, since the first component came in as a term. <code>moveCell</code> unfolded and split at exactly the point where <code>copyCell_spec</code> applies — which is what the bracketing in its definition bought." },
            { "tac": "have step : … := hoare_frame (hoare_free src a) …",
              "state": "tmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (emp ∗ dst ↦ a)\n⊢ Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
              "h": "The preconditions match on the nose; the only difference is the leftover <code>emp ∗</code>." },
            { "tac": "exact hoare_consequence (entails_refl _) step (star_emp_left _)",
              "state": "No goals.",
              "h": "Done, and not one line of it mentions <code>Heap</code>." }
          ],
          "done": "No goals." },
        { "t": "p",
          "h": "One error worth reading before you produce it. Write the <code>have</code> with the postcondition you want instead of the one the rule gives:" },
        { "t": "state",
          "src": "error: Type mismatch\n  hoare_frame (hoare_free src a) (heapLocal_free src) (preserves_of_storeStable (storeStable_free src) ?m.12)\nhas type\n  Hoare (src ↦ a ∗ ?m.12) (Cmd.free src) (emp ∗ ?m.12)\nbut is expected to have type\n  Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
          "cap": "?m.12 is the frame R, still unsolved: hoare_frame never determines R by itself, the ascribed type of the have does. When that type cannot be matched, R has nothing to be solved from and Lean prints it raw." }
      ],
      "pitfall": "Stating <code>step</code> with <code>dst ↦ a</code> as its postcondition instead of <code>emp ∗ (dst ↦ a)</code>. Lean rejects the <code>have</code> itself, and the message takes a moment to read because the frame appears in it as a bare metavariable. Read the <i>has type</i> line and ignore <code>?m.12</code>: it says <code>emp ∗ ?m.12</code>, and that <code>emp</code> is <code>hoare_free</code>’s postcondition, which is not going anywhere. Write the type of a <code>have</code> as the rule produces it and do the wishful thinking afterwards, in <code>hoare_consequence</code>.",
      "variants": "<b>Ask for <code>(src ↦ ?) ∗ (dst ↦ a)</code></b> and it is unprovable: after <code>free src</code> you own nothing there, and no value makes <code>src ↦ ?</code> true of the empty heap — which is <code>pointsTo_not_emp</code>. <b>Free <code>dst</code> instead</b> and the mirror-image reshaping gives postcondition <code>src ↦ a</code>; nothing in the argument cares which cell you keep. <b>Free <code>src</code> twice</b> and the second free is unprovable, since <code>Exec.free</code> demands <code>s.heap src = some v</code> and you no longer own the cell. Double-free is not an axiom we ruled out; it is a triple we cannot prove."
    },

    { "t": "sec", "s": "swap · the store has no ∗" },

    { "t": "p",
      "h": "Swap is the first program that has to keep two pure facts alive at once, and to carry one of them past a command that writes to the store. Nothing else about it is new, and that one thing is where the store-side analogue of disjointness has to be stated." },

    { "t": "p",
      "h": "Compare the two sides. <code>l₁ ↦ a ∗ l₂ ↦ b</code> guarantees the cells are distinct, so a write to one cannot disturb the other, and you never say so. On the store there is no <code>∗</code>, no ownership and therefore no distinctness to extract: variables are shared, and the only way to know that a load does not clobber a fact is to be told the two names differ. That asymmetry is not an artefact of this encoding — it is why the logic separates the heap and not the store." },

    { "t": "p",
      "h": "So the last obligation the two helpers cannot reach is <code>Preserves (.load x l) (pure (fun σ => σ y = v))</code>: the command does change the store, and the assertion does read it. It is true when <code>y ≠ x</code>, false when <code>y = x</code>, and it is the one <code>Preserves</code> proof in the chapter that takes a hypothesis. The exercise below asks for it as <code>preserves_load_fact</code>, and then for the program." },

    { "t": "steps", "title": "The shape of the swap proof",
      "items": [
        { "k": "Four commands, three cuts",
          "h": "<code>swap</code> is right-nested, so the proof is <code>hoare_seq</code> three times, each peeling one command off the front. Four assertions are listed in the solution panel; only the first three are cuts you invent, the fourth being the postcondition you were given. Write all four down before writing any tactic." },
        { "k": "Each step is the sandwich",
          "h": "Exactly as in <code>copyCell_spec</code>. From the second command onwards the frame contains a <code>pure</code> factor as well as a cell, so you frame twice: once for the untouched cell, once for the carried fact." },
        { "k": "The two loads differ",
          "h": "The first has nothing to carry, so <code>preserves_of_heapOnly</code> suffices. The second must carry <code>pure (σ tmp₁ = a)</code> past a load into <code>tmp₂</code>, and that is the single place <code>preserves_load_fact</code> — and <code>tmp₁ ≠ tmp₂</code> — is used." },
        { "k": "The two writes are easy",
          "h": "<code>preserves_of_storeStable (storeStable_write …) _</code> discharges the obligation for any frame at all. Both writes use <code>hoare_write_val</code>, and both need <code>pure_star_regroup</code> to put the fact next to the cell being written." }
      ] },

    {
      "t": "ex",
      "id": "m9-4",
      "name": "swap_spec",
      "hard": false,
      "why": "Deliberately left for you. Everything needed is proved; the work is choosing the intermediate assertions and carrying two facts past two loads. It is also the exercise that shows what a non-trivial verification costs in this style — about ten lines per command, all of it mechanical.",
      "setup": "You state the specification yourself. It takes an extra hypothesis <code>hne : tmp₁ ≠ tmp₂</code>, and the conclusion is <code>Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap tmp₁ tmp₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a))</code>. No <code>l₁ ≠ l₂</code> is needed: the precondition implies it, by <code>two_cells_distinct</code>.",
      "goal": "def swap (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) : Cmd :=\n  .load tmp₁ l₁ ;;\n  (.load tmp₂ l₂ ;;\n   (.write l₁ (.var tmp₂) ;; .write l₂ (.var tmp₁)))\n\n-- { l₁ ↦ a ∗ l₂ ↦ b }  swap tmp₁ tmp₂ l₁ l₂  { l₁ ↦ b ∗ l₂ ↦ a }",
      "hints": [
        "Do <code>preserves_load_fact</code> first, on its own. Five tactics, and the only genuinely new content in the exercise. Open with <code>intro s s' hex hFrame hr</code>, then <code>cases hex with | load hl =></code>, and remember that <code>pure φ</code> is an <code>aAnd</code>, so both the hypothesis and the goal split in two.",
        "For the program: three nested <code>hoare_seq</code>s, because <code>swap</code> is right-nested. Peel one command at a time and never look at more than one command’s worth of assertion.",
        "From the second command onwards you frame twice. Build the inner triple — command plus untouched cell — as one <code>have</code>, then frame the carried fact around <i>that</i> as a second <code>have</code>. Since the frame rule always puts the frame on the right and the layout keeps the fact on the left, each of those two steps is bracketed by a <code>star_comm</code>.",
        "The statement of the extra lemma: <code>preserves_load_fact {x y : Var} {v : Val} (l : Loc) (hne : y ≠ x) : Preserves (.load x l) (pure (fun σ => σ y = v))</code>. Note the order of the disequality — <code>x</code> is the variable being loaded into."
      ],
      "sol": "theorem preserves_load_fact {x y : Var} {v : Val} (l : Loc) (hne : y ≠ x) :\n    Preserves (.load x l) (pure (fun σ => σ y = v)) := by\n  intro s s' hex hFrame hr\n  cases hex with\n  | load hl =>\n      obtain ⟨hy, he⟩ := hr\n      refine ⟨?_, he⟩\n      show Store.set s.store x _ y = v\n      simp [Store.set, hne]\n      exact hy\n\n-- The remaining work: four applications of hoare_seq, each of the form\n--   frame the untouched cell  →  apply the small rule  →  renormalise.\n-- The intermediate assertions, in order:\n--   pure (tmp₁ = a) ∗ (l₁ ↦ a ∗ l₂ ↦ b)\n--   pure (tmp₁ = a) ∗ (pure (tmp₂ = b) ∗ (l₁ ↦ a ∗ l₂ ↦ b))\n--   pure (tmp₁ = a) ∗ (l₁ ↦ b ∗ l₂ ↦ b)\n--   l₁ ↦ b ∗ l₂ ↦ a",
      "expl": "<code>preserves_load_fact</code> is where <code>tmp₁ ≠ tmp₂</code> is consumed: the load overwrites <code>tmp₂</code> and the framed fact talks about <code>tmp₁</code>, so the two must be different variables. Everything after it is the loop you already ran twice.",
      "walk": [
        { "tac": "intro s s' hex hFrame hr",
          "h": "Five <code>intro</code>s reach the conclusion. Note the order in <code>Preserves</code>: the frame heap comes <i>after</i> the execution." },
        { "tac": "cases hex with",
          "h": "Invert. Only <code>Exec.load</code> can conclude a run of <code>.load x l</code>, so there is one case — and the point of doing it is that <code>s'</code> is replaced by the concrete state <code>⟨Store.set s.store x v✝, s.heap⟩</code>." },
        { "tac": "| load hl =>",
          "h": "Names the side condition <code>hl : s.heap l = some v✝</code>, which you will not use: whether the load succeeded is irrelevant to whether a fact about a different variable survives. The <code>with</code> syntax requires the name anyway." },
        { "tac": "obtain ⟨hy, he⟩ := hr",
          "h": "<code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so the hypothesis splits into the fact and the emptiness. The emptiness is about <code>hFrame</code>, which the command cannot reach." },
        { "tac": "refine ⟨?_, he⟩",
          "h": "The goal is also a <code>pure</code>, so also a conjunction. Hand back the second component at once and leave the interesting half open." },
        { "tac": "show Store.set s.store x _ y = v",
          "h": "The goal is <code>fact (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame</code>, which is unreadable and, worse, not in a shape <code>simp</code> will attack. <code>show</code> restates it as the equation it definitionally is. The <code>_</code> is the loaded value, which is inaccessible, so you let Lean supply it." },
        { "tac": "simp [Store.set, hne]",
          "h": "<b>The whole content of the lemma.</b> <code>Store.set</code> unfolds to <code>if y = x then v✝ else s.store y</code>, <code>hne</code> decides the condition, the <code>if</code> collapses to the else branch, and the goal becomes <code>s.store y = v</code>. Delete <code>hne</code> from the bracket and it does not close." },
        { "tac": "exact hy",
          "h": "<code>hy : fact (fun σ => σ y = v) s.store hFrame</code> unfolds to exactly that equation." },
        { "tac": "-- The remaining work: four applications of hoare_seq …",
          "h": "The rest of the exercise. Every step has the shape you used twice in <code>copyCell_spec</code>." },
        { "tac": "--   pure (tmp₁ = a) ∗ (l₁ ↦ a ∗ l₂ ↦ b)",
          "h": "After the first load: <code>hoare_load tmp₁ l₁ a</code> framed by <code>l₂ ↦ b</code>, then one <code>star_assoc_left</code>. The fact stays on the far left throughout — that is the invariant of the whole layout." },
        { "tac": "--   pure (tmp₁ = a) ∗ (pure (tmp₂ = b) ∗ (l₁ ↦ a ∗ l₂ ↦ b))",
          "h": "After the second load, with two facts alive. Getting here needs the inner load framed by <code>l₁ ↦ a</code>, and then that whole triple framed by <code>pure (tmp₁ = a)</code> — which is where <code>preserves_load_fact l₂ hne</code> goes." },
        { "tac": "--   pure (tmp₁ = a) ∗ (l₁ ↦ b ∗ l₂ ↦ b)",
          "h": "After the first write, <code>pure (tmp₂ = b)</code> has been consumed: <code>pure_star_regroup</code> turned it into the <code>aAnd</code> that <code>hoare_write_val l₁ (.var tmp₂) a b</code> demands, and the rule ate it. A fact is used up exactly when the value it describes is stored." },
        { "tac": "--   l₁ ↦ b ∗ l₂ ↦ a",
          "h": "After the second write, the same happens to <code>pure (tmp₁ = a)</code> and nothing is left over. A verification ending with a leftover <code>pure</code> usually means you framed something you should have used." }
      ],
      "deep": [
        { "t": "trace",
          "title": "preserves_load_fact, tactic by tactic",
          "start": "x y : Var\nv : Val\nl : Loc\nhne : y ≠ x\n⊢ Preserves (Cmd.load x l) (_root_.pure fun σ => σ y = v)",
          "steps": [
            { "tac": "intro s s' hex hFrame hr",
              "state": "x y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns s' : State\nhex : Exec (Cmd.load x l) s s'\nhFrame : Heap\nhr : _root_.pure (fun σ => σ y = v) s.store hFrame\n⊢ _root_.pure (fun σ => σ y = v) s'.store hFrame",
              "h": "Hypothesis and goal are the same assertion at two different stores. Everything that follows is about the relation between those two stores." },
            { "tac": "cases hex with | load hl =>",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nhr : _root_.pure (fun σ => σ y = v) s.store hFrame\nv✝ : Val\nhl : s.heap l = some v✝\n⊢ _root_.pure (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame",
              "h": "<code>s'</code> is gone, replaced by the state <code>Exec.load</code> produces. The loaded value <code>v✝</code> is inaccessible, which is why the <code>show</code> two steps later has to write <code>_</code> in its place." },
            { "tac": "obtain ⟨hy, he⟩ := hr",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ _root_.pure (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame",
              "h": "The two halves of <code>pure</code>. <code>he</code> says <code>hFrame = Heap.empty</code> and survives untouched, since the command changes the store and not the frame heap." },
            { "tac": "refine ⟨?_, he⟩",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ fact (fun σ => σ y = v) { store := s.store.set x v✝, heap := s.heap }.store hFrame",
              "h": "<code>he</code> is reused verbatim: <code>emp</code> ignores its store argument, so one proof serves at both stores." },
            { "tac": "show Store.set s.store x _ y = v",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ s.store.set x v✝ y = v",
              "h": "Three unfoldings at once — <code>fact</code>, the structure projection, the application — and the goal is a plain equation about stores. Nothing was proved; the goal became legible and, more to the point, became a shape <code>simp [Store.set]</code> can attack." },
            { "tac": "simp [Store.set, hne]",
              "state": "case load\nx y : Var\nv : Val\nl : Loc\nhne : y ≠ x\ns : State\nhFrame : Heap\nv✝ : Val\nhl : s.heap l = some v✝\nhy : fact (fun σ => σ y = v) s.store hFrame\nhe : emp s.store hFrame\n⊢ s.store y = v",
              "h": "Drop <code>hne</code> from the bracket and <code>simp [Store.set]</code> unfolds the definition and stops, leaving <code>⊢ (if y = x then v✝ else s.store y) = v</code> — unprovable, since for <code>y = x</code> it is false." },
            { "tac": "exact hy",
              "state": "No goals.",
              "h": "Definitional unfolding, not a rewrite." }
          ],
          "done": "No goals." },
        { "t": "p",
          "h": "Here is the top of the program proof, so you can see the layout those intermediate assertions describe. The two goals after the first <code>hoare_seq</code>:" },
        { "t": "state",
          "src": "case refine_1\ntmp₁ tmp₂ : Var\nl₁ l₂ : Loc\na b : Val\nhne : tmp₁ ≠ tmp₂\n⊢ Hoare (l₁ ↦ a ∗ l₂ ↦ b) (Cmd.load tmp₁ l₁) ((_root_.pure fun σ => σ tmp₁ = a) ∗ l₁ ↦ a ∗ l₂ ↦ b)\n\ncase refine_2\ntmp₁ tmp₂ : Var\nl₁ l₂ : Loc\na b : Val\nhne : tmp₁ ≠ tmp₂\n⊢ Hoare ((_root_.pure fun σ => σ tmp₁ = a) ∗ l₁ ↦ a ∗ l₂ ↦ b)\n    (Cmd.load tmp₂ l₂ ;; Cmd.write l₁ (Atom.var tmp₂) ;; Cmd.write l₂ (Atom.var tmp₁)) (l₁ ↦ b ∗ l₂ ↦ a)",
          "cap": "One command, then the rest of the program with the first cut as its precondition. Recurse." },
        { "t": "detail", "title": "Breaking tmp₁ ≠ tmp₂ — the aliased run, mechanised", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p",
              "h": "Take <code>tmp₁ = tmp₂ = 0</code>, <code>l₁ = 0</code>, <code>l₂ = 1</code>, <code>a = 1</code>, <code>b = 2</code>. The second load clobbers the variable the first load filled, so at the writes both <code>.var tmp₁</code> and <code>.var tmp₂</code> evaluate to <code>2</code> and the run ends with both cells holding <code>2</code>. Quantified over all variables, the specification has no proof at all:" },
            { "t": "code", "tag": "illustration",
              "src": "example : ¬ ∀ (t₁ t₂ : Var) (l₁ l₂ : Loc) (a b : Val),\n    Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap t₁ t₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a)) := by\n  intro H\n  have hpre : ((0 ↦ 1) ∗ (1 ↦ 2)) (fun _ => 0)\n      (Heap.union (Heap.singleton 0 1) (Heap.singleton 1 2)) :=\n    ⟨Heap.singleton 0 1, Heap.singleton 1 2, singleton_disjoint 1 2 (by decide), rfl, rfl, rfl⟩\n  obtain ⟨s', hex, hq⟩ := H 0 0 0 1 1 2 _ _ hpre\n  rw [swap] at hex\n  cases hex with | seq hA hB =>\n  cases hA with | load hl1 =>\n  cases hB with | seq hC hD =>\n  cases hC with | load hl2 =>\n  cases hD with | seq hE hF =>\n  cases hE with | write _ =>\n  cases hF with | write _ =>\n  obtain ⟨ha, hb, -, hu, hea, heb⟩ := hq\n  subst hea; subst heb\n  have h1 := congrFun hu 1\n  simp [Heap.union, Heap.singleton, Heap.write, Store.set, Atom.eval] at h1 hl2\n  exact absurd (hl2.trans h1) (by decide)",
              "cap": "not in the corpus — compiles against prelude/m9.lean together with the def of swap from the exercise statement." },
            { "t": "p",
              "h": "Read the shape, because refuting a triple always looks like this. You supply a concrete <code>σ</code> and <code>h</code> satisfying <code>P</code>, take the <code>s'</code> the triple promises, and then pin <code>s'</code> down by inverting the program one command at a time. The seven <code>cases</code> are that pinning; by the end <code>hq</code> is a statement about a heap you can evaluate. The last three lines evaluate it at location <code>1</code>, where the postcondition demands <code>some 1</code> and the run delivers <code>some 2</code>." },
            { "t": "p",
              "h": "Note which hypotheses collide. <code>hl2</code> is the second load’s side condition, <code>h1</code> is the postcondition read off at location <code>1</code>, and after <code>simp</code> they say <code>2 = v✝</code> and <code>v✝ = 1</code>. The aliasing never appears as an error; it appears as an arithmetic contradiction three commands later. Which is the argument for stating the side condition up front, where it is one hypothesis, rather than meeting it here, where it is a counterexample." },
            { "t": "dl",
              "items": [
                { "k": "rw [swap] at hex",
                  "h": "The equation lemma of a <code>def</code>, used as a rewrite: <code>swap 0 0 0 1</code> becomes its body. Needed because <code>cases</code> reads the head symbol of <code>hex</code>’s type, and until this line that head is <code>swap</code>, not <code>;;</code> — no constructor to case on." },
                { "k": "⟨ha, hb, -, hu, hea, heb⟩",
                  "h": "The <code>-</code> means “this component exists, name it nothing, discard it”. Here it drops the disjointness proof. <code>_</code> would keep it in the context under an inaccessible name; <code>-</code> clears it out." },
                { "k": "by decide",
                  "h": "A proof by evaluation, for a decidable proposition with no free variables — here <code>(1 : Loc) ≠ 2</code> and <code>¬ (2 = 1)</code>. It runs the <code>Decidable</code> instance and checks the answer is <code>true</code>. Not <code>simp</code>, not <code>rfl</code>, and it fails — sometimes very slowly — on anything containing a variable." },
                { "k": "congrFun hu 1",
                  "h": "<code>hu</code> is an equation between two heaps, so between two functions; applying both sides at location <code>1</code> turns it into an equation between two <code>Option Val</code>s that <code>simp</code> can evaluate. The standard way down from a heap equation to a fact about one cell." }
              ] }
          ] },
        { "t": "detail", "title": "The complete proof — open it after you have written your own", "tag": "spoiler", "open": false,
          "blocks": [
            { "t": "p",
              "h": "Around forty lines, of which the only real choices are the three <code>Q</code>s." },
            { "t": "code", "tag": "illustration",
              "src": "theorem swap_spec (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) (a b : Val) (hne : tmp₁ ≠ tmp₂) :\n    Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap tmp₁ tmp₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a)) := by\n  refine hoare_seq (Q := pure (fun σ => σ tmp₁ = a) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b))) ?_ ?_\n  · -- load tmp₁ l₁, framed by l₂ ↦ b\n    have step : Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (.load tmp₁ l₁)\n        ((pure (fun σ => σ tmp₁ = a) ∗ (l₁ ↦ a)) ∗ (l₂ ↦ b)) :=\n      hoare_frame (hoare_load tmp₁ l₁ a) (heapLocal_load tmp₁ l₁)\n        (preserves_of_heapOnly _ (heapOnly_pointsTo l₂ b))\n    exact hoare_consequence (entails_refl _) step (star_assoc_left _ _ _)\n  refine hoare_seq (Q := pure (fun σ => σ tmp₁ = a) ∗\n      (pure (fun σ => σ tmp₂ = b) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b)))) ?_ ?_\n  · -- load tmp₂ l₂, framed by l₁ ↦ a inside and by the pure fact outside\n    have inner : Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (.load tmp₂ l₂)\n        (pure (fun σ => σ tmp₂ = b) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b))) := by\n      have base : Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.load tmp₂ l₂)\n          ((pure (fun σ => σ tmp₂ = b) ∗ (l₂ ↦ b)) ∗ (l₁ ↦ a)) :=\n        hoare_frame (hoare_load tmp₂ l₂ b) (heapLocal_load tmp₂ l₂)\n          (preserves_of_heapOnly _ (heapOnly_pointsTo l₁ a))\n      refine hoare_consequence (star_comm _ _) base ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (star_comm _ _)\n    have framed : Hoare (((l₁ ↦ a) ∗ (l₂ ↦ b)) ∗ pure (fun σ => σ tmp₁ = a)) (.load tmp₂ l₂)\n        ((pure (fun σ => σ tmp₂ = b) ∗ ((l₁ ↦ a) ∗ (l₂ ↦ b))) ∗ pure (fun σ => σ tmp₁ = a)) :=\n      hoare_frame inner (heapLocal_load tmp₂ l₂) (preserves_load_fact l₂ hne)\n    exact hoare_consequence (star_comm _ _) framed (star_comm _ _)\n  refine hoare_seq (Q := pure (fun σ => σ tmp₁ = a) ∗ ((l₁ ↦ b) ∗ (l₂ ↦ b))) ?_ ?_\n  · -- write l₁ (.var tmp₂), framed by l₂ ↦ b inside and by the pure fact outside\n    have inner : Hoare ((aAnd (fact (fun σ => σ tmp₂ = b)) (l₁ ↦ a)) ∗ (l₂ ↦ b))\n        (.write l₁ (.var tmp₂)) ((l₁ ↦ b) ∗ (l₂ ↦ b)) :=\n      hoare_frame (hoare_write_val l₁ (.var tmp₂) a b) (heapLocal_write l₁ (.var tmp₂))\n        (preserves_of_storeStable (storeStable_write l₁ (.var tmp₂)) _)\n    have framed : Hoare (((aAnd (fact (fun σ => σ tmp₂ = b)) (l₁ ↦ a)) ∗ (l₂ ↦ b))\n          ∗ pure (fun σ => σ tmp₁ = a))\n        (.write l₁ (.var tmp₂)) (((l₁ ↦ b) ∗ (l₂ ↦ b)) ∗ pure (fun σ => σ tmp₁ = a)) :=\n      hoare_frame inner (heapLocal_write l₁ (.var tmp₂))\n        (preserves_of_storeStable (storeStable_write l₁ (.var tmp₂)) _)\n    refine hoare_consequence ?_ framed (star_comm _ _)\n    refine entails_trans (star_comm _ _) ?_\n    exact star_mono_left _ (pure_star_regroup _ _ _)\n  · -- write l₂ (.var tmp₁), framed by l₁ ↦ b\n    have step : Hoare ((aAnd (fact (fun σ => σ tmp₁ = a)) (l₂ ↦ b)) ∗ (l₁ ↦ b))\n        (.write l₂ (.var tmp₁)) ((l₂ ↦ a) ∗ (l₁ ↦ b)) :=\n      hoare_frame (hoare_write_val l₂ (.var tmp₁) b a) (heapLocal_write l₂ (.var tmp₁))\n        (preserves_of_storeStable (storeStable_write l₂ (.var tmp₁)) _)\n    refine hoare_consequence ?_ step (star_comm _ _)\n    refine entails_trans (star_mono_right _ (star_comm _ _)) ?_\n    exact pure_star_regroup _ _ _",
              "cap": "not in the corpus — one solution among many, compiled against prelude/m9.lean with the def of swap from the exercise statement." },
            { "t": "p",
              "h": "Two things to extract. The double framing in the middle two steps is forced: <code>hoare_frame</code> takes one frame at a time and always puts it on the right, so <code>inner</code> handles the command with its untouched cell and <code>framed</code> wraps the carried fact around the whole of <code>inner</code>. And every <code>hoare_consequence</code> in the proof contains a <code>star_comm</code> somewhere — the tax for keeping facts on the left while the frame rule insists on the right. The opposite convention moves the commutations around without removing them." }
          ] }
      ],
      "pitfall": "Writing the disequality the wrong way round. <code>preserves_load_fact</code> demands <code>hne : y ≠ x</code>, with <code>x</code> the variable loaded into and <code>y</code> the one the fact is about. In the swap proof you load into <code>tmp₂</code> and carry a fact about <code>tmp₁</code>, so <code>tmp₁ ≠ tmp₂</code> is what fits — by luck, not by design. Hand it <code>x ≠ y</code> and <code>simp [Store.set, hne]</code> stops working: <code>simp</code> orients the hypothesis into the rewrite <code>(x = y) = False</code>, the condition in the goal is <code>y = x</code>, the two do not match, and the <code>if</code> is never resolved. Lean says so twice — the goal is left as <code>⊢ (if y = x then v✝ else s.store y) = v</code>, and the linter adds <code>This simp argument is unused: hne</code>. The fix is <code>hne.symm</code>, not a different proof.",
      "variants": "<b>Drop <code>hne</code></b> and the theorem is false, not merely unprovable; the aside above compiles the counterexample. With <code>tmp₁ = tmp₂</code> the second load overwrites the variable the first fact was about, so afterwards <code>σ tmp₁ = b</code>; the first write stores <code>b</code> into <code>l₁</code>, correct by accident, and the second stores <code>b</code> into <code>l₂</code> as well. Inside the proof the single point of failure is <code>simp [Store.set, hne]</code>: with <code>y = x</code> the <code>if</code> takes the then branch and the surviving fact is about the newly loaded value. <b>Interleave the loads and writes</b> and the same collision appears on the heap side: writing <code>l₁</code> before reading <code>l₂</code> is safe here only because the cells are distinct, which <code>two_cells_distinct</code> gives you, but a program that wrote and then read the <i>same</i> cell would need <code>hoare_write_val</code>’s value tracking pointing the other way. <b>Replace <code>Preserves</code> by a syntactic side condition</b> and this exercise still works, but every command that modifies a variable and re-establishes the fact anyway is lost — the <code>x := x</code> witness near the top of the chapter is one."
    },

    { "t": "sec", "s": "What carries forward" },

    { "t": "p",
      "h": "Every precondition in this chapter is a <code>∗</code> of finitely many named cells, written out in full, and every reshaping lemma is a finite rearrangement of that chain. That is the boundary. A program that walks a linked structure has a footprint whose length is not known when you write the proof, so there is no chain to rearrange and nothing to move into leftmost position — and no lemma in scope peels the head cell off an assertion of unknown length. Until there is one, the specification cannot even be stated. <code>listRep</code> and <code>lseg</code> are those assertions, and the lemma that unfolds one of them by a single cell is what M10 must build before the sandwich can fire again." },

    { "t": "p",
      "h": "If the reshaping felt tedious, that is the correct reaction, and it is the motivation for M12: a weakest-precondition calculus computes the intermediate assertions instead of asking you to invent them. It is justified by the rules you have just used by hand, so the tedium was the specification of the tool." },

    { "t": "dod",
      "h": "You can verify small heap-manipulating programs compositionally, without unfolding <code>Exec</code> outside of the primitive rules." }
  ]
});
