/- ===== Unit 26 · `local-compose` · Locality composes ===== -/

/- ex m8-4 heapLocal_seq -/
theorem heapLocal_seq {c₁ c₂ : Cmd} (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) :
    HeapLocal (c₁ ;; c₂) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | seq hex₁ hex₂ =>
      rename_i sMid
      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁
      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂
      refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩
      have heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩ := by
        rw [← hst₁, ← hhp₁]
      rw [heq]
      exact hr₂

/- ex x52 heapLocal_ite -/
theorem heapLocal_ite {b : BExpr} {c₁ c₂ : Cmd}
    (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) : HeapLocal (.ite b c₁ c₂) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | iteTrue hb hex' =>
      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₁ σ h hFrame s' hd hex'
      exact ⟨hdEnd, r, Exec.iteTrue hb hr, hst, hhp⟩
  | iteFalse hb hex' =>
      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₂ σ h hFrame s' hd hex'
      exact ⟨hdEnd, r, Exec.iteFalse hb hr, hst, hhp⟩

/- ex x53 heapLocal_loop -/
theorem heapLocal_loop_aux {b₀ : BExpr} {c₀ : Cmd} (hc : HeapLocal c₀) :
    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →
      ∀ hFrame, Heap.disjoint s.heap hFrame →
        Heap.disjoint s'.heap hFrame ∧
        ∃ r : State, Exec (.loop b₀ c₀) ⟨s.store, Heap.union s.heap hFrame⟩ r ∧
          r.store = s'.store ∧ r.heap = Heap.union s'.heap hFrame := by
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
      intro heq hFrame hd
      cases heq
      exact ⟨hd, _, Exec.loopFalse hb, rfl, rfl⟩
  | loopTrue hb hbody _ _ ihrest =>
      intro heq hFrame hd
      cases heq
      rename_i s s' s'' _ _
      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := hc s.store s.heap hFrame s' hd hbody
      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := ihrest rfl hFrame hdMid
      have heq2 : r₁ = ⟨s'.store, Heap.union s'.heap hFrame⟩ := by
        rw [← hst₁, ← hhp₁]
      refine ⟨hdEnd, r₂, Exec.loopTrue (s' := r₁) hb hr₁ ?_, hst₂, hhp₂⟩
      rw [heq2]
      exact hr₂

theorem heapLocal_loop {b : BExpr} {c : Cmd} (hc : HeapLocal c) :
    HeapLocal (.loop b c) := by
  intro σ h hFrame s' hd hex
  exact heapLocal_loop_aux hc hex rfl hFrame hd
