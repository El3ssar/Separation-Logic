/- ===== Unit 19 · `exec` · Running a command is a relation ===== -/

inductive Exec : Cmd → State → State → Prop where
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
      Exec (.loop b c) s s''

/- ex m5-1 exec_skip_inv -/
theorem exec_skip_inv {s s' : State} (h : Exec .skip s s') : s' = s := by
  cases h; rfl

/- ex x42 exec_assign_inv / exec_load_inv -/
theorem exec_assign_inv {x : Var} {e : Atom} {s s' : State} (h : Exec (.assign x e) s s') :
    s' = ⟨Store.set s.store x (e.eval s.store), s.heap⟩ := by
  cases h; rfl

theorem exec_load_inv {x : Var} {l : Loc} {s s' : State} (h : Exec (.load x l) s s') :
    ∃ v, s.heap l = some v ∧ s' = ⟨Store.set s.store x v, s.heap⟩ := by
  cases h with
  | load hl => exact ⟨_, hl, rfl⟩

/- ex x43 exec_load_stuck -/
theorem exec_load_stuck (x : Var) (l : Loc) (σ : Store) (s' : State) :
    ¬ Exec (.load x l) ⟨σ, Heap.empty⟩ s' := by
  intro hex
  cases hex with
  | load hl => exact absurd hl (by simp [Heap.empty])

/- ex x44 exec_skip_seq_inv -/
theorem exec_skip_seq_inv {c : Cmd} {s s' : State} (h : Exec (.skip ;; c) s s') : Exec c s s' := by
  cases h with
  | seq h₁ h₂ => cases h₁; exact h₂
