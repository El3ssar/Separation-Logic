/- Edition 2 · new Lean checked against site/lean/prelude/m2.lean -/

theorem self_disjoint_iff_empty (h : Heap) : Heap.disjoint h h ↔ h = Heap.empty := by
  constructor
  · intro hd
    funext l
    rcases hd l with h1 | h1 <;> exact h1
  · intro he l
    subst he
    exact Or.inl rfl

theorem union_self (h : Heap) : Heap.union h h = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none h hl]; exact hl
  | some v => rw [union_of_some h hl]

theorem union_cancel_left {h₁ h₂ h₃ : Heap}
    (hd₂ : Heap.disjoint h₁ h₂) (hd₃ : Heap.disjoint h₁ h₃)
    (he : Heap.union h₁ h₂ = Heap.union h₁ h₃) : h₂ = h₃ := by
  funext l
  have hl := congrFun he l
  cases h1 : h₁ l with
  | none => rw [union_of_none h₂ h1, union_of_none h₃ h1] at hl; exact hl
  | some v =>
      rcases hd₂ l with e | e
      · rw [h1] at e; exact absurd e (by simp)
      · rcases hd₃ l with e' | e'
        · rw [h1] at e'; exact absurd e' (by simp)
        · rw [e, e']
