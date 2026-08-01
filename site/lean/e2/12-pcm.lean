/- ===== Unit 10 · `pcm` · The partial commutative monoid ===== -/

/- ex m2-5 union_assoc -/
theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by
  funext l
  cases hl : h₁ l with
  | none =>
      rw [union_of_none (Heap.union h₂ h₃) hl]
      cases hl2 : h₂ l with
      | none =>
          rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]
      | some v =>
          have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2
          rw [union_of_some h₃ hu, union_of_some h₃ hl2]
  | some v =>
      rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]

/- ex m2-6 union_comm -/
theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext l
  rcases hd l with h | h
  · rw [union_of_none h₂ h]
    cases hl : h₂ l with
    | none   => rw [union_of_none h₁ hl, h]
    | some v => rw [union_of_some h₁ hl]
  · rw [union_of_none h₁ h]
    cases hl : h₁ l with
    | none   => rw [union_of_none h₂ hl]; exact h
    | some v => rw [union_of_some h₂ hl]

/- ex m2-7 disjoint_union_left / disjoint_union_right -/
theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :
    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by
  constructor
  · intro hd
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rcases hd l with h | h
      · exact Or.inl (union_eq_none.mp h).1
      · exact Or.inr h
    · rcases hd l with h | h
      · exact Or.inl (union_eq_none.mp h).2
      · exact Or.inr h
  · intro ⟨ha, hb⟩ l
    rcases ha l with h | h
    · rcases hb l with h' | h'
      · exact Or.inl (union_eq_none.mpr ⟨h, h'⟩)
      · exact Or.inr h'
    · exact Or.inr h

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} :
    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃ := by
  constructor
  · intro hd
    have h' := disjoint_union_left.mp (disjoint_symm hd)
    exact ⟨disjoint_symm h'.1, disjoint_symm h'.2⟩
  · intro ⟨ha, hb⟩
    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)

structure PCM (M : Type) where
  op         : M → M → M
  unit       : M
  valid      : M → M → Prop
  op_comm    : ∀ a b, valid a b → op a b = op b a
  op_assoc   : ∀ a b c, op (op a b) c = op a (op b c)
  unit_left  : ∀ a, op unit a = a
  valid_unit : ∀ a, valid unit a
  valid_comm : ∀ a b, valid a b → valid b a

/- ex x23 heapPCM -/
def heapPCM : PCM Heap where
  op         := Heap.union
  unit       := Heap.empty
  valid      := Heap.disjoint
  op_comm    := fun _ _ hd => union_comm hd
  op_assoc   := union_assoc
  unit_left  := union_empty_left
  valid_unit := disjoint_empty_left
  valid_comm := fun _ _ hd => disjoint_symm hd

/- ex x24 union_cancel_left -/
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
