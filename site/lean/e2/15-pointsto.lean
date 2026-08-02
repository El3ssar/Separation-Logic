/- ===== Unit 13 · `pointsto` · `emp`, `↦`, and exact ownership ===== -/

def emp : Assertion := fun _ h => h = Heap.empty

def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v
infix:60 " ↦ " => pointsTo

/- ex m3-1 pointsTo_value_unique / pointsTo_not_emp -/
theorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :
    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂) := by
  intro σ h ⟨h1, h2⟩
  have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]
  rw [singleton_same, singleton_same] at this
  exact Option.some.inj this

theorem pointsTo_not_emp (l : Loc) (v : Val) :
    ¬ ((l ↦ v) ⊢ emp) := by
  intro hcontra
  have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl
  have : Heap.singleton l v l = Heap.empty l := by rw [h]
  rw [singleton_same] at this
  exact absurd this (by simp [Heap.empty])

/- ex x30 emp as nothing anywhere -/
theorem emp_iff_all_none : emp ⊣⊢ fun _ h => ∀ l, h l = none := by
  constructor
  · intro σ h hp l
    rw [hp]
    simp [Heap.empty]
  · intro σ h hp
    funext l
    simp [Heap.empty, hp l]
