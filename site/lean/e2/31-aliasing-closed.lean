/- ===== Unit 28 · `aliasing-closed` · The opening question, closed ===== -/

/- ex x55 classical_conjunction_rule_is_false -/
theorem classical_conjunction_rule_is_false :
    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),
        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))
              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))) := by
  intro hall
  obtain ⟨s', hex, h3, h5⟩ :=
    hall 0 0 3 5 (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)
  cases hex with
  | write hl =>
      have e3 : Heap.write (Heap.singleton 0 3) 0 5 0 = some 3 := h3
      rw [write_same] at e3
      exact absurd e3 (by simp)

/- ex x56 separated_write_ok -/
theorem separated_write_ok (l₁ l₂ : Loc) (a b : Val) :
    Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.write l₂ (.const 5)) ((l₂ ↦ 5) ∗ (l₁ ↦ a)) := by
  have base : Hoare (l₂ ↦ b) (.write l₂ (.const 5)) (l₂ ↦ 5) :=
    hoare_write l₂ (.const 5) b
  exact hoare_frame base (heapLocal_write l₂ (.const 5))
    (preserves_of_heapOnly _ (heapOnly_pointsTo l₁ a))
