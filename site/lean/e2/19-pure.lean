/- ===== Unit 17 · `pure` · Propositions inside a `∗`, and the toolkit ===== -/

def pure (φ : Store → Prop) : Assertion := aAnd (fact φ) emp

/- ex m4-7 two_cells_distinct -/
theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :
    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact (singleton_disjoint_iff v₁ v₂).mp hd

/- ex m4-8 star_swap_middle / star_rotate_left / star_rotate_right / star_pure_left / star_pure_right -/
theorem star_swap_middle (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) :=
  entails_trans (star_assoc_right P Q R)
    (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))

theorem star_rotate_left (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R :=
  star_assoc_right P Q R

theorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) :=
  star_assoc_left P Q R

theorem star_pure_left (φ : Store → Prop) (P : Assertion) :
    pure φ ∗ P ⊢ aAnd (fact φ) P := by
  intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩
  subst he
  rw [hu, union_empty_left]
  exact ⟨hφ, hp⟩

theorem star_pure_right (φ : Store → Prop) (P : Assertion) :
    aAnd (fact φ) P ⊢ pure φ ∗ P := by
  intro σ h ⟨hφ, hp⟩
  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩

/- ex x38 star_or_right / star_exists_right -/
theorem star_or_right (P Q R : Assertion) : aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by
  intro σ h hor
  rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inl hp, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inr hq, hr⟩

theorem star_exists_right {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aExists (fun x => P x ∗ Q) ⊢ aExists P ∗ Q := by
  intro σ h ⟨x, h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩
