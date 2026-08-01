/- ===== Unit 14 · `star` · Separating conjunction, and what it cannot do ===== -/

def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂
infixr:55 " ∗ " => star

/- ex x31 star_intro -/
theorem star_intro {P Q : Assertion} {σ : Store} {h h₁ h₂ : Heap}
    (hd : Heap.disjoint h₁ h₂) (hu : h = Heap.union h₁ h₂)
    (hp : P σ h₁) (hq : Q σ h₂) : (P ∗ Q) σ h :=
  ⟨h₁, h₂, hd, hu, hp, hq⟩

/- ex x32 star_same_loc_absurd -/
theorem star_same_loc_absurd (l : Loc) (v₁ v₂ : Val) :
    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact ((singleton_disjoint_iff v₁ v₂).mp hd) rfl

theorem star_pointsTo_same_false (l : Loc) (v₁ v₂ : Val) :
    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact absurd ((singleton_disjoint_iff v₁ v₂).mp hd) (by simp)

/- ex x33 no_star_weakening -/
theorem no_star_weakening : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)) := by
  intro hall
  have h := hall (fun _ => 0) (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7))
    ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl, rfl⟩
  have h1 := congrFun h 1
  rw [union_of_none (Heap.singleton 1 7) (singleton_other 0 1 4 (by simp)),
      singleton_same, singleton_other 0 1 4 (by simp)] at h1
  exact absurd h1 (by simp)

/- ex x34 no_star_duplication -/
theorem no_star_duplication : ¬ (∀ P : Assertion, P ⊢ P ∗ P) := by
  intro hall
  obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hall (4 ↦ 7) (fun _ => 0) (Heap.singleton 4 7) rfl
  have e1 : h₁ = Heap.singleton 4 7 := hp
  have e2 : h₂ = Heap.singleton 4 7 := hq
  subst e1; subst e2
  exact ((singleton_disjoint_iff 7 7).mp hd) rfl

def starNoDisj (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂

/- ex x35 starNoDisj_dup -/
theorem starNoDisj_dup (P : Assertion) : P ⊢ starNoDisj P P := by
  intro σ h hp
  exact ⟨h, h, (union_self h).symm, hp, hp⟩
