/- Edition 2 · new Lean checked against site/lean/prelude/m9.lean -/

theorem hoare_load_and (x : Var) (l : Loc) (v : Val) :
    Hoare (l ↦ v) (.load x l) (aAnd (fact (fun σ => σ x = v)) (l ↦ v)) := by
  intro σ h hp
  subst hp
  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_, rfl⟩
  show Store.set σ x v x = v
  simp [Store.set]

theorem and_fact_star (φ : Store → Prop) (P R : Assertion) :
    (aAnd (fact φ) P) ∗ R ⊢ aAnd (fact φ) (P ∗ R) := by
  intro σ h ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩
  exact ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩

theorem and_fact_star_intro (φ : Store → Prop) (P R : Assertion) :
    aAnd (fact φ) (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by
  intro σ h ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩
  exact ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩
