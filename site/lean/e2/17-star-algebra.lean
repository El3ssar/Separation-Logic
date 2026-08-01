/- ===== Unit 15 · `star-algebra` · LAB — the laws of `∗` ===== -/

/- ex m4-1 star_emp_left / star_emp_right -/
theorem star_emp_left (P : Assertion) : emp ∗ P ⊢ P := by
  intro σ h ⟨h₁, h₂, _, hu, he, hp⟩
  rw [hu, he, union_empty_left]
  exact hp

theorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by
  intro σ h ⟨h₁, h₂, _, hu, hp, he⟩
  rw [hu, he, union_empty_right]
  exact hp

/- ex m4-2 star_emp_left_intro / star_emp_right_intro -/
theorem star_emp_left_intro (P : Assertion) : P ⊢ emp ∗ P := by
  intro σ h hp
  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩

theorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by
  intro σ h hp
  exact ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩

/- ex m4-3 star_comm -/
theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩

/- ex m4-5 star_mono / star_mono_left / star_mono_right -/
theorem star_mono {P P' Q Q' : Assertion} (hpq : P ⊢ P') (hrs : Q ⊢ Q') :
    P ∗ Q ⊢ P' ∗ Q' := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩

theorem star_mono_left {P P' : Assertion} (Q : Assertion) (h : P ⊢ P') : P ∗ Q ⊢ P' ∗ Q :=
  star_mono h (entails_refl Q)

theorem star_mono_right (P : Assertion) {Q Q' : Assertion} (h : Q ⊢ Q') : P ∗ Q ⊢ P ∗ Q' :=
  star_mono (entails_refl P) h

/- ex m4-6 star_or_left / star_exists_left -/
theorem star_or_left (P Q R : Assertion) : (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R) := by
  intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩
  rcases hpq with hp | hq
  · exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩
  · exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩

theorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q) := by
  intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩
  exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩

/- ex x36 star_emp_left_iff / star_emp_right_iff / star_comm_iff / star_congr -/
theorem star_emp_left_iff (P : Assertion) : emp ∗ P ⊣⊢ P :=
  ⟨star_emp_left P, star_emp_left_intro P⟩

theorem star_emp_right_iff (P : Assertion) : P ∗ emp ⊣⊢ P :=
  ⟨star_emp_right P, star_emp_right_intro P⟩

theorem star_comm_iff (P Q : Assertion) : P ∗ Q ⊣⊢ Q ∗ P :=
  ⟨star_comm P Q, star_comm Q P⟩

theorem star_congr {P P' Q Q' : Assertion} (hp : P ⊣⊢ P') (hq : Q ⊣⊢ Q') :
    P ∗ Q ⊣⊢ P' ∗ Q' :=
  ⟨star_mono hp.1 hq.1, star_mono hp.2 hq.2⟩

-- ∗ has no projection: the substructural fact, made into a theorem
theorem star_not_weakening : ¬ (∀ P Q : Assertion, P ∗ Q ⊢ P) := by
  intro hbad
  have h : (emp ∗ (0 ↦ 0)) ⊢ emp := hbad emp (0 ↦ 0)
  have h2 : (0 ↦ 0) ⊢ emp := entails_trans (star_emp_left_intro _) h
  exact pointsTo_not_emp 0 0 h2
