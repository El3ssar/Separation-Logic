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

def aForall {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∀ x, P x σ h

theorem star_forall_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aForall P ∗ Q ⊢ aForall (fun x => P x ∗ Q) := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩ x
  exact ⟨h₁, h₂, hd, hu, hp x, hq⟩

def Pcx : Bool → Assertion
  | false => (0 ↦ 4)
  | true  => (1 ↦ 7)

theorem star_forall_right_fails :
    ¬ (aForall (fun x => Pcx x ∗ aTrue) ⊢ aForall Pcx ∗ aTrue) := by
  intro hcontra
  have hlhs : aForall (fun x => Pcx x ∗ aTrue) (fun _ => 0)
      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) := by
    intro x
    cases x with
    | false =>
        exact ⟨Heap.singleton 0 4, Heap.singleton 1 7,
          singleton_disjoint 4 7 (by simp), rfl, rfl, trivial⟩
    | true =>
        refine ⟨Heap.singleton 1 7, Heap.singleton 0 4,
          singleton_disjoint 7 4 (by simp), ?_, rfl, trivial⟩
        exact union_comm (singleton_disjoint 4 7 (by simp))
  obtain ⟨h₁, h₂, _, _, hall, _⟩ := hcontra _ _ hlhs
  have e0 : h₁ = Heap.singleton 0 4 := hall false
  have e1 : h₁ = Heap.singleton 1 7 := hall true
  have : Heap.singleton 0 4 0 = Heap.singleton 1 7 0 := by rw [← e0, ← e1]
  rw [singleton_same, singleton_other 1 0 7 (by simp)] at this
  exact absurd this (by simp)

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
