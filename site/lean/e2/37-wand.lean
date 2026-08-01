/- ===== Unit 34 · `wand` · The magic wand ===== -/

def wand (P Q : Assertion) : Assertion :=
  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')
infixr:54 " -∗ " => wand

/- ex m11-1 wand_intro -/
theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R := by
  intro σ hh hp h' hd hq
  exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩

/- ex m11-2 wand_elim -/
theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q := by
  intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩
  rw [hu]
  exact hw h₂ hd hp

/- ex m11-3 star_wand_adjunction -/
theorem star_wand_adjunction (P Q R : Assertion) : (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R) := by
  constructor
  · exact wand_intro
  · intro h
    refine entails_trans (star_mono_left Q h) ?_
    exact wand_elim Q R

/- ex m11-4 wand_mono -/
theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :
    (P -∗ Q) ⊢ (P' -∗ Q') := by
  intro σ h hw h' hd hp'
  exact hq σ _ (hw h' hd (hp σ h' hp'))

/- ex x68 wand_unit / hole_intro / hole_elim -/
theorem wand_unit (P Q : Assertion) : Q ⊢ P -∗ (P ∗ Q) := by
  intro σ h hq h' hd hp
  exact ⟨h', h, disjoint_symm hd, union_comm hd, hp, hq⟩

theorem hole_intro (P R : Assertion) : P ∗ R ⊢ P ∗ (P -∗ (P ∗ R)) :=
  star_mono_right P (wand_unit P R)

theorem hole_elim (P R : Assertion) : P ∗ (P -∗ (P ∗ R)) ⊢ P ∗ R :=
  entails_trans (star_comm P (P -∗ (P ∗ R))) (wand_elim P (P ∗ R))

/- ex x69 wand_curry / wand_uncurry -/
theorem wand_curry (P Q R : Assertion) : ((P ∗ Q) -∗ R) ⊢ P -∗ (Q -∗ R) := by
  intro σ h hw h₁ hd₁ hp h₂ hd₂ hq
  obtain ⟨hdh2, hd12⟩ := disjoint_union_left.mp hd₂
  have hdd : Heap.disjoint h (Heap.union h₁ h₂) :=
    disjoint_union_right.mpr ⟨hd₁, hdh2⟩
  have hR := hw (Heap.union h₁ h₂) hdd ⟨h₁, h₂, hd12, rfl, hp, hq⟩
  rw [union_assoc]
  exact hR

theorem wand_uncurry (P Q R : Assertion) : (P -∗ (Q -∗ R)) ⊢ (P ∗ Q) -∗ R := by
  intro σ h hw h' hd ⟨h₁, h₂, hd₁₂, hu, hp, hq⟩
  subst hu
  obtain ⟨hdh1, hdh2⟩ := disjoint_union_right.mp hd
  have hR := hw h₁ hdh1 hp h₂ (disjoint_union_left.mpr ⟨hdh2, hd₁₂⟩) hq
  rw [← union_assoc]
  exact hR

theorem emp_wand_elim (P : Assertion) : (emp -∗ P) ⊢ P := by
  intro σ h hw
  have hP := hw Heap.empty (disjoint_empty_right h) rfl
  rw [union_empty_right] at hP
  exact hP

theorem emp_wand_intro (P : Assertion) : P ⊢ (emp -∗ P) := by
  intro σ h hp h' hd he
  have he' : h' = Heap.empty := he
  subst he'
  rw [union_empty_right]
  exact hp
