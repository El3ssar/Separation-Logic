/- Edition 2 · new Lean checked against site/lean/prelude/m11.lean -/

theorem wand_unit (P Q : Assertion) : Q ⊢ P -∗ (P ∗ Q) := by
  intro σ h hq h' hd hp
  exact ⟨h', h, disjoint_symm hd, union_comm hd, hp, hq⟩

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

theorem hole_intro (P R : Assertion) : P ∗ R ⊢ P ∗ (P -∗ (P ∗ R)) :=
  star_mono_right P (wand_unit P R)

theorem hole_elim (P R : Assertion) : P ∗ (P -∗ (P ∗ R)) ⊢ P ∗ R :=
  entails_trans (star_comm P (P -∗ (P ∗ R))) (wand_elim P (P ∗ R))

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
