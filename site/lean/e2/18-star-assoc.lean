/- ===== Unit 16 · `star-assoc` · Associativity ===== -/

/- ex m4-4 star_assoc_left / star_assoc_right -/
theorem star_assoc_left (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by
  intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩
  subst hu₂
  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁
  refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩
  · rw [hu₁, union_assoc]
  · exact ⟨hQ, hR, hQR, rfl, hq, hr⟩

theorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by
  intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩
  subst hu₂
  obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁
  refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩
  rw [hu₁, union_assoc]

/- ex x37 star_assoc_iff -/
theorem star_assoc_iff (P Q R : Assertion) : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) :=
  ⟨star_assoc_left P Q R, star_assoc_right P Q R⟩
