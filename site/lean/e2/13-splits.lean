/- ===== Unit 11 · `splits` · LAB — splitting a heap ===== -/

/- ex x25 splits_empty_right -/
theorem splits_empty_right (h : Heap) : Heap.splits h h Heap.empty :=
  ⟨disjoint_empty_right h, (union_empty_right h).symm⟩

/- ex m2-8 splits_empty_left / splits_comm -/
theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h :=
  ⟨disjoint_empty_left h, (union_empty_left h).symm⟩

theorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁ := by
  intro ⟨hd, he⟩
  exact ⟨disjoint_symm hd, by rw [he, union_comm hd]⟩

/- ex m2-9 splits_assoc -/
theorem splits_assoc {h hPQ hP hQ hR : Heap}
    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :
    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by
  obtain ⟨hd₁, he₁⟩ := h1
  obtain ⟨hd₂, he₂⟩ := h2
  subst he₂
  obtain ⟨hPR, hQR'⟩ := disjoint_union_left.mp hd₁
  refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩
  rw [he₁, union_assoc]

/- ex x26 union_not_comm -/
theorem union_not_comm :
    ¬ ∀ h₁ h₂ : Heap, Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  intro h
  have h0 := congrFun (h (Heap.singleton 0 4) (Heap.singleton 0 7)) 0
  rw [union_of_some (Heap.singleton 0 7) (singleton_same 0 4),
      union_of_some (Heap.singleton 0 4) (singleton_same 0 7)] at h0
  exact absurd h0 (by simp)
