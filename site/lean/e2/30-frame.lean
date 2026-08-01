/- ===== Unit 27 · `frame` · The frame rule ===== -/

/- ex m8-5 hoare_frame -/
theorem hoare_frame {P Q R : Assertion} {c : Cmd}
    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :
    Hoare (P ∗ R) c (Q ∗ R) := by
  intro σ h hstar
  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar
  obtain ⟨s', hex, hq⟩ := hc σ hP hp
  obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex
  subst hu
  refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩
  · rw [hrst]; exact hq
  · exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr

/- ex m8-6 write_with_frame -/
theorem write_with_frame (l other : Loc) (old new w : Val) :
    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new)) ((l ↦ new) ∗ (other ↦ w)) := by
  have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=
    hoare_write l (.const new) old
  exact hoare_frame base (heapLocal_write l (.const new))
    (preserves_of_heapOnly _ (heapOnly_pointsTo other w))

/- ex x54 free_with_frame -/
theorem free_with_frame (l other : Loc) (v w : Val) :
    Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (other ↦ w) := by
  have base : Hoare (l ↦ v) (.free l) emp := hoare_free l v
  have framed : Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (emp ∗ (other ↦ w)) :=
    hoare_frame base (heapLocal_free l) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))
  exact hoare_consequence (entails_refl _) framed (star_emp_left _)
