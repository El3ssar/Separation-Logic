/- ===== Unit 30 · `swap` · LAB/capstone — swap ===== -/

def swap (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) : Cmd :=
  .load tmp₁ l₁ ;; (.load tmp₂ l₂ ;; (.write l₁ (.var tmp₂) ;; .write l₂ (.var tmp₁)))

/- ex m9-4 preserves_load_fact -/
theorem preserves_load_fact {x y : Var} {v : Val} (l : Loc) (hne : y ≠ x) :
    Preserves (.load x l) (pure (fun σ => σ y = v)) := by
  intro s s' hex hFrame hr
  cases hex with
  | load hl =>
      obtain ⟨hy, he⟩ := hr
      refine ⟨?_, he⟩
      show Store.set s.store x _ y = v
      simp [Store.set, hne]
      exact hy

/- ex x61 swap_heap -/
theorem swap_heap (l₁ l₂ : Loc) (a b : Val) (hne : l₁ ≠ l₂) :
    Heap.write (Heap.write (Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b)) l₁ b) l₂ a
      = Heap.union (Heap.singleton l₁ b) (Heap.singleton l₂ a) := by
  funext x
  by_cases hx₂ : x = l₂
  · subst hx₂
    rw [write_same]
    rw [union_of_none (Heap.singleton x a) (singleton_other l₁ x b (fun h => hne h.symm))]
    rw [singleton_same]
  · rw [write_other _ l₂ x a hx₂]
    by_cases hx₁ : x = l₁
    · subst hx₁
      rw [write_same, union_of_some (Heap.singleton l₂ a) (singleton_same x b)]
    · rw [write_other _ l₁ x b hx₁,
          union_of_none (Heap.singleton l₂ b) (singleton_other l₁ x a hx₁),
          union_of_none (Heap.singleton l₂ a) (singleton_other l₁ x b hx₁),
          singleton_other l₂ x b hx₂, singleton_other l₂ x a hx₂]

/- ex x62 swap_spec -/
theorem swap_spec (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) (a b : Val) (hne : tmp₁ ≠ tmp₂) :
    Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap tmp₁ tmp₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a)) := by
  intro σ h hstar
  obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hstar
  subst hp; subst hq; subst hu
  have hlne : l₁ ≠ l₂ := (singleton_disjoint_iff a b).mp hd
  have hH1 : Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b) l₁ = some a :=
    union_of_some _ (singleton_same l₁ a)
  have hH2 : Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b) l₂ = some b := by
    rw [union_of_none (Heap.singleton l₂ b) (singleton_other l₁ l₂ a (Ne.symm hlne)), singleton_same]
  have e2 : Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₂ = b := by simp [Store.set]
  have e1 : Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₁ = a := by simp [Store.set, hne]
  have hH3 : Heap.write (Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b)) l₁
      (Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₂) l₂ = some b := by
    rw [write_other _ l₁ l₂ _ hlne.symm]; exact hH2
  refine ⟨_, Exec.seq (Exec.load hH1) (Exec.seq (Exec.load hH2)
      (Exec.seq (Exec.write hH1) (Exec.write hH3))), ?_⟩
  refine ⟨Heap.singleton l₁ b, Heap.singleton l₂ a, singleton_disjoint b a hlne, ?_, rfl, rfl⟩
  show Heap.write (Heap.write (Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b)) l₁
        (Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₂)) l₂
        (Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₁) = _
  rw [e1, e2]
  exact swap_heap l₁ l₂ a b hlne
