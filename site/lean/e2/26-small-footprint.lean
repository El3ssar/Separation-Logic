/- ===== Unit 23 · `small-footprint` · Rules that mention only what they touch ===== -/

/- ex m7-1 hoare_load -/
theorem hoare_load (x : Var) (l : Loc) (v : Val) :
    Hoare (l ↦ v) ((.load x l)) (pure (fun σ => σ x = v) ∗ (l ↦ v)) := by
  intro σ h hp
  subst hp
  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩
  refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩
  show Store.set σ x v x = v
  simp [Store.set]

/- ex m7-2 hoare_write -/
theorem hoare_write (l : Loc) (e : Atom) (old : Val) :
    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h) := by
  intro σ h hp
  subst hp
  exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,
         Exec.write (singleton_same l old),
         write_singleton l old (e.eval σ)⟩

/- ex m7-3 hoare_free -/
theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) ((.free l)) (emp) := by
  intro σ h hp
  subst hp
  exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,
         Exec.free (singleton_same l v),
         erase_singleton l v⟩

def clearCell (l : Loc) : Cmd := .write l (.const 0)

/- ex m7-4 clearCell_spec -/
theorem clearCell_spec (l : Loc) (old : Val) : Hoare (l ↦ old) ((clearCell l)) (l ↦ 0) :=
  hoare_write l (.const 0) old

/- ex x48 writeTwice_spec -/
theorem writeTwice_spec (l : Loc) (old : Val) :
    Hoare (l ↦ old) ((.write l (.const 1) ;; .write l (.const 2))) (l ↦ 2) :=
  hoare_seq (hoare_write l (.const 1) old) (hoare_write l (.const 2) 1)

def readAndFree (x : Var) (l : Loc) : Cmd := .load x l ;; .free l

/- ex m7-5 readAndFree_spec -/
theorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :
    Hoare (l ↦ v) ((readAndFree x l)) (pure (fun σ => σ x = v)) := by
  intro σ h hp
  subst hp
  refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩
  · exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))
  · show Store.set σ x v x = v
    simp [Store.set]
  · exact erase_singleton l v
