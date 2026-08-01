/- ===== Unit 32 · `listrep` · Lists in the heap ===== -/

def node (p : Loc) (value next : Nat) : Assertion :=
  (p ↦ value) ∗ ((p + 1) ↦ next)

def listRep : List Nat → Loc → Assertion
  | [],      p => pure (fun _ => p = 0)
  | x :: xs, p =>
      aExists fun next =>
        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next

/- ex m10-1 listRep_nil / listRep_cons_unfold / listRep_cons_fold -/
theorem listRep_nil (p : Loc) : listRep [] p ⊢ pure (fun _ => p = 0) := entails_refl _

theorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :
    listRep (x :: xs) p ⊢
      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next :=
  entails_refl _

theorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :
    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢
      listRep (x :: xs) p :=
  entails_refl _

/- ex x65 listRep_cons_ne_zero -/
theorem listRep_cons_ne_zero (x : Nat) (xs : List Nat) (p : Loc) :
    listRep (x :: xs) p ⊢ fact (fun _ => p ≠ 0) := by
  intro σ h ⟨n, h₁, h₂, _, _, ⟨hp, _⟩, _⟩
  exact hp

/- ex m10-2 node_cells_distinct -/
theorem node_cells_distinct (p : Loc) (x next : Nat) :
    node p x next ⊢ fact (fun _ => p ≠ p + 1) :=
  two_cells_distinct p (p + 1) x next

/- ex m10-3 concrete_list -/
theorem concrete_list (p : Loc) (a b c : Nat) (q r : Loc)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p := by
  intro σ h hstar
  obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd', hu', hn₂, hn₃⟩ := hstar
  subst hu'
  subst hu
  refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _,
          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩
  refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩
  refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _,
          (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩
  refine ⟨h₃, h₄, hd', rfl, hn₂, ?_⟩
  refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩
  exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩
