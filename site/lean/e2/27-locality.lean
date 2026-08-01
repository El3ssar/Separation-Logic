/- ===== Unit 24 · `locality` · What "local" has to mean ===== -/

def HeapLocal (c : Cmd) : Prop :=
  ∀ σ h hFrame s',
    Heap.disjoint h hFrame →
    Exec c ⟨σ, h⟩ s' →
    Heap.disjoint s'.heap hFrame ∧
    ∃ r : State,
      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧
      r.store = s'.store ∧
      r.heap = Heap.union s'.heap hFrame

def Preserves (c : Cmd) (R : Assertion) : Prop :=
  ∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame

def HeapOnly (R : Assertion) : Prop := ∀ σ σ' h, R σ h → R σ' h

theorem preserves_of_heapOnly {R : Assertion} (c : Cmd) (h : HeapOnly R) : Preserves c R :=
  fun s s' _ hFrame hr => h s.store s'.store hFrame hr

/- ex x49 heapOnly_pointsTo / heapOnly_emp / heapOnly_star -/
theorem heapOnly_pointsTo (l : Loc) (v : Val) : HeapOnly (l ↦ v) :=
  fun _ _ _ hr => hr

theorem heapOnly_emp : HeapOnly emp := fun _ _ _ hr => hr

theorem heapOnly_star {P Q : Assertion} (hp : HeapOnly P) (hq : HeapOnly Q) :
    HeapOnly (P ∗ Q) := by
  intro σ σ' h ⟨h₁, h₂, hd, hu, h1, h2⟩
  exact ⟨h₁, h₂, hd, hu, hp σ σ' h₁ h1, hq σ σ' h₂ h2⟩

/- ex m8-1 heapLocal_skip / heapLocal_assign / heapLocal_load -/
theorem heapLocal_skip : HeapLocal .skip := by
  intro σ h hFrame s' hd hex
  cases hex
  exact ⟨hd, ⟨σ, Heap.union h hFrame⟩, Exec.skip, rfl, rfl⟩

theorem heapLocal_assign (x : Var) (e : Atom) : HeapLocal (.assign x e) := by
  intro σ h hFrame s' hd hex
  cases hex
  exact ⟨hd, ⟨Store.set σ x (e.eval σ), Heap.union h hFrame⟩, Exec.assign, rfl, rfl⟩

theorem heapLocal_load (x : Var) (l : Loc) : HeapLocal (.load x l) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | load hl =>
      refine ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩, Exec.load ?_, rfl, rfl⟩
      exact union_of_some hFrame hl

/- ex x50 not_heapOnly_pure -/
theorem not_heapOnly_pure (x : Var) : ¬ HeapOnly (pure (fun σ => σ x = 0)) := by
  intro hho
  have h := hho (fun _ => 0) (fun _ => 1) Heap.empty ⟨rfl, rfl⟩
  have h1 : (1 : Nat) = 0 := h.1
  exact absurd h1 (by simp)

/- ex x51 frame_needs_preserves — the store counterexample, as a refutation -/
-- framing an assignment with a store fact is false
theorem frame_needs_preserves (x : Var) :
    Hoare (pure (fun σ => σ x = 0)) (.assign x (.const 1)) (pure (fun σ => σ x = 1))
    ∧ ¬ Hoare (pure (fun σ => σ x = 0) ∗ pure (fun σ => σ x = 0))
              (.assign x (.const 1))
              (pure (fun σ => σ x = 1) ∗ pure (fun σ => σ x = 0)) := by
  constructor
  · intro σ h ⟨_, he⟩
    refine ⟨⟨Store.set σ x 1, h⟩, Exec.assign, ?_, he⟩
    show Store.set σ x 1 x = 1
    simp [Store.set]
  · intro hall
    obtain ⟨s', hex, h₁, h₂, _, _, hq, hr⟩ :=
      hall (fun _ => 0) Heap.empty
        ⟨Heap.empty, Heap.empty, disjoint_empty_left _, (union_empty_left _).symm,
         ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    cases hex
    have e0 : Store.set (fun _ => 0) x 1 x = 0 := hr.1
    rw [show Store.set (fun _ => 0) x 1 x = 1 from by simp [Store.set]] at e0
    exact absurd e0 (by simp)
