/- Edition 2 · new Lean checked against site/lean/prelude/m8.lean -/

/- Group B3: locality of control flow, against the M8 prelude. -/

theorem heapLocal_ite {b : BExpr} {c₁ c₂ : Cmd}
    (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) : HeapLocal (.ite b c₁ c₂) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | iteTrue hb hex' =>
      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₁ σ h hFrame s' hd hex'
      exact ⟨hdEnd, r, Exec.iteTrue hb hr, hst, hhp⟩
  | iteFalse hb hex' =>
      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₂ σ h hFrame s' hd hex'
      exact ⟨hdEnd, r, Exec.iteFalse hb hr, hst, hhp⟩

theorem heapLocal_loop_aux {b₀ : BExpr} {c₀ : Cmd} (hc : HeapLocal c₀) :
    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →
      ∀ hFrame, Heap.disjoint s.heap hFrame →
        Heap.disjoint s'.heap hFrame ∧
        ∃ r : State, Exec (.loop b₀ c₀) ⟨s.store, Heap.union s.heap hFrame⟩ r ∧
          r.store = s'.store ∧ r.heap = Heap.union s'.heap hFrame := by
  intro cmd s s' hex
  induction hex with
  | skip => intro heq; cases heq
  | assign => intro heq; cases heq
  | load _ => intro heq; cases heq
  | write _ => intro heq; cases heq
  | free _ => intro heq; cases heq
  | seq _ _ _ _ => intro heq; cases heq
  | iteTrue _ _ _ => intro heq; cases heq
  | iteFalse _ _ _ => intro heq; cases heq
  | loopFalse hb =>
      intro heq hFrame hd
      cases heq
      exact ⟨hd, _, Exec.loopFalse hb, rfl, rfl⟩
  | loopTrue hb hbody _ _ ihrest =>
      intro heq hFrame hd
      cases heq
      rename_i s s' s'' _ _
      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := hc s.store s.heap hFrame s' hd hbody
      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := ihrest rfl hFrame hdMid
      have heq2 : r₁ = ⟨s'.store, Heap.union s'.heap hFrame⟩ := by
        rw [← hst₁, ← hhp₁]
      refine ⟨hdEnd, r₂, Exec.loopTrue (s' := r₁) hb hr₁ ?_, hst₂, hhp₂⟩
      rw [heq2]
      exact hr₂

theorem heapLocal_loop {b : BExpr} {c : Cmd} (hc : HeapLocal c) :
    HeapLocal (.loop b c) := by
  intro σ h hFrame s' hd hex
  exact heapLocal_loop_aux hc hex rfl hFrame hd

theorem write_union_no_disjointness (h hFrame : Heap) (l : Loc) (v : Val) :
    Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame := by
  funext x
  by_cases hx : x = l
  · subst hx
    rw [write_same, union_of_some hFrame (write_same h x v)]
  · rw [write_other (Heap.union h hFrame) l x v hx]
    have hw : Heap.write h l v x = h x := write_other h l x v hx
    cases hh : h x with
    | none => rw [union_of_none hFrame hh, union_of_none hFrame (hw.trans hh)]
    | some w => rw [union_of_some hFrame hh, union_of_some hFrame (hw.trans hh)]

theorem not_heapOnly_pure (x : Var) : ¬ HeapOnly (pure (fun σ => σ x = 0)) := by
  intro hho
  have h := hho (fun _ => 0) (fun _ => 1) Heap.empty ⟨rfl, rfl⟩
  have h1 : (1 : Nat) = 0 := h.1
  exact absurd h1 (by simp)

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

theorem free_with_frame (l other : Loc) (v w : Val) :
    Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (other ↦ w) := by
  have base : Hoare (l ↦ v) (.free l) emp := hoare_free l v
  have framed : Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (emp ∗ (other ↦ w)) :=
    hoare_frame base (heapLocal_free l) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))
  exact hoare_consequence (entails_refl _) framed (star_emp_left _)

def ptsAtLeast (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v

theorem classical_conjunction_rule_is_false :
    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),
        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))
              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))) := by
  intro hall
  obtain ⟨s', hex, h3, h5⟩ :=
    hall 0 0 3 5 (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)
  cases hex with
  | write hl =>
      have e3 : Heap.write (Heap.singleton 0 3) 0 5 0 = some 3 := h3
      rw [write_same] at e3
      exact absurd e3 (by simp)

theorem separated_write_ok (l₁ l₂ : Loc) (a b : Val) :
    Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.write l₂ (.const 5)) ((l₂ ↦ 5) ∗ (l₁ ↦ a)) := by
  have base : Hoare (l₂ ↦ b) (.write l₂ (.const 5)) (l₂ ↦ 5) :=
    hoare_write l₂ (.const 5) b
  exact hoare_frame base (heapLocal_write l₂ (.const 5))
    (preserves_of_heapOnly _ (heapOnly_pointsTo l₁ a))
