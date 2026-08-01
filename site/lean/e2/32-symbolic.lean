/- ===== Unit 29 · `symbolic` · Symbolic execution ===== -/

def StoreStable (c : Cmd) : Prop := ∀ s s', Exec c s s' → s'.store = s.store

/- ex x57 storeStable_write / storeStable_free / preserves_of_storeStable -/
theorem storeStable_write (l : Loc) (e : Atom) : StoreStable (.write l e) := by
  intro s s' hex; cases hex; rfl

theorem storeStable_free (l : Loc) : StoreStable (.free l) := by
  intro s s' hex; cases hex; rfl

theorem preserves_of_storeStable {c : Cmd} (h : StoreStable c) (R : Assertion) :
    Preserves c R := by
  intro s s' hex hFrame hr
  rw [h s s' hex]; exact hr

/- ex x58 readAndFree_framed -/
theorem readAndFree_framed (x : Var) (l : Loc) (v : Val) :
    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=
  hoare_seq
    (hoare_consequence (entails_refl _) (hoare_load x l v) (star_comm _ _))
    (hoare_consequence (entails_refl _)
      (hoare_frame (hoare_free l v) (heapLocal_free l)
        (preserves_of_storeStable (storeStable_free l) _))
      (star_emp_left _))

theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :
    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v) := by
  intro σ h hpre
  obtain ⟨hv, hp⟩ := hpre
  subst hp
  refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,
          Exec.write (singleton_same l old), ?_⟩
  show Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l v
  rw [write_singleton]
  have : e.eval σ = v := hv
  rw [this]

/- ex x59 pure_star_regroup -/
theorem pure_star_regroup (φ : Store → Prop) (P R : Assertion) :
    pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by
  intro σ h hstar
  obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar
  subst he
  refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩
  rw [hu, union_empty_left, huPR]

/- ex x60 hoare_load_and / and_fact_star -/
theorem hoare_load_and (x : Var) (l : Loc) (v : Val) :
    Hoare (l ↦ v) (.load x l) (aAnd (fact (fun σ => σ x = v)) (l ↦ v)) := by
  intro σ h hp
  subst hp
  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_, rfl⟩
  show Store.set σ x v x = v
  simp [Store.set]

theorem and_fact_star (φ : Store → Prop) (P R : Assertion) :
    (aAnd (fact φ) P) ∗ R ⊢ aAnd (fact φ) (P ∗ R) := by
  intro σ h ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩
  exact ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩

theorem and_fact_star_intro (φ : Store → Prop) (P R : Assertion) :
    aAnd (fact φ) (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by
  intro σ h ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩
  exact ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩

def copyCell (tmp : Var) (src dst : Loc) : Cmd :=
  .load tmp src ;; .write dst (.var tmp)

/- ex m9-1 copyCell_spec -/
theorem copyCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :
    Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst) ((src ↦ a) ∗ (dst ↦ a)) := by
  refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_
  · -- the load, framed by `dst ↦ b`, then renormalised
    have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src)
        ((pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)) :=
      hoare_frame (hoare_load tmp src a) (heapLocal_load tmp src)
        (preserves_of_heapOnly _ (heapOnly_pointsTo dst b))
    refine hoare_consequence (entails_refl _) step ?_
    refine entails_trans (star_assoc_left _ _ _) ?_
    refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_
    exact pure_star_regroup _ _ _
  · -- the write, with the value known from the pure fact, framed by `src ↦ a`
    have step : Hoare ((aAnd (fact (fun σ => (Atom.var tmp).eval σ = a)) (dst ↦ b)) ∗ (src ↦ a))
        (.write dst (.var tmp)) ((dst ↦ a) ∗ (src ↦ a)) :=
      hoare_frame (hoare_write_val dst (.var tmp) b a) (heapLocal_write dst (.var tmp))
        (preserves_of_storeStable (storeStable_write dst (.var tmp)) _)
    exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))

def moveCell (tmp : Var) (src dst : Loc) : Cmd :=
  copyCell tmp src dst ;; .free src

/- ex m9-2 exec_seq_assoc -/
theorem exec_seq_assoc {c₁ c₂ c₃ : Cmd} {s s' : State} :
    Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; (c₂ ;; c₃)) s s' := by
  constructor
  · intro h
    cases h with | seq h₁ h₂ => cases h₁ with | seq ha hb => exact .seq ha (.seq hb h₂)
  · intro h
    cases h with | seq h₁ h₂ => cases h₂ with | seq ha hb => exact .seq (.seq h₁ ha) hb

/- ex m9-3 moveCell_spec -/
theorem moveCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :
    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCell tmp src dst) (dst ↦ a) := by
  refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_
  have step : Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a)) :=
    hoare_frame (hoare_free src a) (heapLocal_free src)
      (preserves_of_storeStable (storeStable_free src) _)
  exact hoare_consequence (entails_refl _) step (star_emp_left _)
