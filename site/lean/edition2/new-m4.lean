/- Edition 2 · new Lean checked against site/lean/prelude/m4.lean -/

theorem self_disjoint_iff_empty (h : Heap) : Heap.disjoint h h ↔ h = Heap.empty := by
  constructor
  · intro hd
    funext l
    rcases hd l with h1 | h1 <;> exact h1
  · intro he l
    subst he
    exact Or.inl rfl

theorem union_self (h : Heap) : Heap.union h h = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none h hl]; exact hl
  | some v => rw [union_of_some h hl]

theorem union_cancel_left {h₁ h₂ h₃ : Heap}
    (hd₂ : Heap.disjoint h₁ h₂) (hd₃ : Heap.disjoint h₁ h₃)
    (he : Heap.union h₁ h₂ = Heap.union h₁ h₃) : h₂ = h₃ := by
  funext l
  have hl := congrFun he l
  cases h1 : h₁ l with
  | none => rw [union_of_none h₂ h1, union_of_none h₃ h1] at hl; exact hl
  | some v =>
      rcases hd₂ l with e | e
      · rw [h1] at e; exact absurd e (by simp)
      · rcases hd₃ l with e' | e'
        · rw [h1] at e'; exact absurd e' (by simp)
        · rw [e, e']

structure PCM (M : Type) where
  op         : M → M → M
  unit       : M
  valid      : M → M → Prop
  op_comm    : ∀ a b, valid a b → op a b = op b a
  op_assoc   : ∀ a b c, op (op a b) c = op a (op b c)
  unit_left  : ∀ a, op unit a = a
  valid_unit : ∀ a, valid unit a
  valid_comm : ∀ a b, valid a b → valid b a

def heapPCM : PCM Heap where
  op         := Heap.union
  unit       := Heap.empty
  valid      := Heap.disjoint
  op_comm    := fun _ _ hd => union_comm hd
  op_assoc   := union_assoc
  unit_left  := union_empty_left
  valid_unit := disjoint_empty_left
  valid_comm := fun _ _ hd => disjoint_symm hd

def pcmStar {M : Type} (K : PCM M) (P Q : M → Prop) : M → Prop :=
  fun m => ∃ m₁ m₂, K.valid m₁ m₂ ∧ m = K.op m₁ m₂ ∧ P m₁ ∧ Q m₂

theorem pcmStar_comm {M : Type} (K : PCM M) (P Q : M → Prop) (m : M) :
    pcmStar K P Q m → pcmStar K Q P m := by
  intro ⟨m₁, m₂, hv, hm, hp, hq⟩
  exact ⟨m₂, m₁, K.valid_comm _ _ hv, by rw [hm, K.op_comm _ _ hv], hq, hp⟩

theorem pcmStar_unit_left {M : Type} (K : PCM M) (P : M → Prop) (m : M) :
    pcmStar K (fun x => x = K.unit) P m → P m := by
  intro ⟨m₁, m₂, _, hm, he, hp⟩
  subst he
  rw [hm, K.unit_left]
  exact hp

/- Group B2: PCM + star-level new rungs, against the M4 prelude. -/

theorem splits_empty_right (h : Heap) : Heap.splits h h Heap.empty :=
  ⟨disjoint_empty_right h, (union_empty_right h).symm⟩

-- the two-directional forms.  Edition 1 proves the halves and never joins them.
theorem star_emp_left_iff (P : Assertion) : emp ∗ P ⊣⊢ P :=
  ⟨star_emp_left P, star_emp_left_intro P⟩

theorem star_emp_right_iff (P : Assertion) : P ∗ emp ⊣⊢ P :=
  ⟨star_emp_right P, star_emp_right_intro P⟩

theorem star_assoc_iff (P Q R : Assertion) : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) :=
  ⟨star_assoc_left P Q R, star_assoc_right P Q R⟩

theorem star_comm_iff (P Q : Assertion) : P ∗ Q ⊣⊢ Q ∗ P :=
  ⟨star_comm P Q, star_comm Q P⟩

-- equivalence is an equivalence relation: the reader needs this to chain ⊣⊢
theorem equiv_refl (P : Assertion) : P ⊣⊢ P := ⟨entails_refl P, entails_refl P⟩

theorem equiv_symm {P Q : Assertion} (h : P ⊣⊢ Q) : Q ⊣⊢ P := ⟨h.2, h.1⟩

theorem equiv_trans {P Q R : Assertion} (h₁ : P ⊣⊢ Q) (h₂ : Q ⊣⊢ R) : P ⊣⊢ R :=
  ⟨entails_trans h₁.1 h₂.1, entails_trans h₂.2 h₁.2⟩

-- ∗ has no projection: the substructural fact, made into a theorem
theorem star_not_weakening : ¬ (∀ P Q : Assertion, P ∗ Q ⊢ P) := by
  intro hbad
  have h : (emp ∗ (0 ↦ 0)) ⊢ emp := hbad emp (0 ↦ 0)
  have h2 : (0 ↦ 0) ⊢ emp := entails_trans (star_emp_left_intro _) h
  exact pointsTo_not_emp 0 0 h2

-- the other missing direction of star_or
theorem star_or_right (P Q R : Assertion) : aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by
  intro σ h hor
  rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inl hp, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inr hq, hr⟩

theorem star_exists_right {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aExists (fun x => P x ∗ Q) ⊢ aExists P ∗ Q := by
  intro σ h ⟨x, h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩

theorem no_star_duplication : ¬ (∀ P : Assertion, P ⊢ P ∗ P) := by
  intro hall
  obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hall (4 ↦ 7) (fun _ => 0) (Heap.singleton 4 7) rfl
  have e1 : h₁ = Heap.singleton 4 7 := hp
  have e2 : h₂ = Heap.singleton 4 7 := hq
  subst e1; subst e2
  exact ((singleton_disjoint_iff 7 7).mp hd) rfl

theorem no_star_weakening : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)) := by
  intro hall
  have h := hall (fun _ => 0) (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7))
    ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl, rfl⟩
  have h1 := congrFun h 1
  rw [union_of_none (Heap.singleton 1 7) (singleton_other 0 1 4 (by simp)),
      singleton_same, singleton_other 0 1 4 (by simp)] at h1
  exact absurd h1 (by simp)

theorem star_congr {P P' Q Q' : Assertion} (hp : P ⊣⊢ P') (hq : Q ⊣⊢ Q') :
    P ∗ Q ⊣⊢ P' ∗ Q' :=
  ⟨star_mono hp.1 hq.1, star_mono hp.2 hq.2⟩

theorem star_intro {P Q : Assertion} {σ : Store} {h h₁ h₂ : Heap}
    (hd : Heap.disjoint h₁ h₂) (hu : h = Heap.union h₁ h₂)
    (hp : P σ h₁) (hq : Q σ h₂) : (P ∗ Q) σ h :=
  ⟨h₁, h₂, hd, hu, hp, hq⟩

theorem star_same_loc_absurd (l : Loc) (v₁ v₂ : Val) :
    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact ((singleton_disjoint_iff v₁ v₂).mp hd) rfl

def starNoDisj (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂

theorem starNoDisj_dup (P : Assertion) : P ⊢ starNoDisj P P := by
  intro σ h hp
  exact ⟨h, h, (union_self h).symm, hp, hp⟩

theorem star_pointsTo_same_false (l : Loc) (v₁ v₂ : Val) :
    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact absurd ((singleton_disjoint_iff v₁ v₂).mp hd) (by simp)

theorem or_left (P Q : Assertion) : P ⊢ aOr P Q := fun _ _ hp => Or.inl hp
theorem or_right (P Q : Assertion) : Q ⊢ aOr P Q := fun _ _ hq => Or.inr hq
theorem or_elim {P Q R : Assertion} (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : aOr P Q ⊢ R := by
  intro σ h hpq
  rcases hpq with hp | hq
  · exact h₁ σ h hp
  · exact h₂ σ h hq
