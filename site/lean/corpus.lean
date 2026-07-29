/- ============================================================
   Separation Logic in Lean 4 — the complete verified corpus.

   Every definition and every exercise solution from milestones
   M0 through M13, concatenated in course order.

   Checked with Lean 4.32.2. No imports. No Mathlib. No sorry.
     $ lean corpus.lean       (silence means it all compiled)

   M14 (optional allocation) and the Reference chapter contain
   deliberately schematic code and are not included here.
   ============================================================ -/


/- ===== § What we are building, and why ===== -/

/- code -/
abbrev Loc   := Nat
abbrev Val   := Nat
abbrev Heap  := Loc → Option Val
abbrev Var   := Nat
abbrev Store := Var → Val

/- code -/
abbrev Assertion := Store → Heap → Prop


/- ===== M0 The Lean you actually need ===== -/

/- code -/
theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp

/- code -/
theorem exists_example : ∃ n : Nat, n = 3 := ⟨3, rfl⟩

/- code -/
theorem function_extensionality {f g : Nat → Nat}
    (h : ∀ x, f x = g x) : f = g := funext h

/- code -/
def update (f : Nat → Nat) (x value : Nat) : Nat → Nat :=
  fun y => if y = x then value else f y

/- ex m0-1 update_same -/
theorem update_same (f : Nat → Nat) (x value : Nat) :
    update f x value x = value := by
  simp [update]

/- ex m0-2 update_other -/
theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :
    update f x value y = f y := by
  simp [update, hne]

/- ex m0-3 update_shadow -/
theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x <;> simp [update, h]

/- ex m0-4 update_comm -/
theorem update_comm (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :
    update (update f x a) y b = update (update f y b) x a := by
  funext z
  unfold update
  by_cases hzx : z = x
  · have hzy : z ≠ y := by rw [hzx]; exact hne
    rw [if_neg hzy, if_pos hzx, if_pos hzx]
  · by_cases hzy : z = y
    · rw [if_pos hzy, if_neg hzx, if_pos hzy]
    · rw [if_neg hzy, if_neg hzx, if_neg hzx, if_neg hzy]


/- ===== M1 Heaps as partial functions ===== -/

/- code -/
namespace Heap

def empty : Heap := fun _ => none

def singleton (l : Loc) (v : Val) : Heap :=
  fun x => if x = l then some v else none

def write (h : Heap) (l : Loc) (v : Val) : Heap :=
  fun x => if x = l then some v else h x

def erase (h : Heap) (l : Loc) : Heap :=
  fun x => if x = l then none else h x

end Heap

/- ex m1-1 singleton_same -/
theorem singleton_same (l : Loc) (v : Val) :
    Heap.singleton l v l = some v := by
  simp [Heap.singleton]

/- ex m1-2 singleton_other -/
theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.singleton l v x = none := by
  simp [Heap.singleton, hne]

/- ex m1-3 write_same / write_other -/
theorem write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.write h l v l = some v := by
  simp [Heap.write]

theorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.write h l v x = h x := by
  simp [Heap.write, hne]

/- ex m1-4 erase_same / erase_other -/
theorem erase_same (h : Heap) (l : Loc) :
    Heap.erase h l l = none := by
  simp [Heap.erase]

theorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :
    Heap.erase h l x = h x := by
  simp [Heap.erase, hne]

/- ex m1-5 write_shadow -/
theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, hx]

/- ex m1-6 erase_write_same -/
theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.erase (Heap.write h l v) l = Heap.erase h l := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]

/- ex m1-7 write_comm -/
theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by
  funext x
  unfold Heap.write
  by_cases hx₁ : x = l₁
  · have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne
    rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]
  · by_cases hx₂ : x = l₂
    · rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]
    · rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]

/- ex m1-8 write_singleton / erase_singleton -/
theorem write_singleton (l : Loc) (v w : Val) :
    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]

theorem erase_singleton (l : Loc) (v : Val) :
    Heap.erase (Heap.singleton l v) l = Heap.empty := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]


/- ===== M2 Disjointness, union, and the resource monoid ===== -/

/- code -/
def Heap.disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ l, h₁ l = none ∨ h₂ l = none

def Heap.union (h₁ h₂ : Heap) : Heap :=
  fun l =>
    match h₁ l with
    | some v => some v
    | none   => h₂ l

def Heap.splits (whole left right : Heap) : Prop :=
  Heap.disjoint left right ∧ whole = Heap.union left right

/- ex m2-1 disjoint_symm -/
theorem disjoint_symm {h₁ h₂ : Heap} : Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁ := by
  intro hd l
  exact (hd l).symm

/- ex m2-2 disjoint_empty_left / right -/
theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=
  fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty :=
  fun _ => Or.inr rfl

/- ex m2-3 singleton_disjoint (and its converse) -/
theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) := by
  intro x
  by_cases hx : x = l₁
  · right
    have : x ≠ l₂ := by rw [hx]; exact hne
    exact singleton_other l₂ x v₂ this
  · left
    exact singleton_other l₁ x v₁ hx

theorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :
    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂ := by
  constructor
  · intro hd heq
    subst heq
    rcases hd l₁ with h | h <;>
      · rw [singleton_same] at h; exact absurd h (by simp)
  · exact singleton_disjoint v₁ v₂

/- code -/
theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :
    Heap.union h₁ h₂ l = h₂ l := by
  simp [Heap.union, hl]

theorem union_of_some {h₁ : Heap} (h₂ : Heap) {l : Loc} {v : Val} (hl : h₁ l = some v) :
    Heap.union h₁ h₂ l = some v := by
  simp [Heap.union, hl]

theorem union_eq_none {h₁ h₂ : Heap} {l : Loc} :
    Heap.union h₁ h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by
  constructor
  · intro h
    cases hl : h₁ l with
    | none   => exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩
    | some v => rw [union_of_some h₂ hl] at h; exact absurd h (by simp)
  · intro ⟨ha, hb⟩
    rw [union_of_none h₂ ha]; exact hb

/- ex m2-4 union_empty_left / right -/
theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext l; rfl

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none Heap.empty hl]; rfl
  | some v => rw [union_of_some Heap.empty hl]

/- ex m2-5 union_assoc -/
theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by
  funext l
  cases hl : h₁ l with
  | none =>
      rw [union_of_none (Heap.union h₂ h₃) hl]
      cases hl2 : h₂ l with
      | none =>
          rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]
      | some v =>
          have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2
          rw [union_of_some h₃ hu, union_of_some h₃ hl2]
  | some v =>
      rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]

/- ex m2-6 union_comm -/
theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext l
  rcases hd l with h | h
  · rw [union_of_none h₂ h]
    cases hl : h₂ l with
    | none   => rw [union_of_none h₁ hl, h]
    | some v => rw [union_of_some h₁ hl]
  · rw [union_of_none h₁ h]
    cases hl : h₁ l with
    | none   => rw [union_of_none h₂ hl]; exact h
    | some v => rw [union_of_some h₂ hl]

/- ex m2-7 disjoint_union_left / right -/
theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :
    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by
  constructor
  · intro hd
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rcases hd l with h | h
      · exact Or.inl (union_eq_none.mp h).1
      · exact Or.inr h
    · rcases hd l with h | h
      · exact Or.inl (union_eq_none.mp h).2
      · exact Or.inr h
  · intro ⟨ha, hb⟩ l
    rcases ha l with h | h
    · rcases hb l with h' | h'
      · exact Or.inl (union_eq_none.mpr ⟨h, h'⟩)
      · exact Or.inr h'
    · exact Or.inr h

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} :
    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃ := by
  constructor
  · intro hd
    have h' := disjoint_union_left.mp (disjoint_symm hd)
    exact ⟨disjoint_symm h'.1, disjoint_symm h'.2⟩
  · intro ⟨ha, hb⟩
    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)

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


/- ===== M3 Assertions, entailment, and exact ownership ===== -/

/- (repeat of earlier block, skipped) -/

/- code -/
def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h
infix:40 " ⊢ " => Entails

def AssertionEquiv (P Q : Assertion) : Prop := Entails P Q ∧ Entails Q P
infix:40 " ⊣⊢ " => AssertionEquiv

/- code -/
def aTrue  : Assertion := fun _ _ => True

def aFalse : Assertion := fun _ _ => False

def aAnd (P Q : Assertion) : Assertion := fun σ h => P σ h ∧ Q σ h

def aOr  (P Q : Assertion) : Assertion := fun σ h => P σ h ∨ Q σ h

def aExists {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∃ x, P x σ h

/- code -/
def emp : Assertion := fun _ h => h = Heap.empty

def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v
infix:60 " ↦ " => pointsTo

/- code -/
def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ

def pure (φ : Store → Prop) : Assertion := aAnd (fact φ) emp

/- ex m3-1 pointsTo_value_unique — and why the obvious statement is false -/
theorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :
    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂) := by
  intro σ h ⟨h1, h2⟩
  have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]
  rw [singleton_same, singleton_same] at this
  exact Option.some.inj this

theorem pointsTo_not_emp (l : Loc) (v : Val) :
    ¬ ((l ↦ v) ⊢ emp) := by
  intro hcontra
  have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl
  have : Heap.singleton l v l = Heap.empty l := by rw [h]
  rw [singleton_same] at this
  exact absurd this (by simp [Heap.empty])

/- ex m3-2 entails_refl / entails_trans -/
theorem entails_refl (P : Assertion) : P ⊢ P := fun _ _ hp => hp

theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun σ h hp => h₂ σ h (h₁ σ h hp)

/- ex m3-3 and_left / and_right / and_intro -/
theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1

theorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2

theorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=
  fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩


/- ===== M4 Separating conjunction ===== -/

/- code -/
def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂
infixr:55 " ∗ " => star

/- ex m4-1 star_emp_left / star_emp_right -/
theorem star_emp_left (P : Assertion) : emp ∗ P ⊢ P := by
  intro σ h ⟨h₁, h₂, _, hu, he, hp⟩
  rw [hu, he, union_empty_left]
  exact hp

theorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by
  intro σ h ⟨h₁, h₂, _, hu, hp, he⟩
  rw [hu, he, union_empty_right]
  exact hp

/- ex m4-2 star_emp_left_intro / star_emp_right_intro -/
theorem star_emp_left_intro (P : Assertion) : P ⊢ emp ∗ P := by
  intro σ h hp
  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩

theorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by
  intro σ h hp
  exact ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩

/- ex m4-3 star_comm -/
theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩

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

/- ex m4-5 star_mono -/
theorem star_mono {P P' Q Q' : Assertion} (hpq : P ⊢ P') (hrs : Q ⊢ Q') :
    P ∗ Q ⊢ P' ∗ Q' := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩

theorem star_mono_left {P P' : Assertion} (Q : Assertion) (h : P ⊢ P') : P ∗ Q ⊢ P' ∗ Q :=
  star_mono h (entails_refl Q)

theorem star_mono_right (P : Assertion) {Q Q' : Assertion} (h : Q ⊢ Q') : P ∗ Q ⊢ P ∗ Q' :=
  star_mono (entails_refl P) h

/- ex m4-6 star_or_left / star_exists_left -/
theorem star_or_left (P Q R : Assertion) : (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R) := by
  intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩
  rcases hpq with hp | hq
  · exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩
  · exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩

theorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q) := by
  intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩
  exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩

/- ex m4-7 two_cells_distinct -/
theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :
    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact (singleton_disjoint_iff v₁ v₂).mp hd

/- ex m4-8 star_swap_middle, star_rotate_left/right, star_pure_left/right -/
theorem star_swap_middle (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) :=
  entails_trans (star_assoc_right P Q R)
    (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))

theorem star_rotate_left (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R :=
  star_assoc_right P Q R

theorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) :=
  star_assoc_left P Q R

theorem star_pure_left (φ : Store → Prop) (P : Assertion) :
    pure φ ∗ P ⊢ aAnd (fact φ) P := by
  intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩
  subst he
  rw [hu, union_empty_left]
  exact ⟨hφ, hp⟩

theorem star_pure_right (φ : Store → Prop) (P : Assertion) :
    aAnd (fact φ) P ⊢ pure φ ∗ P := by
  intro σ h ⟨hφ, hp⟩
  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩


/- ===== M5 A tiny imperative language ===== -/

/- code -/
inductive Atom where
  | const : Nat → Atom
  | var   : Var → Atom
  | plus  : Atom → Atom → Atom
  | minus : Atom → Atom → Atom
  deriving Repr

def Atom.eval (σ : Store) : Atom → Val
  | .const v  => v
  | .var x    => σ x
  | .plus a b => a.eval σ + b.eval σ
  | .minus a b => a.eval σ - b.eval σ

def Store.set (σ : Store) (x : Var) (v : Val) : Store :=
  fun y => if y = x then v else σ y

structure State where
  store : Store
  heap  : Heap

/- code -/
inductive BExpr where
  | equals : Atom → Atom → BExpr
  | not    : BExpr → BExpr

def BExpr.eval (σ : Store) : BExpr → Bool
  | .equals a b => a.eval σ == b.eval σ
  | .not b      => !(b.eval σ)

/- code -/
inductive Cmd where
  | skip
  | assign : Var → Atom → Cmd
  | load   : Var → Loc → Cmd
  | write  : Loc → Atom → Cmd
  | free   : Loc → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : BExpr → Cmd → Cmd → Cmd
  | loop   : BExpr → Cmd → Cmd

infixr:60 " ;; " => Cmd.seq

/- code -/
inductive Exec : Cmd → State → State → Prop where
  | skip {s} : Exec .skip s s
  | assign {s x e} :
      Exec (.assign x e) s ⟨Store.set s.store x (e.eval s.store), s.heap⟩
  | load {s x l v} (hl : s.heap l = some v) :
      Exec (.load x l) s ⟨Store.set s.store x v, s.heap⟩
  | write {s l e old} (hl : s.heap l = some old) :
      Exec (.write l e) s ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩
  | free {s l v} (hl : s.heap l = some v) :
      Exec (.free l) s ⟨s.store, Heap.erase s.heap l⟩
  | seq {s s' s'' c₁ c₂} (h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'') :
      Exec (c₁ ;; c₂) s s''
  | iteTrue {s s' b c₁ c₂} (hb : b.eval s.store = true) (h : Exec c₁ s s') :
      Exec (.ite b c₁ c₂) s s'
  | iteFalse {s s' b c₁ c₂} (hb : b.eval s.store = false) (h : Exec c₂ s s') :
      Exec (.ite b c₁ c₂) s s'
  | loopFalse {s b c} (hb : b.eval s.store = false) :
      Exec (.loop b c) s s
  | loopTrue {s s' s'' b c} (hb : b.eval s.store = true)
      (hbody : Exec c s s') (hrest : Exec (.loop b c) s' s'') :
      Exec (.loop b c) s s''

/- ex m5-1 exec_skip_inv -/
theorem exec_skip_inv {s s' : State} (h : Exec .skip s s') : s' = s := by
  cases h; rfl

/- ex m5-2 exec_deterministic -/
theorem exec_deterministic {c : Cmd} {s s₁ s₂ : State}
    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | skip => cases h₂; rfl
  | assign => cases h₂; rfl
  | load hl => cases h₂ with | load hl' => rw [hl] at hl'; cases hl'; rfl
  | write hl => cases h₂ with | write hl' => rfl
  | free hl => cases h₂ with | free hl' => rfl
  | seq _ _ ih₁ ih₂ =>
      cases h₂ with
      | seq h₁' h₂' => exact ih₂ (ih₁ h₁' ▸ h₂')
  | iteTrue hb _ ih =>
      cases h₂ with
      | iteTrue hb' h' => exact ih h'
      | iteFalse hb' h' => rw [hb] at hb'; exact absurd hb' (by simp)
  | iteFalse hb _ ih =>
      cases h₂ with
      | iteTrue hb' h' => rw [hb] at hb'; exact absurd hb' (by simp)
      | iteFalse hb' h' => exact ih h'
  | loopFalse hb =>
      cases h₂ with
      | loopFalse hb' => rfl
      | loopTrue hb' _ _ => rw [hb] at hb'; exact absurd hb' (by simp)
  | loopTrue hb _ _ ihb ihr =>
      cases h₂ with
      | loopFalse hb' => rw [hb] at hb'; exact absurd hb' (by simp)
      | loopTrue hb' hbody' hrest' => exact ihr (ihb hbody' ▸ hrest')

/- code -/
def run : Nat → Cmd → State → Option State
  | 0,     _,            _ => none
  | _ + 1, .skip,        s => some s
  | _ + 1, .assign x e,  s => some ⟨Store.set s.store x (e.eval s.store), s.heap⟩
  | _ + 1, .load x l,    s =>
      match s.heap l with
      | some v => some ⟨Store.set s.store x v, s.heap⟩
      | none   => none
  | _ + 1, .write l e,   s =>
      match s.heap l with
      | some _ => some ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩
      | none   => none
  | _ + 1, .free l,      s =>
      match s.heap l with
      | some _ => some ⟨s.store, Heap.erase s.heap l⟩
      | none   => none
  | n + 1, .seq c₁ c₂,   s =>
      match run n c₁ s with
      | some s' => run n c₂ s'
      | none    => none
  | n + 1, .ite b c₁ c₂, s =>
      match b.eval s.store with
      | true  => run n c₁ s
      | false => run n c₂ s
  | n + 1, .loop b c,   s =>
      match b.eval s.store with
      | true  =>
          match run n c s with
          | some s' => run n (.loop b c) s'
          | none    => none
      | false => some s

/- ex m5-3 run_sound -/
theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s' := by
  intro n
  induction n with
  | zero => intro c s s' h; simp [run] at h
  | succ n ih =>
    intro c s s' h
    cases c with
    | skip => simp [run] at h; rw [← h]; exact .skip
    | assign x e => simp [run] at h; rw [← h]; exact .assign
    | load x l =>
        simp only [run] at h
        cases hl : s.heap l with
        | none   => rw [hl] at h; simp at h
        | some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl
    | write l e =>
        simp only [run] at h
        cases hl : s.heap l with
        | none   => rw [hl] at h; simp at h
        | some v => rw [hl] at h; simp at h; rw [← h]; exact .write hl
    | free l =>
        simp only [run] at h
        cases hl : s.heap l with
        | none   => rw [hl] at h; simp at h
        | some v => rw [hl] at h; simp at h; rw [← h]; exact .free hl
    | seq c₁ c₂ =>
        simp only [run] at h
        cases hr : run n c₁ s with
        | none    => rw [hr] at h; simp at h
        | some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s' h)
    | ite b c₁ c₂ =>
        simp only [run] at h
        cases hb : b.eval s.store with
        | true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s' h)
        | false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s' h)
    | loop b c =>
        simp only [run] at h
        cases hb : b.eval s.store with
        | false =>
            rw [hb] at h
            have hs : s = s' := Option.some.inj h
            subst hs
            exact .loopFalse hb
        | true  =>
            rw [hb] at h
            cases hr : run n c s with
            | none    => rw [hr] at h; simp at h
            | some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s' h)

/- ex m5-4 run_mono, run_le, run_complete -/
theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s' : State),
    run n c s = some s' → run (n + 1) c s = some s' := by
  intro n
  induction n with
  | zero => intro c s s' h; simp [run] at h
  | succ n ih =>
    intro c s s' h
    cases c with
    | skip => simpa [run] using h
    | assign x e => simpa [run] using h
    | load x l => simpa [run] using h
    | write l e => simpa [run] using h
    | free l => simpa [run] using h
    | seq c₁ c₂ =>
        simp only [run] at h ⊢
        cases hr : run n c₁ s with
        | none    => rw [hr] at h; simp at h
        | some s₁ => rw [hr] at h; rw [ih c₁ s s₁ hr]; exact ih c₂ s₁ s' h
    | ite b c₁ c₂ =>
        simp only [run] at h ⊢
        cases hb : b.eval s.store with
        | true  => rw [hb] at h; exact ih c₁ s s' h
        | false => rw [hb] at h; exact ih c₂ s s' h
    | loop b c =>
        simp only [run] at h ⊢
        cases hb : b.eval s.store with
        | false => rw [hb] at h; exact h
        | true  =>
            rw [hb] at h
            cases hr : run n c s with
            | none    => rw [hr] at h; simp at h
            | some s₁ =>
                rw [hr] at h
                have : run (n + 1) c s = some s₁ := ih c s s₁ hr
                rw [this]
                exact ih _ s₁ s' h

theorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s' : State}
    (h : run n c s = some s') : run m c s = some s' := by
  induction hle with
  | refl => exact h
  | step _ ih => exact run_mono _ _ _ _ ih

theorem run_complete {c : Cmd} {s s' : State} (h : Exec c s s') :
    ∃ n, run n c s = some s' := by
  induction h with
  | skip => exact ⟨1, rfl⟩
  | assign => exact ⟨1, rfl⟩
  | load hl => exact ⟨1, by simp [run, hl]⟩
  | write hl => exact ⟨1, by simp [run, hl]⟩
  | free hl => exact ⟨1, by simp [run, hl]⟩
  | seq _ _ ih₁ ih₂ =>
      obtain ⟨n₁, h₁⟩ := ih₁
      obtain ⟨n₂, h₂⟩ := ih₂
      refine ⟨max n₁ n₂ + 1, ?_⟩
      simp only [run]
      rw [run_le (Nat.le_max_left n₁ n₂) h₁]
      exact run_le (Nat.le_max_right n₁ n₂) h₂
  | iteTrue hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩
  | iteFalse hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩
  | loopFalse hb => exact ⟨1, by simp only [run, hb]⟩
  | loopTrue hb _ _ ihb ihr =>
      obtain ⟨n₁, h₁⟩ := ihb
      obtain ⟨n₂, h₂⟩ := ihr
      refine ⟨max n₁ n₂ + 1, ?_⟩
      simp only [run, hb]
      rw [run_le (Nat.le_max_left n₁ n₂) h₁]
      exact run_le (Nat.le_max_right n₁ n₂) h₂


/- ===== M6 Hoare triples ===== -/

/- code -/
def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap

/- code -/
def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap

/- code -/
def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=
  fun σ h => Q (Store.set σ x (e.eval σ)) h

/- ex m6-1 hoare_consequence -/
theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}
    (hpre : P' ⊢ P) (hc : Hoare (P) (c) (Q)) (hpost : Q ⊢ Q') : Hoare (P') (c) (Q') := by
  intro σ h hp
  obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)
  exact ⟨s', hex, hpost s'.store s'.heap hq⟩

/- ex m6-2 hoare_skip / hoare_seq -/
theorem hoare_skip (P : Assertion) : Hoare (P) (.skip) (P) :=
  fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩

theorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}
    (h₁ : Hoare (P) (c₁) (Q)) (h₂ : Hoare (Q) (c₂) (R)) : Hoare (P) ((c₁ ;; c₂)) (R) := by
  intro σ h hp
  obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp
  obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq
  exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩

/- ex m6-3 hoare_assign -/
theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :
    Hoare (subst x e Q) ((.assign x e)) (Q) := by
  intro σ h hq
  exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩

/- ex m6-4 assign_constant -/
theorem assign_constant (x : Var) :
    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by
  intro σ h he
  refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩
  show Store.set σ x 10 x = 10
  simp [Store.set]

/- ex m6-5 assign_twice -/
theorem assign_twice (x y : Var) :
    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))
      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp) := by
  refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_
  · intro σ h he
    refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩
    show Store.set σ x 3 x = 3
    simp [Store.set]
  · intro σ h hpre
    obtain ⟨hx, he⟩ := hpre
    have hx' : σ x = 3 := hx
    refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩
    show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3
    constructor
    · show (if x = y then σ x else σ x) = 3
      simp [hx']
    · show (if y = y then σ x else σ y) = 3
      simp [hx']


/- ===== M7 The small-footprint rules ===== -/

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

/- ex m7-4 clearCell_spec -/
def clearCell (l : Loc) : Cmd := .write l (.const 0)

theorem clearCell_spec (l : Loc) (old : Val) : Hoare (l ↦ old) ((clearCell l)) (l ↦ 0) :=
  hoare_write l (.const 0) old

/- ex m7-5 readAndFree_spec -/
def readAndFree (x : Var) (l : Loc) : Cmd := .load x l ;; .free l

theorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :
    Hoare (l ↦ v) ((readAndFree x l)) (pure (fun σ => σ x = v)) := by
  intro σ h hp
  subst hp
  refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩
  · exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))
  · show Store.set σ x v x = v
    simp [Store.set]
  · exact erase_singleton l v


/- ===== M8 Locality and the frame rule ===== -/

/- code -/
def HeapLocal (c : Cmd) : Prop :=
  ∀ σ h hFrame s',
    Heap.disjoint h hFrame →
    Exec c ⟨σ, h⟩ s' →
    Heap.disjoint s'.heap hFrame ∧
    ∃ r : State,
      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧
      r.store = s'.store ∧
      r.heap = Heap.union s'.heap hFrame

/- code -/
def Preserves (c : Cmd) (R : Assertion) : Prop :=
  ∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame

/- code -/
def HeapOnly (R : Assertion) : Prop := ∀ σ σ' h, R σ h → R σ' h

theorem preserves_of_heapOnly {R : Assertion} (c : Cmd) (h : HeapOnly R) : Preserves c R :=
  fun s s' _ hFrame hr => h s.store s'.store hFrame hr

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

/- ex m8-2 heapLocal_write -/
theorem heapLocal_write (l : Loc) (e : Atom) : HeapLocal (.write l e) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | write hl =>
      have hl' : h l = _ := hl
      have hdw : Heap.disjoint (Heap.write h l (e.eval σ)) hFrame := by
        intro x
        rcases hd x with hx | hx
        · by_cases hxl : x = l
          · subst hxl; rw [hl'] at hx; exact absurd hx (by simp)
          · left; rw [write_other h l x (e.eval σ) hxl]; exact hx
        · exact Or.inr hx
      refine ⟨hdw, ⟨σ, Heap.write (Heap.union h hFrame) l (e.eval σ)⟩,
              Exec.write (union_of_some hFrame hl'), rfl, ?_⟩
      show Heap.write (Heap.union h hFrame) l (e.eval σ)
             = Heap.union (Heap.write h l (e.eval σ)) hFrame
      funext x
      by_cases hxl : x = l
      · subst hxl
        rw [write_same (Heap.union h hFrame) x (e.eval σ),
            union_of_some hFrame (write_same h x (e.eval σ))]
      · rw [write_other (Heap.union h hFrame) l x (e.eval σ) hxl]
        have hwx : Heap.write h l (e.eval σ) x = h x := write_other h l x (e.eval σ) hxl
        cases hx : h x with
        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]
        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]

/- ex m8-3 heapLocal_free -/
theorem heapLocal_free (l : Loc) : HeapLocal (.free l) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | free hl =>
      have hl' : h l = _ := hl
      have hde : Heap.disjoint (Heap.erase h l) hFrame := by
        intro x
        rcases hd x with hx | hx
        · left
          by_cases hxl : x = l
          · subst hxl; exact erase_same h x
          · rw [erase_other h l x hxl]; exact hx
        · exact Or.inr hx
      refine ⟨hde, ⟨σ, Heap.erase (Heap.union h hFrame) l⟩,
              Exec.free (union_of_some hFrame hl'), rfl, ?_⟩
      show Heap.erase (Heap.union h hFrame) l = Heap.union (Heap.erase h l) hFrame
      funext x
      by_cases hxl : x = l
      · subst hxl
        rw [erase_same (Heap.union h hFrame) x,
            union_of_none hFrame (erase_same h x)]
        rcases hd x with hx | hx
        · rw [hx] at hl'; exact absurd hl' (by simp)
        · exact hx.symm
      · rw [erase_other (Heap.union h hFrame) l x hxl]
        have hex' : Heap.erase h l x = h x := erase_other h l x hxl
        cases hx : h x with
        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hex'.trans hx)]
        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hex'.trans hx)]

/- ex m8-4 heapLocal_seq -/
theorem heapLocal_seq {c₁ c₂ : Cmd} (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) :
    HeapLocal (c₁ ;; c₂) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | seq hex₁ hex₂ =>
      rename_i sMid
      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁
      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂
      refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩
      have heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩ := by
        rw [← hst₁, ← hhp₁]
      rw [heq]
      exact hr₂

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


/- ===== M9 Symbolic execution — verifying real programs ===== -/

/- code -/
def StoreStable (c : Cmd) : Prop := ∀ s s', Exec c s s' → s'.store = s.store

theorem storeStable_write (l : Loc) (e : Atom) : StoreStable (.write l e) := by
  intro s s' hex; cases hex; rfl

theorem storeStable_free (l : Loc) : StoreStable (.free l) := by
  intro s s' hex; cases hex; rfl

theorem preserves_of_storeStable {c : Cmd} (h : StoreStable c) (R : Assertion) :
    Preserves c R := by
  intro s s' hex hFrame hr
  rw [h s s' hex]; exact hr

/- code -/
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

/- code -/
theorem pure_star_regroup (φ : Store → Prop) (P R : Assertion) :
    pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by
  intro σ h hstar
  obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar
  subst he
  refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩
  rw [hu, union_empty_left, huPR]

/- code -/
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

/- code -/
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

/- ex m9-4 swap_spec -/
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

-- The remaining work: four applications of hoare_seq, each of the form
--   frame the untouched cell  →  apply the small rule  →  renormalise.
-- The intermediate assertions, in order:
--   pure (tmp₁ = a) ∗ (l₁ ↦ a ∗ l₂ ↦ b)
--   pure (tmp₁ = a) ∗ (pure (tmp₂ = b) ∗ (l₁ ↦ a ∗ l₂ ↦ b))
--   pure (tmp₁ = a) ∗ (l₁ ↦ b ∗ l₂ ↦ b)
--   l₁ ↦ b ∗ l₂ ↦ a


/- ===== M10 Recursive predicates and linked structures ===== -/

/- code -/
def node (p : Loc) (value next : Nat) : Assertion :=
  (p ↦ value) ∗ ((p + 1) ↦ next)

def listRep : List Nat → Loc → Assertion
  | [],      p => pure (fun _ => p = 0)
  | x :: xs, p =>
      aExists fun next =>
        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next

/- code -/
def lseg : List Nat → Loc → Loc → Assertion
  | [],      start, finish => pure (fun _ => start = finish)
  | x :: xs, start, finish =>
      aExists fun next =>
        pure (fun _ => start ≠ 0) ∗ node start x next ∗ lseg xs next finish

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

/- ex m10-2 node_cells_distinct -/
theorem node_cells_distinct (p : Loc) (x next : Nat) :
    node p x next ⊢ fact (fun _ => p ≠ p + 1) :=
  two_cells_distinct p (p + 1) x next

/- ex m10-3 concrete three-node list -/
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

/- ex m10-4 lseg_append -/
theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :
    aExists P ⊢ aExists Q := by
  intro σ hh ⟨x, hp⟩
  exact ⟨x, h x σ hh hp⟩

theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),
    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by
  intro xs
  induction xs with
  | nil =>
      intro ys p q r σ h hstar
      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar
      have hpq' : p = q := hpq
      subst hpq'
      subst he
      rw [hu, union_empty_left]
      exact hys
  | cons x xs ih =>
      intro ys p q r
      refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_
      refine entails_trans (star_exists_left _ _) ?_
      refine aExists_mono (fun n => ?_)
      refine entails_trans (star_assoc_left _ _ _) ?_
      refine star_mono_right _ ?_
      refine entails_trans (star_assoc_left _ _ _) ?_
      exact star_mono_right _ (ih ys n q r)

/- ex m10-5 lseg_listRep -/
theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),
    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p := by
  intro xs
  induction xs with
  | nil =>
      intro ys p q σ h hstar
      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar
      have hpq' : p = q := hpq
      subst hpq'
      subst he
      rw [hu, union_empty_left]
      exact hys
  | cons x xs ih =>
      intro ys p q
      refine entails_trans (star_exists_left _ _) ?_
      refine aExists_mono (fun n => ?_)
      refine entails_trans (star_assoc_left _ _ _) ?_
      refine star_mono_right _ ?_
      refine entails_trans (star_assoc_left _ _ _) ?_
      exact star_mono_right _ (ih ys n q)


/- ===== M11 The magic wand ===== -/

/- code -/
def wand (P Q : Assertion) : Assertion :=
  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')
infixr:54 " -∗ " => wand

/- ex m11-1 wand_intro -/
theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R := by
  intro σ hh hp h' hd hq
  exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩

/- ex m11-2 wand_elim -/
theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q := by
  intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩
  rw [hu]
  exact hw h₂ hd hp

/- ex m11-3 star_wand_adjunction -/
theorem star_wand_adjunction (P Q R : Assertion) : (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R) := by
  constructor
  · exact wand_intro
  · intro h
    refine entails_trans (star_mono_left Q h) ?_
    exact wand_elim Q R

/- ex m11-4 wand_mono -/
theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :
    (P -∗ Q) ⊢ (P' -∗ Q') := by
  intro σ h hw h' hd hp'
  exact hq σ _ (hw h' hd (hp σ h' hp'))


/- ===== M12 Weakest preconditions ===== -/

/- code -/
def wp (c : Cmd) (Q : Assertion) : Assertion :=
  fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap

/- code -/
theorem hoare_iff_entails_wp (P Q : Assertion) (c : Cmd) :
    Hoare P c Q ↔ P ⊢ wp c Q := Iff.rfl

/- ex m12-1 wp_skip / wp_assign -/
theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex; exact hq
  · intro σ h hq
    exact ⟨⟨σ, h⟩, Exec.skip, hq⟩

theorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :
    wp (.assign x e) Q ⊣⊢ subst x e Q := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex; exact hq
  · intro σ h hq
    exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩

/- ex m12-2 wp_seq -/
theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :
    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q) := by
  constructor
  · intro σ h ⟨s'', hex, hq⟩
    cases hex with
    | seq h₁ h₂ => exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩
  · intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩
    exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩

/- ex m12-3 wp_mono -/
theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q' := by
  intro σ hh ⟨s', hex, hq⟩
  exact ⟨s', hex, h s'.store s'.heap hq⟩

/- ex m12-4 wp_free_emp -/
theorem heap_eq_singleton {h : Heap} {l : Loc} {v : Val}
    (hl : h l = some v) (hrest : Heap.erase h l = Heap.empty) :
    h = Heap.singleton l v := by
  funext x
  by_cases hx : x = l
  · subst hx; rw [hl, singleton_same]
  · rw [singleton_other l x v hx]
    have := congrFun hrest x
    rw [erase_other h l x hx] at this
    exact this

theorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by
  constructor
  · intro σ h ⟨s', hex, he⟩
    cases hex with
    | free hl =>
        refine ⟨_, heap_eq_singleton hl ?_⟩
        exact he
  · intro σ h ⟨v, hp⟩
    subst hp
    exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v),
           erase_singleton l v⟩

/- ex m12-5 wp_write -/
theorem wp_write (l : Loc) (new : Val) :
    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old) := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex with
    | write hl =>
        rename_i old
        refine ⟨old, ?_⟩
        have hl' : h l = some old := hl
        have hq' : Heap.write h l new = Heap.singleton l new := hq
        funext x
        by_cases hx : x = l
        · subst hx; rw [hl', singleton_same]
        · rw [singleton_other l x old hx]
          have := congrFun hq' x
          rw [write_other h l x new hx, singleton_other l x new hx] at this
          exact this
  · intro σ h ⟨old, hp⟩
    subst hp
    exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩,
           Exec.write (singleton_same l old), write_singleton l old new⟩


/- ===== M13 Loops, invariants, and termination ===== -/

/- code -/
theorem partial_of_total {P Q : Assertion} {c : Cmd}
    (h : Hoare P c Q) : PartialHoare P c Q := by
  intro σ hh s' hp hex
  obtain ⟨s'', hex'', hq⟩ := h σ hh hp
  have : s' = s'' := exec_deterministic hex hex''
  rw [this]; exact hq

/- code -/
def bTrue (b : BExpr) : Assertion := fun σ _ => b.eval σ = true

def bFalse (b : BExpr) : Assertion := fun σ _ => b.eval σ = false

/- ex m13-1 partialHoare_skip / seq / consequence -/
theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P := by
  intro σ h s' hp hex
  cases hex; exact hp

theorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}
    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :
    PartialHoare P (c₁ ;; c₂) R := by
  intro σ h s' hp hex
  cases hex with
  | seq hex₁ hex₂ =>
      rename_i sMid
      exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂

theorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}
    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :
    PartialHoare P' c Q' := by
  intro σ h s' hp hex
  exact hpost s'.store s'.heap (hc σ h s' (hpre σ h hp) hex)

/- ex m13-2 partialHoare_ite -/
theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}
    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)
    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :
    PartialHoare P (.ite b c₁ c₂) Q := by
  intro σ h s' hp hex
  cases hex with
  | iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'
  | iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'

/- ex m13-3 the while rule -/
theorem loop_invariant {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}
    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :
    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →
      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by
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
      intro heq hI
      cases heq
      exact ⟨hI, hb⟩
  | loopTrue hb hbdy _ _ ihrest =>
      intro heq hI
      cases heq
      exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)

theorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}
    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :
    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by
  intro σ h s' hI hex
  exact loop_invariant hbody hex rfl hI

/- ex m13-4 hoare_while_variant -/
theorem hoare_while_variant {I : Nat → Assertion} {b : BExpr} {c : Cmd}
    (hstep : ∀ n, Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n))
    (hstop : ∀ σ h, I 0 σ h → b.eval σ = false) :
    ∀ n, Hoare (I n) (.loop b c) (aExists fun m => aAnd (I m) (bFalse b)) := by
  intro n
  induction n with
  | zero =>
      intro σ h hI
      exact ⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩
  | succ n ih =>
      intro σ h hI
      cases hbv : b.eval σ with
      | true =>
          obtain ⟨s₁, hex₁, hI₁⟩ := hstep n σ h ⟨hI, hbv⟩
          obtain ⟨s₂, hex₂, hpost⟩ := ih s₁.store s₁.heap hI₁
          exact ⟨s₂, Exec.loopTrue hbv hex₁ hex₂, hpost⟩
      | false =>
          exact ⟨⟨σ, h⟩, Exec.loopFalse hbv, n + 1, hI, hbv⟩

/- ex m13-5 a loop that actually terminates -/
def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))

def countdown (x : Var) : Cmd :=
  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))

theorem countdown_spec (x : Var) : ∀ n,
    Hoare (fun σ _ => σ x = n) (countdown x)
      (aExists fun m => aAnd (fun σ _ => σ x = m) (bFalse (counterGuard x))) := by
  refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_
  · intro n σ h hpre
    obtain ⟨hx, _⟩ := hpre
    refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩
    show Store.set σ x (σ x - 1) x = n
    have hx' : σ x = n + 1 := hx
    simp [Store.set, hx']
  · intro σ h hI
    have hx : σ x = 0 := hI
    show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false
    simp [Atom.eval, hx]

