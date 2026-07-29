/- Everything defined and proved UP TO AND INCLUDING M2.
   Verified with Lean 4.32.2, no imports, no Mathlib. -/

abbrev Loc   := Nat
abbrev Val   := Nat
abbrev Heap  := Loc → Option Val
abbrev Var   := Nat
abbrev Store := Var → Val

abbrev Assertion := Store → Heap → Prop

theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp

theorem exists_example : ∃ n : Nat, n = 3 := ⟨3, rfl⟩

theorem function_extensionality {f g : Nat → Nat}
    (h : ∀ x, f x = g x) : f = g := funext h

def update (f : Nat → Nat) (x value : Nat) : Nat → Nat :=
  fun y => if y = x then value else f y

theorem update_same (f : Nat → Nat) (x value : Nat) :
    update f x value x = value := by
  simp [update]

theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :
    update f x value y = f y := by
  simp [update, hne]

theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x <;> simp [update, h]

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

namespace Heap

def empty : Heap := fun _ => none

def singleton (l : Loc) (v : Val) : Heap :=
  fun x => if x = l then some v else none

def write (h : Heap) (l : Loc) (v : Val) : Heap :=
  fun x => if x = l then some v else h x

def erase (h : Heap) (l : Loc) : Heap :=
  fun x => if x = l then none else h x

end Heap

theorem singleton_same (l : Loc) (v : Val) :
    Heap.singleton l v l = some v := by
  simp [Heap.singleton]

theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.singleton l v x = none := by
  simp [Heap.singleton, hne]

theorem write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.write h l v l = some v := by
  simp [Heap.write]

theorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.write h l v x = h x := by
  simp [Heap.write, hne]

theorem erase_same (h : Heap) (l : Loc) :
    Heap.erase h l l = none := by
  simp [Heap.erase]

theorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :
    Heap.erase h l x = h x := by
  simp [Heap.erase, hne]

theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, hx]

theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.erase (Heap.write h l v) l = Heap.erase h l := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]

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

theorem write_singleton (l : Loc) (v w : Val) :
    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]

theorem erase_singleton (l : Loc) (v : Val) :
    Heap.erase (Heap.singleton l v) l = Heap.empty := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]

def Heap.disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ l, h₁ l = none ∨ h₂ l = none

def Heap.union (h₁ h₂ : Heap) : Heap :=
  fun l =>
    match h₁ l with
    | some v => some v
    | none   => h₂ l

def Heap.splits (whole left right : Heap) : Prop :=
  Heap.disjoint left right ∧ whole = Heap.union left right

theorem disjoint_symm {h₁ h₂ : Heap} : Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁ := by
  intro hd l
  exact (hd l).symm

theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=
  fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty :=
  fun _ => Or.inr rfl

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

theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext l; rfl

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none Heap.empty hl]; rfl
  | some v => rw [union_of_some Heap.empty hl]

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

theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h :=
  ⟨disjoint_empty_left h, (union_empty_left h).symm⟩

theorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁ := by
  intro ⟨hd, he⟩
  exact ⟨disjoint_symm hd, by rw [he, union_comm hd]⟩

theorem splits_assoc {h hPQ hP hQ hR : Heap}
    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :
    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by
  obtain ⟨hd₁, he₁⟩ := h1
  obtain ⟨hd₂, he₂⟩ := h2
  subst he₂
  obtain ⟨hPR, hQR'⟩ := disjoint_union_left.mp hd₁
  refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩
  rw [he₁, union_assoc]
