/- ===== Unit 00 · `aliasing` · The rule that is false ===== -/

abbrev Loc   := Nat
abbrev Val   := Nat
abbrev Heap  := Loc → Option Val
abbrev Var   := Nat
abbrev Store := Var → Val

def aliasedAfter : Heap := fun x => if x = 4 then some 5 else none

/- ex x01 write a heap, prove a lookup -/
def twoAllocated : Heap := fun x => if x = 4 then some 5 else if x = 9 then some 2 else none

example : twoAllocated 7 = none := by
  simp [twoAllocated]

/- ex x02 aliasedAfter — the aliased postcondition is unsatisfiable -/
example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5) := by
  intro ⟨h3, _⟩
  simp [aliasedAfter] at h3

/- ===== Unit 01 · `terms` · Propositions are types, proofs are terms ===== -/

theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp

theorem exists_example : ∃ n : Nat, n = 3 := ⟨3, rfl⟩

theorem exists_three : ∃ n : Nat, n + 1 = 4 := ⟨3, rfl⟩

theorem two_add_two : 2 + 2 = 4 := rfl

theorem mp (P Q : Prop) : P → (P → Q) → Q := fun hp hpq => hpq hp

/- ex x03 comp -/
theorem comp (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := fun hp => g (f hp)

/- ex x04 and_comm' / or_comm' -/
theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := fun h => ⟨h.2, h.1⟩

theorem or_comm' (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim Or.inr Or.inl

theorem and_comm_tac (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

theorem or_comm_tac (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hp | hq
  · right; exact hp
  · left;  exact hq

/- ex x05 exists_mono -/
theorem exists_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) :
    (∃ n, P n) → ∃ n, Q n := by
  intro hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨n, h n hn⟩

/- ex x06 nested_pack / nested_unpack -/
theorem nested_pack {P Q : Nat → Prop} {a b : Nat} (hp : P a) (hq : Q b) :
    ∃ x y, x = a ∧ y = b ∧ P x ∧ Q y :=
  ⟨a, b, rfl, rfl, hp, hq⟩

theorem nested_unpack {P Q : Nat → Prop} (h : ∃ x y, P x ∧ Q y ∧ x = y) :
    ∃ z, P z ∧ Q z := by
  obtain ⟨x, y, hpx, hqy, hxy⟩ := h
  simp [hxy] at hpx
  exact ⟨y, hpx, hqy⟩

/- ===== Unit 02 · `compute` · Equality, computation, and the limits of `rfl` ===== -/

theorem rw_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

theorem calc_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a = b := h1
    _ = c := h2

def double (n : Nat) : Nat := n + n

abbrev double' (n : Nat) : Nat := n + n

/- ex x07 double -/
theorem double'_unfold (n : Nat) : double' n = n + n := rfl

theorem double'_three : double' 3 = 6 := rfl

theorem double_unfold (n : Nat) : double n = n + n := by
  simp [double]

theorem double_zero_left (n : Nat) : double n = 0 + n + n := by
  simp [double]

/- ex x08 some_inj / some_ne_none -/
theorem some_inj (v w : Val) (h : some v = some w) : v = w :=
  Option.some.inj h

theorem some_ne_none (v : Val) : some v ≠ none := by
  simp

theorem some_ne_none' (v : Val) : some v ≠ none := by
  intro h
  cases h

def defined (h : Heap) (l : Loc) : Prop := ∃ v, h l = some v

/- ex x09 defined -/
theorem defined_of_ne_none (h : Heap) (l : Loc) (hne : h l ≠ none) : defined h l := by
  cases hl : h l with
  | none   => exact absurd hl hne
  | some v => exact ⟨v, hl⟩

/- ===== Unit 03 · `funext` · Functions as values ===== -/

theorem function_extensionality {f g : Nat → Nat}
    (h : ∀ x, f x = g x) : f = g := funext h

def twice (f : Nat → Nat) : Nat → Nat := fun n => f (f n)

theorem twice_succ : twice (fun n => n + 1) = fun n => n + 2 := by
  funext n
  rfl

theorem apply_eq {f g : Nat → Nat} (h : f = g) (n : Nat) : f n = g n :=
  congrFun h n

/- ex x10 funext_drill -/
theorem funext_drill : (fun n : Nat => 0 + n) = (fun n => n) := by
  funext n
  simp

/- ex x11 if_drill -/
theorem if_drill (f : Nat → Nat) (a b : Nat) (hab : a ≠ b) :
    (if a = a then f a else f b) = f a ∧ (if b = a then f a else f b) = f b := by
  constructor
  · rw [if_pos rfl]
  · rw [if_neg (Ne.symm hab)]

/- ex x12 by_cases_drill -/
theorem by_cases_drill (f : Nat → Nat) (x y : Nat) :
    (if y = x then f x else f y) = f y := by
  by_cases h : y = x <;> simp [h]

/- ===== Unit 04 · `update` · LAB — the update family ===== -/

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

/- ex x13 update_idem -/
theorem update_idem (f : Nat → Nat) (x : Nat) : update f x (f x) = f := by
  funext y
  by_cases h : y = x <;> simp [update, h]

/- ===== Unit 05 · `heap` · Memory as a partial function ===== -/

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

/- ===== Unit 06 · `heap-laws` · LAB — equations between heaps ===== -/

theorem heap_ext {h₁ h₂ : Heap} (h : ∀ l, h₁ l = h₂ l) : h₁ = h₂ := funext h

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

/- the counterexample shown beside write_comm, when the disequality is dropped -/
example : ¬ ∀ (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val),
    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by
  intro hc
  have hbad := congrFun (hc Heap.empty 0 0 1 2) 0
  simp [Heap.write] at hbad

/- ex m1-8 write_singleton / erase_singleton -/
theorem write_singleton (l : Loc) (v w : Val) :
    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]

theorem erase_singleton (l : Loc) (v : Val) :
    Heap.erase (Heap.singleton l v) l = Heap.empty := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]

/- ex x14 erase_erase / write_of_eq -/
theorem erase_erase (h : Heap) (l : Loc) :
    Heap.erase (Heap.erase h l) l = Heap.erase h l := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, hx]

theorem write_of_eq {h : Heap} {l : Loc} {v : Val} (hl : h l = some v) :
    Heap.write h l v = h := by
  funext x
  by_cases hx : x = l
  · rw [hx, write_same]
    exact hl.symm
  · rw [write_other h l x v hx]

/- ex x15 erase_write_comm, and the refutation of the unconditional claim -/
theorem erase_write_comm (h : Heap) (l l' : Loc) (v : Val) (hne : l ≠ l') :
    Heap.erase (Heap.write h l v) l' = Heap.write (Heap.erase h l') l v := by
  funext x
  simp only [Heap.write, Heap.erase]
  by_cases hx : x = l'
  · have hxl : x ≠ l := by rw [hx]; exact fun hc => hne hc.symm
    rw [if_pos hx, if_neg hxl, if_pos hx]
  · by_cases hxl : x = l
    · rw [if_neg hx, if_pos hxl, if_pos hxl]
    · rw [if_neg hx, if_neg hxl, if_neg hxl, if_neg hx]

example : ¬ ∀ (h : Heap) (l l' : Loc) (v : Val),
    Heap.erase (Heap.write h l v) l' = Heap.write (Heap.erase h l') l v := by
  intro hc
  have hbad := congrFun (hc Heap.empty 0 0 7) 0
  simp [Heap.erase, Heap.write] at hbad

theorem write_erase_same (h : Heap) (l : Loc) (v : Val) :
    Heap.write (Heap.erase h l) l v = Heap.write h l v := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.erase, hx]

theorem erase_comm (h : Heap) (l₁ l₂ : Loc) :
    Heap.erase (Heap.erase h l₁) l₂ = Heap.erase (Heap.erase h l₂) l₁ := by
  funext x
  by_cases h₁ : x = l₁ <;> by_cases h₂ : x = l₂ <;> simp [Heap.erase, h₁, h₂]

theorem write_empty (l : Loc) (v : Val) :
    Heap.write Heap.empty l v = Heap.singleton l v := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.empty, Heap.singleton, hx]

/- ===== Unit 07 · `footprint` · How much do you own? ===== -/

def ptsAtLeast (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h l = some v
def ptsExactly (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h = Heap.singleton l v

def twoCells : Heap := Heap.write (Heap.singleton 4 3) 9 7

/- ex x16 a two cell heap satisfies the loose reading -/
example : ptsAtLeast 4 3 (fun _ => 0) twoCells := by
  have hne : (4 : Loc) ≠ 9 := by simp
  show twoCells 4 = some 3
  unfold twoCells
  rw [write_other (Heap.singleton 4 3) 9 4 7 hne, singleton_same]

/- ex x17 it does not satisfy the exact reading -/
example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by
  intro h
  have hne : (9 : Loc) ≠ 4 := by simp
  have h9 := congrFun h 9
  unfold twoCells at h9
  rw [write_same, singleton_other 4 9 3 hne] at h9
  exact some_ne_none 7 h9

/- ex x18 after `free`, the heap is not empty -/
example : Heap.erase twoCells 4 ≠ Heap.empty := by
  intro h
  have hne : (9 : Loc) ≠ 4 := by simp
  have h9 := congrFun h 9
  rw [erase_other twoCells 4 9 hne] at h9
  unfold twoCells at h9
  rw [write_same] at h9
  exact some_ne_none 7 h9

/- ===== Unit 08 · `disjoint` · Disjointness ===== -/

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

/- ex m2-2 disjoint_empty_left / disjoint_empty_right -/
theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=
  fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty :=
  fun _ => Or.inr rfl

/- ex m2-3 singleton_disjoint / singleton_disjoint_iff -/
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
      · rw [singleton_same] at h; cases h
  · exact singleton_disjoint v₁ v₂

/- ex x19 self_disjoint_iff_empty -/
theorem self_disjoint_iff_empty (h : Heap) : Heap.disjoint h h ↔ h = Heap.empty := by
  constructor
  · intro hd
    funext l
    rcases hd l with h1 | h1 <;> exact h1
  · intro he l
    subst he
    exact Or.inl rfl

/- ===== Unit 09 · `union` · Union, and why it must be total ===== -/

/- ex x20 union_of_none / union_of_some -/
theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :
    Heap.union h₁ h₂ l = h₂ l := by
  simp [Heap.union, hl]

theorem union_of_some {h₁ : Heap} (h₂ : Heap) {l : Loc} {v : Val} (hl : h₁ l = some v) :
    Heap.union h₁ h₂ l = some v := by
  simp [Heap.union, hl]

/- ex x21 union_eq_none -/
theorem union_eq_none {h₁ h₂ : Heap} {l : Loc} :
    Heap.union h₁ h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by
  constructor
  · intro h
    cases hl : h₁ l with
    | none   => exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩
    | some v => rw [union_of_some h₂ hl] at h; exact absurd h (by simp)
  · intro ⟨ha, hb⟩
    rw [union_of_none h₂ ha]; exact hb

/- ex m2-4 union_empty_left / union_empty_right -/
theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext l; rfl

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none Heap.empty hl]; rfl
  | some v => rw [union_of_some Heap.empty hl]

/- ex x22 union_self -/
theorem union_self (h : Heap) : Heap.union h h = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none h hl]; exact hl
  | some v => rw [union_of_some h hl]

/- ===== Unit 10 · `pcm` · The partial commutative monoid ===== -/

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

/- ex m2-7 disjoint_union_left / disjoint_union_right -/
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

structure PCM (M : Type) where
  op         : M → M → M
  unit       : M
  valid      : M → M → Prop
  op_comm    : ∀ a b, valid a b → op a b = op b a
  op_assoc   : ∀ a b c, op (op a b) c = op a (op b c)
  unit_left  : ∀ a, op unit a = a
  valid_unit : ∀ a, valid unit a
  valid_comm : ∀ a b, valid a b → valid b a

/- ex x23 heapPCM -/
def heapPCM : PCM Heap where
  op         := Heap.union
  unit       := Heap.empty
  valid      := Heap.disjoint
  op_comm    := fun _ _ hd => union_comm hd
  op_assoc   := union_assoc
  unit_left  := union_empty_left
  valid_unit := disjoint_empty_left
  valid_comm := fun _ _ hd => disjoint_symm hd

/- ex x24 union_cancel_left -/
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

/- ===== Unit 11 · `splits` · LAB — splitting a heap ===== -/

/- ex x25 splits_empty_right -/
theorem splits_empty_right (h : Heap) : Heap.splits h h Heap.empty :=
  ⟨disjoint_empty_right h, (union_empty_right h).symm⟩

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

/- ex x26 union_not_comm -/
theorem union_not_comm :
    ¬ ∀ h₁ h₂ : Heap, Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  intro h
  have h0 := congrFun (h (Heap.singleton 0 4) (Heap.singleton 0 7)) 0
  rw [union_of_some (Heap.singleton 0 7) (singleton_same 0 4),
      union_of_some (Heap.singleton 0 4) (singleton_same 0 7)] at h0
  exact absurd h0 (by simp)

/- ===== Unit 12 · `assertions` · Assertions and entailment ===== -/

abbrev Assertion := Store → Heap → Prop

def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h
infix:40 " ⊢ " => Entails

def AssertionEquiv (P Q : Assertion) : Prop := Entails P Q ∧ Entails Q P
infix:40 " ⊣⊢ " => AssertionEquiv

def aTrue  : Assertion := fun _ _ => True

def aFalse : Assertion := fun _ _ => False

def aAnd (P Q : Assertion) : Assertion := fun σ h => P σ h ∧ Q σ h

def aOr  (P Q : Assertion) : Assertion := fun σ h => P σ h ∨ Q σ h

def aExists {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∃ x, P x σ h

def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ

/- ex m3-2 entails_refl / entails_trans -/
theorem entails_refl (P : Assertion) : P ⊢ P := fun _ _ hp => hp

theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun σ h hp => h₂ σ h (h₁ σ h hp)

/- ex m3-3 and_left / and_right / and_intro -/
theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1

theorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2

theorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=
  fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩

/- ex x27 or_left / or_right / or_elim -/
theorem or_left (P Q : Assertion) : P ⊢ aOr P Q := fun _ _ hp => Or.inl hp
theorem or_right (P Q : Assertion) : Q ⊢ aOr P Q := fun _ _ hq => Or.inr hq
theorem or_elim {P Q R : Assertion} (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : aOr P Q ⊢ R := by
  intro σ h hpq
  rcases hpq with hp | hq
  · exact h₁ σ h hp
  · exact h₂ σ h hq

/- ex x28 equiv_refl / equiv_symm / equiv_trans -/
theorem equiv_refl (P : Assertion) : P ⊣⊢ P := ⟨entails_refl P, entails_refl P⟩

theorem equiv_symm {P Q : Assertion} (h : P ⊣⊢ Q) : Q ⊣⊢ P := ⟨h.2, h.1⟩

theorem equiv_trans {P Q R : Assertion} (h₁ : P ⊣⊢ Q) (h₂ : Q ⊣⊢ R) : P ⊣⊢ R :=
  ⟨entails_trans h₁.1 h₂.1, entails_trans h₂.2 h₁.2⟩

/- ex x29 and_comm_iff / and_assoc_iff -/
theorem and_comm_iff (P Q : Assertion) : aAnd P Q ⊣⊢ aAnd Q P :=
  ⟨fun _ _ hp => ⟨hp.2, hp.1⟩, fun _ _ hp => ⟨hp.2, hp.1⟩⟩

theorem and_assoc_iff (P Q R : Assertion) : aAnd P (aAnd Q R) ⊣⊢ aAnd (aAnd P Q) R :=
  ⟨fun _ _ hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩, fun _ _ hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩

/- ===== Unit 13 · `pointsto` · `emp`, `↦`, and exact ownership ===== -/

def emp : Assertion := fun _ h => h = Heap.empty

def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v
infix:60 " ↦ " => pointsTo

/- ex m3-1 pointsTo_value_unique / pointsTo_not_emp -/
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

/- ex x30 emp as nothing anywhere -/
theorem emp_iff_all_none : emp ⊣⊢ fun _ h => ∀ l, h l = none := by
  constructor
  · intro σ h hp l
    rw [hp]
    simp [Heap.empty]
  · intro σ h hp
    funext l
    simp [Heap.empty, hp l]

/- ===== Unit 14 · `star` · Separating conjunction, and what it cannot do ===== -/

def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂
infixr:55 " ∗ " => star

/- ex x31 star_intro -/
theorem star_intro {P Q : Assertion} {σ : Store} {h h₁ h₂ : Heap}
    (hd : Heap.disjoint h₁ h₂) (hu : h = Heap.union h₁ h₂)
    (hp : P σ h₁) (hq : Q σ h₂) : (P ∗ Q) σ h :=
  ⟨h₁, h₂, hd, hu, hp, hq⟩

/- ex x32 star_same_loc_absurd -/
theorem star_same_loc_absurd (l : Loc) (v₁ v₂ : Val) :
    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact ((singleton_disjoint_iff v₁ v₂).mp hd) rfl

theorem star_pointsTo_same_false (l : Loc) (v₁ v₂ : Val) :
    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact absurd ((singleton_disjoint_iff v₁ v₂).mp hd) (by simp)

/- ex x33 no_star_weakening -/
theorem no_star_weakening : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)) := by
  intro hall
  have h := hall (fun _ => 0) (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7))
    ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl, rfl⟩
  have h1 := congrFun h 1
  rw [union_of_none (Heap.singleton 1 7) (singleton_other 0 1 4 (by simp)),
      singleton_same, singleton_other 0 1 4 (by simp)] at h1
  exact absurd h1 (by simp)

/- ex x34 no_star_duplication -/
theorem no_star_duplication : ¬ (∀ P : Assertion, P ⊢ P ∗ P) := by
  intro hall
  obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hall (4 ↦ 7) (fun _ => 0) (Heap.singleton 4 7) rfl
  have e1 : h₁ = Heap.singleton 4 7 := hp
  have e2 : h₂ = Heap.singleton 4 7 := hq
  subst e1; subst e2
  exact ((singleton_disjoint_iff 7 7).mp hd) rfl

def starNoDisj (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂

/- ex x35 starNoDisj_dup -/
theorem starNoDisj_dup (P : Assertion) : P ⊢ starNoDisj P P := by
  intro σ h hp
  exact ⟨h, h, (union_self h).symm, hp, hp⟩

/- ===== Unit 15 · `star-algebra` · LAB — the laws of `∗` ===== -/

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

/- ex m4-5 star_mono / star_mono_left / star_mono_right -/
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

def aForall {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∀ x, P x σ h

theorem star_forall_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aForall P ∗ Q ⊢ aForall (fun x => P x ∗ Q) := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩ x
  exact ⟨h₁, h₂, hd, hu, hp x, hq⟩

def Pcx : Bool → Assertion
  | false => (0 ↦ 4)
  | true  => (1 ↦ 7)

theorem star_forall_right_fails :
    ¬ (aForall (fun x => Pcx x ∗ aTrue) ⊢ aForall Pcx ∗ aTrue) := by
  intro hcontra
  have hlhs : aForall (fun x => Pcx x ∗ aTrue) (fun _ => 0)
      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) := by
    intro x
    cases x with
    | false =>
        exact ⟨Heap.singleton 0 4, Heap.singleton 1 7,
          singleton_disjoint 4 7 (by simp), rfl, rfl, trivial⟩
    | true =>
        refine ⟨Heap.singleton 1 7, Heap.singleton 0 4,
          singleton_disjoint 7 4 (by simp), ?_, rfl, trivial⟩
        exact union_comm (singleton_disjoint 4 7 (by simp))
  obtain ⟨h₁, h₂, _, _, hall, _⟩ := hcontra _ _ hlhs
  have e0 : h₁ = Heap.singleton 0 4 := hall false
  have e1 : h₁ = Heap.singleton 1 7 := hall true
  have : Heap.singleton 0 4 0 = Heap.singleton 1 7 0 := by rw [← e0, ← e1]
  rw [singleton_same, singleton_other 1 0 7 (by simp)] at this
  exact absurd this (by simp)

/- ex x36 star_emp_left_iff / star_emp_right_iff / star_comm_iff / star_congr -/
theorem star_emp_left_iff (P : Assertion) : emp ∗ P ⊣⊢ P :=
  ⟨star_emp_left P, star_emp_left_intro P⟩

theorem star_emp_right_iff (P : Assertion) : P ∗ emp ⊣⊢ P :=
  ⟨star_emp_right P, star_emp_right_intro P⟩

theorem star_comm_iff (P Q : Assertion) : P ∗ Q ⊣⊢ Q ∗ P :=
  ⟨star_comm P Q, star_comm Q P⟩

theorem star_congr {P P' Q Q' : Assertion} (hp : P ⊣⊢ P') (hq : Q ⊣⊢ Q') :
    P ∗ Q ⊣⊢ P' ∗ Q' :=
  ⟨star_mono hp.1 hq.1, star_mono hp.2 hq.2⟩

-- ∗ has no projection: the substructural fact, made into a theorem
theorem star_not_weakening : ¬ (∀ P Q : Assertion, P ∗ Q ⊢ P) := by
  intro hbad
  have h : (emp ∗ (0 ↦ 0)) ⊢ emp := hbad emp (0 ↦ 0)
  have h2 : (0 ↦ 0) ⊢ emp := entails_trans (star_emp_left_intro _) h
  exact pointsTo_not_emp 0 0 h2

/- ===== Unit 16 · `star-assoc` · Associativity ===== -/

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

/- ex x37 star_assoc_iff -/
theorem star_assoc_iff (P Q R : Assertion) : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) :=
  ⟨star_assoc_left P Q R, star_assoc_right P Q R⟩

/- ===== Unit 17 · `pure` · Propositions inside a `∗`, and the toolkit ===== -/

def pure (φ : Store → Prop) : Assertion := aAnd (fact φ) emp

/- ex m4-7 two_cells_distinct -/
theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :
    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact (singleton_disjoint_iff v₁ v₂).mp hd

/- ex m4-8 star_swap_middle / star_rotate_left / star_rotate_right / star_pure_left / star_pure_right -/
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

/- ex x38 star_or_right / star_exists_right -/
theorem star_or_right (P Q R : Assertion) : aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by
  intro σ h hor
  rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inl hp, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inr hq, hr⟩

theorem star_exists_right {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aExists (fun x => P x ∗ Q) ⊢ aExists P ∗ Q := by
  intro σ h ⟨x, h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩

/- ===== Unit 18 · `language` · A language that can get memory wrong ===== -/

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

inductive BExpr where
  | equals : Atom → Atom → BExpr
  | not    : BExpr → BExpr

def BExpr.eval (σ : Store) : BExpr → Bool
  | .equals a b => a.eval σ == b.eval σ
  | .not b      => !(b.eval σ)

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

/- ex x39 @Store.set = @update, storeSet_same, storeSet_other -/
example : @Store.set = @update := rfl

theorem storeSet_same (σ : Store) (x : Var) (v : Val) : Store.set σ x v x = v := update_same σ x v
theorem storeSet_other (σ : Store) (x y : Var) (v : Val) (hne : y ≠ x) :
    Store.set σ x v y = σ y := update_other σ x y v hne

/- ex x40 Atom evaluation and truncated subtraction -/
example : (Atom.plus (.var 0) (.minus (.var 1) (.const 2))).eval (Store.set (fun _ => 0) 1 9) = 7 := rfl

example (σ : Store) : (Atom.minus (.const 3) (.const 5)).eval σ = 0 := rfl

/- ex x41 Atom.size -/
def Atom.size : Atom → Nat
  | .const _ => 1
  | .var _ => 1
  | .plus a b => a.size + b.size + 1
  | .minus a b => a.size + b.size + 1

example : (Atom.plus (.const 1) (.var 0)).size = 3 := rfl

/- ===== Unit 19 · `exec` · Running a command is a relation ===== -/

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

/- ex x42 exec_assign_inv / exec_load_inv -/
theorem exec_assign_inv {x : Var} {e : Atom} {s s' : State} (h : Exec (.assign x e) s s') :
    s' = ⟨Store.set s.store x (e.eval s.store), s.heap⟩ := by
  cases h; rfl

theorem exec_load_inv {x : Var} {l : Loc} {s s' : State} (h : Exec (.load x l) s s') :
    ∃ v, s.heap l = some v ∧ s' = ⟨Store.set s.store x v, s.heap⟩ := by
  cases h with
  | load hl => exact ⟨_, hl, rfl⟩

/- ex x43 exec_load_stuck -/
theorem exec_load_stuck (x : Var) (l : Loc) (σ : Store) (s' : State) :
    ¬ Exec (.load x l) ⟨σ, Heap.empty⟩ s' := by
  intro hex
  cases hex with
  | load hl => exact absurd hl (by simp [Heap.empty])

/- ex x44 exec_skip_seq_inv -/
theorem exec_skip_seq_inv {c : Cmd} {s s' : State} (h : Exec (.skip ;; c) s s') : Exec c s s' := by
  cases h with
  | seq h₁ h₂ => cases h₁; exact h₂

/- ===== Unit 20 · `induction` · Structural induction, up to derivations ===== -/

def allZeros : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: allZeros n

/- ex x45 allZeros_length / append_nil -/
theorem allZeros_length (n : Nat) : (allZeros n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allZeros, ih]

theorem append_nil (xs : List Nat) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp

/- ex x46 exec_id -/
theorem exec_id {c : Cmd} {s s' : State} (h : Exec c s s') : Exec c s s' := by
  induction h with
  | skip => exact .skip
  | assign => exact .assign
  | load hl => exact .load hl
  | write hl => exact .write hl
  | free hl => exact .free hl
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue hb _ ih => exact .iteTrue hb ih
  | iteFalse hb _ ih => exact .iteFalse hb ih
  | loopFalse hb => exact .loopFalse hb
  | loopTrue hb _ _ ihb ihr => exact .loopTrue hb ihb ihr

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

/- ===== Unit 21 · `interpreter` · LAB — an interpreter, proved to agree (OPTIONAL) ===== -/

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

def demoProg : Cmd := .load 0 3 ;; .write 3 (.plus (.var 0) (.const 1))

def demoStart : State := ⟨fun _ => 0, Heap.singleton 3 7⟩

/- ex x47 run_example -/
example : run 6 demoProg demoStart
    = some ⟨Store.set demoStart.store 0 7, Heap.write demoStart.heap 3 8⟩ := by rfl

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

/- ex m5-4 run_mono / run_le / run_complete -/
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

def spin : Cmd := .loop (.not (.equals (.const 0) (.const 1))) .skip

theorem run_spin_none : ∀ (n : Nat) (s : State), run n spin s = none := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      show (match run n Cmd.skip s with
            | some s' => run n spin s'
            | none    => none) = none
      cases n with
      | zero   => rfl
      | succ m => exact ih s

theorem spin_diverges (s s' : State) : ¬ Exec spin s s' := by
  intro hex
  obtain ⟨n, hn⟩ := run_complete hex
  rw [run_spin_none n s] at hn
  exact absurd hn (by simp)

/- ===== Unit 22 · `hoare` · Hoare triples ===== -/

def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap

def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap

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

/- ===== Unit 24 · `locality` · What "local" has to mean ===== -/

def HeapLocalWeak (c : Cmd) : Prop :=
  ∀ σ h hFrame s',
    Heap.disjoint h hFrame →
    Exec c ⟨σ, h⟩ s' →
    ∃ r : State,
      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧
      r.store = s'.store ∧
      r.heap = Heap.union s'.heap hFrame

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

/- ===== Unit 25 · `local-heap` · Locality of `write` and `free` ===== -/

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

/- ===== Unit 26 · `local-compose` · Locality composes ===== -/

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

/- ex x52 heapLocal_ite -/
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

/- ex x53 heapLocal_loop -/
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

/- ===== Unit 28 · `aliasing-closed` · The opening question, closed ===== -/

/- ex x55 classical_conjunction_rule_is_false -/
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

/- ex x56 separated_write_ok -/
theorem separated_write_ok (l₁ l₂ : Loc) (a b : Val) :
    Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.write l₂ (.const 5)) ((l₂ ↦ 5) ∗ (l₁ ↦ a)) := by
  have base : Hoare (l₂ ↦ b) (.write l₂ (.const 5)) (l₂ ↦ 5) :=
    hoare_write l₂ (.const 5) b
  exact hoare_frame base (heapLocal_write l₂ (.const 5))
    (preserves_of_heapOnly _ (heapOnly_pointsTo l₁ a))

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

/- ===== Unit 31 · `wp` · Weakest preconditions ===== -/

def wp (c : Cmd) (Q : Assertion) : Assertion :=
  fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap

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

/- ex x63 wp_sound / wp_weakest -/
theorem wp_sound (c : Cmd) (Q : Assertion) : Hoare (wp c Q) c Q := fun _ _ hp => hp

theorem wp_weakest {P Q : Assertion} {c : Cmd} (h : Hoare P c Q) : P ⊢ wp c Q := h

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

/- ex m12-4 wp_free_emp -/
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

/- ex x64 wp_frame -/
theorem wp_frame {Q R : Assertion} {c : Cmd}
    (hlocal : HeapLocal c) (hpres : Preserves c R) : wp c Q ∗ R ⊢ wp c (Q ∗ R) :=
  hoare_frame (fun _ _ hp => hp) hlocal hpres

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

/- ===== Unit 33 · `lseg` · LAB — segments and append ===== -/

def lseg : List Nat → Loc → Loc → Assertion
  | [],      start, finish => pure (fun _ => start = finish)
  | x :: xs, start, finish =>
      aExists fun next =>
        pure (fun _ => start ≠ 0) ∗ node start x next ∗ lseg xs next finish

/- ex x66 aExists_mono / lseg_nil_iff -/
theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :
    aExists P ⊢ aExists Q := by
  intro σ hh ⟨x, hp⟩
  exact ⟨x, h x σ hh hp⟩

theorem lseg_nil_iff (p q : Loc) : lseg [] p q ⊣⊢ pure (fun _ => p = q) :=
  ⟨entails_refl _, entails_refl _⟩

/- ex m10-4 lseg_append -/
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

/- ex x67 listRep_null -/
theorem listRep_null (xs : List Nat) : listRep xs 0 ⊢ pure (fun _ => xs = []) := by
  cases xs with
  | nil => intro σ h hp; exact ⟨rfl, hp.2⟩
  | cons x xs =>
      intro σ h hrep
      obtain ⟨next, h₁, h₂, _, _, ⟨hne, _⟩, _⟩ := hrep
      exact absurd rfl hne

/- ===== Unit 34 · `wand` · The magic wand ===== -/

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

/- ex x68 wand_unit / hole_intro / hole_elim -/
theorem wand_unit (P Q : Assertion) : Q ⊢ P -∗ (P ∗ Q) := by
  intro σ h hq h' hd hp
  exact ⟨h', h, disjoint_symm hd, union_comm hd, hp, hq⟩

theorem hole_intro (P R : Assertion) : P ∗ R ⊢ P ∗ (P -∗ (P ∗ R)) :=
  star_mono_right P (wand_unit P R)

theorem hole_elim (P R : Assertion) : P ∗ (P -∗ (P ∗ R)) ⊢ P ∗ R :=
  entails_trans (star_comm P (P -∗ (P ∗ R))) (wand_elim P (P ∗ R))

/- ex x69 wand_curry / wand_uncurry -/
theorem wand_curry (P Q R : Assertion) : ((P ∗ Q) -∗ R) ⊢ P -∗ (Q -∗ R) := by
  intro σ h hw h₁ hd₁ hp h₂ hd₂ hq
  obtain ⟨hdh2, hd12⟩ := disjoint_union_left.mp hd₂
  have hdd : Heap.disjoint h (Heap.union h₁ h₂) :=
    disjoint_union_right.mpr ⟨hd₁, hdh2⟩
  have hR := hw (Heap.union h₁ h₂) hdd ⟨h₁, h₂, hd12, rfl, hp, hq⟩
  rw [union_assoc]
  exact hR

theorem wand_uncurry (P Q R : Assertion) : (P -∗ (Q -∗ R)) ⊢ (P ∗ Q) -∗ R := by
  intro σ h hw h' hd ⟨h₁, h₂, hd₁₂, hu, hp, hq⟩
  subst hu
  obtain ⟨hdh1, hdh2⟩ := disjoint_union_right.mp hd
  have hR := hw h₁ hdh1 hp h₂ (disjoint_union_left.mpr ⟨hdh2, hd₁₂⟩) hq
  rw [← union_assoc]
  exact hR

theorem emp_wand_elim (P : Assertion) : (emp -∗ P) ⊢ P := by
  intro σ h hw
  have hP := hw Heap.empty (disjoint_empty_right h) rfl
  rw [union_empty_right] at hP
  exact hP

theorem emp_wand_intro (P : Assertion) : P ⊢ (emp -∗ P) := by
  intro σ h hp h' hd he
  have he' : h' = Heap.empty := he
  subst he'
  rw [union_empty_right]
  exact hp

/- ===== Unit 35 · `partial` · Partial correctness, and conditionals ===== -/

/- ex x70 partial_of_total -/
theorem partial_of_total {P Q : Assertion} {c : Cmd}
    (h : Hoare P c Q) : PartialHoare P c Q := by
  intro σ hh s' hp hex
  obtain ⟨s'', hex'', hq⟩ := h σ hh hp
  have : s' = s'' := exec_deterministic hex hex''
  rw [this]; exact hq

def bTrue (b : BExpr) : Assertion := fun σ _ => b.eval σ = true

def bFalse (b : BExpr) : Assertion := fun σ _ => b.eval σ = false

/- ex m13-1 partialHoare_skip / partialHoare_seq / partialHoare_consequence -/
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

/- ex x71 hoare_ite -/
theorem hoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}
    (h₁ : Hoare (aAnd P (bTrue b)) c₁ Q)
    (h₂ : Hoare (aAnd P (bFalse b)) c₂ Q) :
    Hoare P (.ite b c₁ c₂) Q := by
  intro σ h hp
  cases hbv : b.eval σ with
  | true =>
      obtain ⟨s', hex, hq⟩ := h₁ σ h ⟨hp, hbv⟩
      exact ⟨s', Exec.iteTrue hbv hex, hq⟩
  | false =>
      obtain ⟨s', hex, hq⟩ := h₂ σ h ⟨hp, hbv⟩
      exact ⟨s', Exec.iteFalse hbv hex, hq⟩

theorem wp_ite (b : BExpr) (c₁ c₂ : Cmd) (Q : Assertion) :
    wp (.ite b c₁ c₂) Q ⊣⊢
      aOr (aAnd (bTrue b) (wp c₁ Q)) (aAnd (bFalse b) (wp c₂ Q)) := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex with
    | iteTrue hb hex' => exact Or.inl ⟨hb, s', hex', hq⟩
    | iteFalse hb hex' => exact Or.inr ⟨hb, s', hex', hq⟩
  · intro σ h hor
    rcases hor with ⟨hb, s', hex, hq⟩ | ⟨hb, s', hex, hq⟩
    · exact ⟨s', Exec.iteTrue hb hex, hq⟩
    · exact ⟨s', Exec.iteFalse hb hex, hq⟩

/- ===== Unit 36 · `invariant` · The invariant rule ===== -/

/- ex m13-3 loop_invariant / partialHoare_while -/
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

def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))

def countdown (x : Var) : Cmd :=
  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))

/- ex x72 countdown_keeps_cell -/
theorem countdown_keeps_cell (x : Var) (l : Loc) (v : Val) :
    PartialHoare (l ↦ v) (countdown x) (aAnd (l ↦ v) (bFalse (counterGuard x))) := by
  refine partialHoare_while (I := (l ↦ v)) ?_
  intro σ h s' hpre hex
  cases hex
  exact hpre.1

/- ===== Unit 37 · `variant` · LAB/capstone — a loop that terminates, and owns a cell ===== -/

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

/- ex m13-5 countdown_spec -/
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

def drainBody (x : Var) (l : Loc) : Cmd :=
  .assign x (.minus (.var x) (.const 1)) ;; .write l (.var x)

def drain (x : Var) (l : Loc) : Cmd := .loop (counterGuard x) (drainBody x l)

/- ex x73 drainInv / drain_step / drain_stop / drain_spec -/
def drainInv (x : Var) (l : Loc) (n : Nat) : Assertion :=
  aAnd (fact (fun σ => σ x = n)) (l ↦ n)

theorem drain_step (x : Var) (l : Loc) (n : Nat) :
    Hoare (aAnd (drainInv x l (n + 1)) (bTrue (counterGuard x)))
          (drainBody x l) (drainInv x l n) := by
  intro σ h hpre
  obtain ⟨⟨hx, hh⟩, _⟩ := hpre
  have hx' : σ x = n + 1 := hx
  subst hh
  refine ⟨_, Exec.seq Exec.assign (Exec.write (singleton_same l (n + 1))), ?_, ?_⟩
  · show Store.set σ x (σ x - 1) x = n
    simp [Store.set, hx']
  · show Heap.write (Heap.singleton l (n + 1)) l (Store.set σ x (σ x - 1) x)
        = Heap.singleton l n
    have hset : Store.set σ x (σ x - 1) x = n := by simp [Store.set, hx']
    rw [hset, write_singleton]

theorem drain_stop (x : Var) (l : Loc) :
    ∀ σ h, drainInv x l 0 σ h → (counterGuard x).eval σ = false := by
  intro σ h hI
  have hx : σ x = 0 := hI.1
  show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false
  simp [Atom.eval, hx]

theorem drain_spec (x : Var) (l : Loc) : ∀ n,
    Hoare (drainInv x l n) (drain x l)
      (aExists fun m => aAnd (drainInv x l m) (bFalse (counterGuard x))) :=
  hoare_while_variant (fun n => drain_step x l n) (drain_stop x l)

/- ===== Unit 38 · `beyond` · Allocation, generalisation, and what is undone ===== -/

def pcmStar {M : Type} (K : PCM M) (P Q : M → Prop) : M → Prop :=
  fun m => ∃ m₁ m₂, K.valid m₁ m₂ ∧ m = K.op m₁ m₂ ∧ P m₁ ∧ Q m₂

/- ex x74 pcmStar_comm -/
theorem pcmStar_comm {M : Type} (K : PCM M) (P Q : M → Prop) (m : M) :
    pcmStar K P Q m → pcmStar K Q P m := by
  intro ⟨m₁, m₂, hv, hm, hp, hq⟩
  exact ⟨m₂, m₁, K.valid_comm _ _ hv, by rw [hm, K.op_comm _ _ hv], hq, hp⟩

/- ex x75 pcmStar_unit_left -/
theorem pcmStar_unit_left {M : Type} (K : PCM M) (P : M → Prop) (m : M) :
    pcmStar K (fun x => x = K.unit) P m → P m := by
  intro ⟨m₁, m₂, _, hm, he, hp⟩
  subst he
  rw [hm, K.unit_left]
  exact hp

