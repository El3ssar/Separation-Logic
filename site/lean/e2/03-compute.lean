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
