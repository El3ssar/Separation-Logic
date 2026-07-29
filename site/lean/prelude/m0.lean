/- Everything defined and proved UP TO AND INCLUDING M0.
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
