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
