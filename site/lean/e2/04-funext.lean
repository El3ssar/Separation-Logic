/- ===== Unit 03 · `funext` · Functions as values ===== -/

theorem function_extensionality {f g : Nat → Nat}
    (h : ∀ x, f x = g x) : f = g := funext h

def twice (f : Nat → Nat) : Nat → Nat := fun n => f (f n)

theorem twice_succ : twice (fun n => n + 1) = fun n => n + 2 := by
  funext n
  rfl

theorem apply_eq {f g : Nat → Nat} (h : f = g) (n : Nat) : f n = g n :=
  congrFun h n
