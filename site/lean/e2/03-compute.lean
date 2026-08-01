/- ===== Unit 02 · `compute` · Equality, computation, and the limits of `rfl` ===== -/

theorem rw_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

theorem calc_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a = b := h1
    _ = c := h2
