/- ===== Unit 00 · `aliasing` · The rule that is false ===== -/

abbrev Loc   := Nat
abbrev Val   := Nat
abbrev Heap  := Loc → Option Val
abbrev Var   := Nat
abbrev Store := Var → Val

def aliasedAfter : Heap := fun x => if x = 4 then some 5 else none

/- ex x02 aliasedAfter — the aliased postcondition is unsatisfiable -/
example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5) := by
  intro ⟨h3, _⟩
  simp [aliasedAfter] at h3
