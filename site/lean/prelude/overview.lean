/- Everything defined and proved UP TO AND INCLUDING §.
   Verified with Lean 4.32.2, no imports, no Mathlib. -/

abbrev Loc   := Nat
abbrev Val   := Nat
abbrev Heap  := Loc → Option Val
abbrev Var   := Nat
abbrev Store := Var → Val

abbrev Assertion := Store → Heap → Prop
