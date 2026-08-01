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
