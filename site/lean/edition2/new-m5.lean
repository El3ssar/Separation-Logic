/- Edition 2 · new Lean checked against site/lean/prelude/m5.lean -/

example : @Store.set = @update := rfl

theorem storeSet_same (σ : Store) (x : Var) (v : Val) : Store.set σ x v x = v := update_same σ x v
theorem storeSet_other (σ : Store) (x y : Var) (v : Val) (hne : y ≠ x) :
    Store.set σ x v y = σ y := update_other σ x y v hne

example (σ : Store) : (Atom.minus (.const 3) (.const 5)).eval σ = 0 := rfl

def Atom.size : Atom → Nat
  | .const _ => 1
  | .var _ => 1
  | .plus a b => a.size + b.size + 1
  | .minus a b => a.size + b.size + 1

example : (Atom.plus (.const 1) (.var 0)).size = 3 := rfl

theorem exec_load_stuck (x : Var) (l : Loc) (σ : Store) (s' : State) :
    ¬ Exec (.load x l) ⟨σ, Heap.empty⟩ s' := by
  intro hex
  cases hex with
  | load hl => exact absurd hl (by simp [Heap.empty])

theorem exec_load_inv {x : Var} {l : Loc} {s s' : State} (h : Exec (.load x l) s s') :
    ∃ v, s.heap l = some v ∧ s' = ⟨Store.set s.store x v, s.heap⟩ := by
  cases h with
  | load hl => exact ⟨_, hl, rfl⟩

theorem exec_assign_inv {x : Var} {e : Atom} {s s' : State} (h : Exec (.assign x e) s s') :
    s' = ⟨Store.set s.store x (e.eval s.store), s.heap⟩ := by
  cases h; rfl

theorem exec_skip_seq_inv {c : Cmd} {s s' : State} (h : Exec (.skip ;; c) s s') : Exec c s s' := by
  cases h with
  | seq h₁ h₂ => cases h₁; exact h₂

def allZeros : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: allZeros n

theorem allZeros_length (n : Nat) : (allZeros n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allZeros, ih]

theorem append_nil (xs : List Nat) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp

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
