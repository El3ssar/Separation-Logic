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
