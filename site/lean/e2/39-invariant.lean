/- ===== Unit 36 · `invariant` · The invariant rule ===== -/

/- ex m13-3 loop_invariant / partialHoare_while -/
theorem loop_invariant {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}
    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :
    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →
      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by
  intro cmd s s' hex
  induction hex with
  | skip => intro heq; cases heq
  | assign => intro heq; cases heq
  | load _ => intro heq; cases heq
  | write _ => intro heq; cases heq
  | free _ => intro heq; cases heq
  | seq _ _ _ _ => intro heq; cases heq
  | iteTrue _ _ _ => intro heq; cases heq
  | iteFalse _ _ _ => intro heq; cases heq
  | loopFalse hb =>
      intro heq hI
      cases heq
      exact ⟨hI, hb⟩
  | loopTrue hb hbdy _ _ ihrest =>
      intro heq hI
      cases heq
      exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)

theorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}
    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :
    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by
  intro σ h s' hI hex
  exact loop_invariant hbody hex rfl hI

def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))

def countdown (x : Var) : Cmd :=
  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))

/- ex x72 countdown_keeps_cell -/
theorem countdown_keeps_cell (x : Var) (l : Loc) (v : Val) :
    PartialHoare (l ↦ v) (countdown x) (aAnd (l ↦ v) (bFalse (counterGuard x))) := by
  refine partialHoare_while (I := (l ↦ v)) ?_
  intro σ h s' hpre hex
  cases hex
  exact hpre.1
