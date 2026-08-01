/- Edition 2 · new Lean checked against site/lean/prelude/m10.lean -/

theorem listRep_cons_ne_zero (x : Nat) (xs : List Nat) (p : Loc) :
    listRep (x :: xs) p ⊢ fact (fun _ => p ≠ 0) := by
  intro σ h ⟨n, h₁, h₂, _, _, ⟨hp, _⟩, _⟩
  exact hp

theorem lseg_nil_iff (p q : Loc) : lseg [] p q ⊣⊢ pure (fun _ => p = q) :=
  ⟨entails_refl _, entails_refl _⟩

theorem listRep_null (xs : List Nat) : listRep xs 0 ⊢ pure (fun _ => xs = []) := by
  cases xs with
  | nil => intro σ h hp; exact ⟨rfl, hp.2⟩
  | cons x xs =>
      intro σ h hrep
      obtain ⟨next, h₁, h₂, _, _, ⟨hne, _⟩, _⟩ := hrep
      exact absurd rfl hne
