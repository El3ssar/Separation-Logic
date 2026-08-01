/- Edition 2 · new Lean checked against site/lean/prelude/m12.lean -/

theorem wp_sound (c : Cmd) (Q : Assertion) : Hoare (wp c Q) c Q := fun _ _ hp => hp

theorem wp_weakest {P Q : Assertion} {c : Cmd} (h : Hoare P c Q) : P ⊢ wp c Q := h

theorem wp_frame {Q R : Assertion} {c : Cmd}
    (hlocal : HeapLocal c) (hpres : Preserves c R) : wp c Q ∗ R ⊢ wp c (Q ∗ R) :=
  hoare_frame (fun _ _ hp => hp) hlocal hpres

def bTrue (b : BExpr) : Assertion := fun σ _ => b.eval σ = true
def bFalse (b : BExpr) : Assertion := fun σ _ => b.eval σ = false

/- Group B5: total-correctness control flow + wp, against the M12 prelude. -/

theorem hoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}
    (h₁ : Hoare (aAnd P (bTrue b)) c₁ Q)
    (h₂ : Hoare (aAnd P (bFalse b)) c₂ Q) :
    Hoare P (.ite b c₁ c₂) Q := by
  intro σ h hp
  cases hbv : b.eval σ with
  | true =>
      obtain ⟨s', hex, hq⟩ := h₁ σ h ⟨hp, hbv⟩
      exact ⟨s', Exec.iteTrue hbv hex, hq⟩
  | false =>
      obtain ⟨s', hex, hq⟩ := h₂ σ h ⟨hp, hbv⟩
      exact ⟨s', Exec.iteFalse hbv hex, hq⟩

theorem wp_ite (b : BExpr) (c₁ c₂ : Cmd) (Q : Assertion) :
    wp (.ite b c₁ c₂) Q ⊣⊢
      aOr (aAnd (bTrue b) (wp c₁ Q)) (aAnd (bFalse b) (wp c₂ Q)) := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex with
    | iteTrue hb hex' => exact Or.inl ⟨hb, s', hex', hq⟩
    | iteFalse hb hex' => exact Or.inr ⟨hb, s', hex', hq⟩
  · intro σ h hor
    rcases hor with ⟨hb, s', hex, hq⟩ | ⟨hb, s', hex, hq⟩
    · exact ⟨s', Exec.iteTrue hb hex, hq⟩
    · exact ⟨s', Exec.iteFalse hb hex, hq⟩
