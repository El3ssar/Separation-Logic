/- ===== Unit 35 · `partial` · Partial correctness, and conditionals ===== -/

/- ex x70 partial_of_total -/
theorem partial_of_total {P Q : Assertion} {c : Cmd}
    (h : Hoare P c Q) : PartialHoare P c Q := by
  intro σ hh s' hp hex
  obtain ⟨s'', hex'', hq⟩ := h σ hh hp
  have : s' = s'' := exec_deterministic hex hex''
  rw [this]; exact hq

def bTrue (b : BExpr) : Assertion := fun σ _ => b.eval σ = true

def bFalse (b : BExpr) : Assertion := fun σ _ => b.eval σ = false

/- ex m13-1 partialHoare_skip / partialHoare_seq / partialHoare_consequence -/
theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P := by
  intro σ h s' hp hex
  cases hex; exact hp

theorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}
    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :
    PartialHoare P (c₁ ;; c₂) R := by
  intro σ h s' hp hex
  cases hex with
  | seq hex₁ hex₂ =>
      rename_i sMid
      exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂

theorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}
    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :
    PartialHoare P' c Q' := by
  intro σ h s' hp hex
  exact hpost s'.store s'.heap (hc σ h s' (hpre σ h hp) hex)

/- ex m13-2 partialHoare_ite -/
theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}
    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)
    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :
    PartialHoare P (.ite b c₁ c₂) Q := by
  intro σ h s' hp hex
  cases hex with
  | iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'
  | iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'

/- ex x71 hoare_ite -/
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
