/- ===== Unit 12 · `assertions` · Assertions and entailment ===== -/

abbrev Assertion := Store → Heap → Prop

def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h
infix:40 " ⊢ " => Entails

def AssertionEquiv (P Q : Assertion) : Prop := Entails P Q ∧ Entails Q P
infix:40 " ⊣⊢ " => AssertionEquiv

def aTrue  : Assertion := fun _ _ => True

def aFalse : Assertion := fun _ _ => False

def aAnd (P Q : Assertion) : Assertion := fun σ h => P σ h ∧ Q σ h

def aOr  (P Q : Assertion) : Assertion := fun σ h => P σ h ∨ Q σ h

def aExists {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∃ x, P x σ h

def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ

/- ex m3-2 entails_refl / entails_trans -/
theorem entails_refl (P : Assertion) : P ⊢ P := fun _ _ hp => hp

theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun σ h hp => h₂ σ h (h₁ σ h hp)

/- ex m3-3 and_left / and_right / and_intro -/
theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1

theorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2

theorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=
  fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩

/- ex x27 or_left / or_right / or_elim -/
theorem or_left (P Q : Assertion) : P ⊢ aOr P Q := fun _ _ hp => Or.inl hp
theorem or_right (P Q : Assertion) : Q ⊢ aOr P Q := fun _ _ hq => Or.inr hq
theorem or_elim {P Q R : Assertion} (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : aOr P Q ⊢ R := by
  intro σ h hpq
  rcases hpq with hp | hq
  · exact h₁ σ h hp
  · exact h₂ σ h hq

/- ex x28 equiv_refl / equiv_symm / equiv_trans -/
theorem equiv_refl (P : Assertion) : P ⊣⊢ P := ⟨entails_refl P, entails_refl P⟩

theorem equiv_symm {P Q : Assertion} (h : P ⊣⊢ Q) : Q ⊣⊢ P := ⟨h.2, h.1⟩

theorem equiv_trans {P Q R : Assertion} (h₁ : P ⊣⊢ Q) (h₂ : Q ⊣⊢ R) : P ⊣⊢ R :=
  ⟨entails_trans h₁.1 h₂.1, entails_trans h₂.2 h₁.2⟩
