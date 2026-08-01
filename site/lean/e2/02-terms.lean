/- ===== Unit 01 · `terms` · Propositions are types, proofs are terms ===== -/

theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp

theorem exists_example : ∃ n : Nat, n = 3 := ⟨3, rfl⟩

theorem mp (P Q : Prop) : P → (P → Q) → Q := fun hp hpq => hpq hp

/- ex x03 comp -/
theorem comp (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := fun hp => g (f hp)

/- ex x04 and_comm' / or_comm' -/
theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := fun h => ⟨h.2, h.1⟩

theorem or_comm' (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim Or.inr Or.inl

theorem and_comm_tac (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

theorem or_comm_tac (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hp | hq
  · right; exact hp
  · left;  exact hq

theorem exists_three : ∃ n : Nat, n + 1 = 4 := ⟨3, rfl⟩

/- ex x05 exists_mono -/
theorem exists_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) :
    (∃ n, P n) → ∃ n, Q n := by
  intro hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨n, h n hn⟩

theorem two_add_two : 2 + 2 = 4 := rfl
