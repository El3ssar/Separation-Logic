/- ===== Unit 22 · `hoare` · Hoare triples ===== -/

def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap

def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap

def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=
  fun σ h => Q (Store.set σ x (e.eval σ)) h

/- ex m6-1 hoare_consequence -/
theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}
    (hpre : P' ⊢ P) (hc : Hoare (P) (c) (Q)) (hpost : Q ⊢ Q') : Hoare (P') (c) (Q') := by
  intro σ h hp
  obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)
  exact ⟨s', hex, hpost s'.store s'.heap hq⟩

/- ex m6-2 hoare_skip / hoare_seq -/
theorem hoare_skip (P : Assertion) : Hoare (P) (.skip) (P) :=
  fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩

theorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}
    (h₁ : Hoare (P) (c₁) (Q)) (h₂ : Hoare (Q) (c₂) (R)) : Hoare (P) ((c₁ ;; c₂)) (R) := by
  intro σ h hp
  obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp
  obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq
  exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩

/- ex m6-3 hoare_assign -/
theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :
    Hoare (subst x e Q) ((.assign x e)) (Q) := by
  intro σ h hq
  exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩

/- ex m6-4 assign_constant -/
theorem assign_constant (x : Var) :
    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by
  intro σ h he
  refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩
  show Store.set σ x 10 x = 10
  simp [Store.set]

/- ex m6-5 assign_twice -/
theorem assign_twice (x y : Var) :
    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))
      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp) := by
  refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_
  · intro σ h he
    refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩
    show Store.set σ x 3 x = 3
    simp [Store.set]
  · intro σ h hpre
    obtain ⟨hx, he⟩ := hpre
    have hx' : σ x = 3 := hx
    refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩
    show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3
    constructor
    · show (if x = y then σ x else σ x) = 3
      simp [hx']
    · show (if y = y then σ x else σ y) = 3
      simp [hx']
