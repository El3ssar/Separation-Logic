/- ===== Unit 38 · `beyond` · Allocation, generalisation, and what is undone ===== -/

def pcmStar {M : Type} (K : PCM M) (P Q : M → Prop) : M → Prop :=
  fun m => ∃ m₁ m₂, K.valid m₁ m₂ ∧ m = K.op m₁ m₂ ∧ P m₁ ∧ Q m₂

/- ex x74 pcmStar_comm -/
theorem pcmStar_comm {M : Type} (K : PCM M) (P Q : M → Prop) (m : M) :
    pcmStar K P Q m → pcmStar K Q P m := by
  intro ⟨m₁, m₂, hv, hm, hp, hq⟩
  exact ⟨m₂, m₁, K.valid_comm _ _ hv, by rw [hm, K.op_comm _ _ hv], hq, hp⟩

/- ex x75 pcmStar_unit_left -/
theorem pcmStar_unit_left {M : Type} (K : PCM M) (P : M → Prop) (m : M) :
    pcmStar K (fun x => x = K.unit) P m → P m := by
  intro ⟨m₁, m₂, _, hm, he, hp⟩
  subst he
  rw [hm, K.unit_left]
  exact hp
