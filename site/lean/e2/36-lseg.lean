/- ===== Unit 33 · `lseg` · LAB — segments and append ===== -/

def lseg : List Nat → Loc → Loc → Assertion
  | [],      start, finish => pure (fun _ => start = finish)
  | x :: xs, start, finish =>
      aExists fun next =>
        pure (fun _ => start ≠ 0) ∗ node start x next ∗ lseg xs next finish

/- ex x66 aExists_mono / lseg_nil_iff -/
theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :
    aExists P ⊢ aExists Q := by
  intro σ hh ⟨x, hp⟩
  exact ⟨x, h x σ hh hp⟩

theorem lseg_nil_iff (p q : Loc) : lseg [] p q ⊣⊢ pure (fun _ => p = q) :=
  ⟨entails_refl _, entails_refl _⟩

/- ex m10-4 lseg_append -/
theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),
    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by
  intro xs
  induction xs with
  | nil =>
      intro ys p q r σ h hstar
      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar
      have hpq' : p = q := hpq
      subst hpq'
      subst he
      rw [hu, union_empty_left]
      exact hys
  | cons x xs ih =>
      intro ys p q r
      refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_
      refine entails_trans (star_exists_left _ _) ?_
      refine aExists_mono (fun n => ?_)
      refine entails_trans (star_assoc_left _ _ _) ?_
      refine star_mono_right _ ?_
      refine entails_trans (star_assoc_left _ _ _) ?_
      exact star_mono_right _ (ih ys n q r)

/- ex m10-5 lseg_listRep -/
theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),
    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p := by
  intro xs
  induction xs with
  | nil =>
      intro ys p q σ h hstar
      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar
      have hpq' : p = q := hpq
      subst hpq'
      subst he
      rw [hu, union_empty_left]
      exact hys
  | cons x xs ih =>
      intro ys p q
      refine entails_trans (star_exists_left _ _) ?_
      refine aExists_mono (fun n => ?_)
      refine entails_trans (star_assoc_left _ _ _) ?_
      refine star_mono_right _ ?_
      refine entails_trans (star_assoc_left _ _ _) ?_
      exact star_mono_right _ (ih ys n q)

/- ex x67 listRep_null -/
theorem listRep_null (xs : List Nat) : listRep xs 0 ⊢ pure (fun _ => xs = []) := by
  cases xs with
  | nil => intro σ h hp; exact ⟨rfl, hp.2⟩
  | cons x xs =>
      intro σ h hrep
      obtain ⟨next, h₁, h₂, _, _, ⟨hne, _⟩, _⟩ := hrep
      exact absurd rfl hne
