/- ===== Unit 31 · `wp` · Weakest preconditions ===== -/

def wp (c : Cmd) (Q : Assertion) : Assertion :=
  fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap

theorem hoare_iff_entails_wp (P Q : Assertion) (c : Cmd) :
    Hoare P c Q ↔ P ⊢ wp c Q := Iff.rfl

/- ex m12-1 wp_skip / wp_assign -/
theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex; exact hq
  · intro σ h hq
    exact ⟨⟨σ, h⟩, Exec.skip, hq⟩

theorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :
    wp (.assign x e) Q ⊣⊢ subst x e Q := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex; exact hq
  · intro σ h hq
    exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩

/- ex m12-2 wp_seq -/
theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :
    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q) := by
  constructor
  · intro σ h ⟨s'', hex, hq⟩
    cases hex with
    | seq h₁ h₂ => exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩
  · intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩
    exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩

/- ex m12-3 wp_mono -/
theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q' := by
  intro σ hh ⟨s', hex, hq⟩
  exact ⟨s', hex, h s'.store s'.heap hq⟩

/- ex x63 wp_sound / wp_weakest -/
theorem wp_sound (c : Cmd) (Q : Assertion) : Hoare (wp c Q) c Q := fun _ _ hp => hp

theorem wp_weakest {P Q : Assertion} {c : Cmd} (h : Hoare P c Q) : P ⊢ wp c Q := h

theorem heap_eq_singleton {h : Heap} {l : Loc} {v : Val}
    (hl : h l = some v) (hrest : Heap.erase h l = Heap.empty) :
    h = Heap.singleton l v := by
  funext x
  by_cases hx : x = l
  · subst hx; rw [hl, singleton_same]
  · rw [singleton_other l x v hx]
    have := congrFun hrest x
    rw [erase_other h l x hx] at this
    exact this

/- ex m12-4 wp_free_emp -/
theorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by
  constructor
  · intro σ h ⟨s', hex, he⟩
    cases hex with
    | free hl =>
        refine ⟨_, heap_eq_singleton hl ?_⟩
        exact he
  · intro σ h ⟨v, hp⟩
    subst hp
    exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v),
           erase_singleton l v⟩

/- ex m12-5 wp_write -/
theorem wp_write (l : Loc) (new : Val) :
    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old) := by
  constructor
  · intro σ h ⟨s', hex, hq⟩
    cases hex with
    | write hl =>
        rename_i old
        refine ⟨old, ?_⟩
        have hl' : h l = some old := hl
        have hq' : Heap.write h l new = Heap.singleton l new := hq
        funext x
        by_cases hx : x = l
        · subst hx; rw [hl', singleton_same]
        · rw [singleton_other l x old hx]
          have := congrFun hq' x
          rw [write_other h l x new hx, singleton_other l x new hx] at this
          exact this
  · intro σ h ⟨old, hp⟩
    subst hp
    exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩,
           Exec.write (singleton_same l old), write_singleton l old new⟩

/- ex x64 wp_frame -/
theorem wp_frame {Q R : Assertion} {c : Cmd}
    (hlocal : HeapLocal c) (hpres : Preserves c R) : wp c Q ∗ R ⊢ wp c (Q ∗ R) :=
  hoare_frame (fun _ _ hp => hp) hlocal hpres
