/- ===== Unit 37 · `variant` · LAB/capstone — a loop that terminates, and owns a cell ===== -/

/- ex m13-4 hoare_while_variant -/
theorem hoare_while_variant {I : Nat → Assertion} {b : BExpr} {c : Cmd}
    (hstep : ∀ n, Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n))
    (hstop : ∀ σ h, I 0 σ h → b.eval σ = false) :
    ∀ n, Hoare (I n) (.loop b c) (aExists fun m => aAnd (I m) (bFalse b)) := by
  intro n
  induction n with
  | zero =>
      intro σ h hI
      exact ⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩
  | succ n ih =>
      intro σ h hI
      cases hbv : b.eval σ with
      | true =>
          obtain ⟨s₁, hex₁, hI₁⟩ := hstep n σ h ⟨hI, hbv⟩
          obtain ⟨s₂, hex₂, hpost⟩ := ih s₁.store s₁.heap hI₁
          exact ⟨s₂, Exec.loopTrue hbv hex₁ hex₂, hpost⟩
      | false =>
          exact ⟨⟨σ, h⟩, Exec.loopFalse hbv, n + 1, hI, hbv⟩

/- ex m13-5 countdown_spec -/
theorem countdown_spec (x : Var) : ∀ n,
    Hoare (fun σ _ => σ x = n) (countdown x)
      (aExists fun m => aAnd (fun σ _ => σ x = m) (bFalse (counterGuard x))) := by
  refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_
  · intro n σ h hpre
    obtain ⟨hx, _⟩ := hpre
    refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩
    show Store.set σ x (σ x - 1) x = n
    have hx' : σ x = n + 1 := hx
    simp [Store.set, hx']
  · intro σ h hI
    have hx : σ x = 0 := hI
    show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false
    simp [Atom.eval, hx]

def drainBody (x : Var) (l : Loc) : Cmd :=
  .assign x (.minus (.var x) (.const 1)) ;; .write l (.var x)

def drain (x : Var) (l : Loc) : Cmd := .loop (counterGuard x) (drainBody x l)

def drainInv (x : Var) (l : Loc) (n : Nat) : Assertion :=
  aAnd (fact (fun σ => σ x = n)) (l ↦ n)

/- ex x73 drain_spec / drain_step / drain_stop -/
theorem drain_step (x : Var) (l : Loc) (n : Nat) :
    Hoare (aAnd (drainInv x l (n + 1)) (bTrue (counterGuard x)))
          (drainBody x l) (drainInv x l n) := by
  intro σ h hpre
  obtain ⟨⟨hx, hh⟩, _⟩ := hpre
  have hx' : σ x = n + 1 := hx
  subst hh
  refine ⟨_, Exec.seq Exec.assign (Exec.write (singleton_same l (n + 1))), ?_, ?_⟩
  · show Store.set σ x (σ x - 1) x = n
    simp [Store.set, hx']
  · show Heap.write (Heap.singleton l (n + 1)) l (Store.set σ x (σ x - 1) x)
        = Heap.singleton l n
    have hset : Store.set σ x (σ x - 1) x = n := by simp [Store.set, hx']
    rw [hset, write_singleton]

theorem drain_stop (x : Var) (l : Loc) :
    ∀ σ h, drainInv x l 0 σ h → (counterGuard x).eval σ = false := by
  intro σ h hI
  have hx : σ x = 0 := hI.1
  show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false
  simp [Atom.eval, hx]

theorem drain_spec (x : Var) (l : Loc) : ∀ n,
    Hoare (drainInv x l n) (drain x l)
      (aExists fun m => aAnd (drainInv x l m) (bFalse (counterGuard x))) :=
  hoare_while_variant (fun n => drain_step x l n) (drain_stop x l)
