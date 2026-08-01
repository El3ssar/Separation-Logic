/- Edition 2 · new Lean checked against site/lean/prelude/m13.lean TRUNCATED TO LINE 1277.
   The shipped m13 prelude does not compile: its last block redeclares Cmd. -/

def swap (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) : Cmd :=
  .load tmp₁ l₁ ;; (.load tmp₂ l₂ ;; (.write l₁ (.var tmp₂) ;; .write l₂ (.var tmp₁)))

theorem swap_heap (l₁ l₂ : Loc) (a b : Val) (hne : l₁ ≠ l₂) :
    Heap.write (Heap.write (Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b)) l₁ b) l₂ a
      = Heap.union (Heap.singleton l₁ b) (Heap.singleton l₂ a) := by
  funext x
  by_cases hx₂ : x = l₂
  · subst hx₂
    rw [write_same]
    rw [union_of_none (Heap.singleton x a) (singleton_other l₁ x b (fun h => hne h.symm))]
    rw [singleton_same]
  · rw [write_other _ l₂ x a hx₂]
    by_cases hx₁ : x = l₁
    · subst hx₁
      rw [write_same, union_of_some (Heap.singleton l₂ a) (singleton_same x b)]
    · rw [write_other _ l₁ x b hx₁,
          union_of_none (Heap.singleton l₂ b) (singleton_other l₁ x a hx₁),
          union_of_none (Heap.singleton l₂ a) (singleton_other l₁ x b hx₁),
          singleton_other l₂ x b hx₂, singleton_other l₂ x a hx₂]
theorem swap_spec (tmp₁ tmp₂ : Var) (l₁ l₂ : Loc) (a b : Val) (hne : tmp₁ ≠ tmp₂) :
    Hoare ((l₁ ↦ a) ∗ (l₂ ↦ b)) (swap tmp₁ tmp₂ l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a)) := by
  intro σ h hstar
  obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hstar
  subst hp; subst hq; subst hu
  have hlne : l₁ ≠ l₂ := (singleton_disjoint_iff a b).mp hd
  have hH1 : Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b) l₁ = some a :=
    union_of_some _ (singleton_same l₁ a)
  have hH2 : Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b) l₂ = some b := by
    rw [union_of_none (Heap.singleton l₂ b) (singleton_other l₁ l₂ a (Ne.symm hlne)), singleton_same]
  have e2 : Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₂ = b := by simp [Store.set]
  have e1 : Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₁ = a := by simp [Store.set, hne]
  have hH3 : Heap.write (Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b)) l₁
      (Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₂) l₂ = some b := by
    rw [write_other _ l₁ l₂ _ hlne.symm]; exact hH2
  refine ⟨_, Exec.seq (Exec.load hH1) (Exec.seq (Exec.load hH2)
      (Exec.seq (Exec.write hH1) (Exec.write hH3))), ?_⟩
  refine ⟨Heap.singleton l₁ b, Heap.singleton l₂ a, singleton_disjoint b a hlne, ?_, rfl, rfl⟩
  show Heap.write (Heap.write (Heap.union (Heap.singleton l₁ a) (Heap.singleton l₂ b)) l₁
        (Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₂)) l₂
        (Store.set (Store.set σ tmp₁ a) tmp₂ b tmp₁) = _
  rw [e1, e2]
  exact swap_heap l₁ l₂ a b hlne

def drainBody (x : Var) (l : Loc) : Cmd :=
  .assign x (.minus (.var x) (.const 1)) ;; .write l (.var x)

def drain (x : Var) (l : Loc) : Cmd := .loop (counterGuard x) (drainBody x l)

def drainInv (x : Var) (l : Loc) (n : Nat) : Assertion :=
  aAnd (fact (fun σ => σ x = n)) (l ↦ n)

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

theorem countdown_keeps_cell (x : Var) (l : Loc) (v : Val) :
    PartialHoare (l ↦ v) (countdown x) (aAnd (l ↦ v) (bFalse (counterGuard x))) := by
  refine partialHoare_while (I := (l ↦ v)) ?_
  intro σ h s' hpre hex
  cases hex
  exact hpre.1
