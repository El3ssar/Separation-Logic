/- ===== Unit 21 · `interpreter` · LAB — an interpreter, proved to agree (OPTIONAL) ===== -/

def run : Nat → Cmd → State → Option State
  | 0,     _,            _ => none
  | _ + 1, .skip,        s => some s
  | _ + 1, .assign x e,  s => some ⟨Store.set s.store x (e.eval s.store), s.heap⟩
  | _ + 1, .load x l,    s =>
      match s.heap l with
      | some v => some ⟨Store.set s.store x v, s.heap⟩
      | none   => none
  | _ + 1, .write l e,   s =>
      match s.heap l with
      | some _ => some ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩
      | none   => none
  | _ + 1, .free l,      s =>
      match s.heap l with
      | some _ => some ⟨s.store, Heap.erase s.heap l⟩
      | none   => none
  | n + 1, .seq c₁ c₂,   s =>
      match run n c₁ s with
      | some s' => run n c₂ s'
      | none    => none
  | n + 1, .ite b c₁ c₂, s =>
      match b.eval s.store with
      | true  => run n c₁ s
      | false => run n c₂ s
  | n + 1, .loop b c,   s =>
      match b.eval s.store with
      | true  =>
          match run n c s with
          | some s' => run n (.loop b c) s'
          | none    => none
      | false => some s

def demoProg : Cmd := .load 0 3 ;; .write 3 (.plus (.var 0) (.const 1))

def demoStart : State := ⟨fun _ => 0, Heap.singleton 3 7⟩

/- ex x47 run_example -/
example : run 6 demoProg demoStart
    = some ⟨Store.set demoStart.store 0 7, Heap.write demoStart.heap 3 8⟩ := by rfl

/- ex m5-3 run_sound -/
theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s' := by
  intro n
  induction n with
  | zero => intro c s s' h; simp [run] at h
  | succ n ih =>
    intro c s s' h
    cases c with
    | skip => simp [run] at h; rw [← h]; exact .skip
    | assign x e => simp [run] at h; rw [← h]; exact .assign
    | load x l =>
        simp only [run] at h
        cases hl : s.heap l with
        | none   => rw [hl] at h; simp at h
        | some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl
    | write l e =>
        simp only [run] at h
        cases hl : s.heap l with
        | none   => rw [hl] at h; simp at h
        | some v => rw [hl] at h; simp at h; rw [← h]; exact .write hl
    | free l =>
        simp only [run] at h
        cases hl : s.heap l with
        | none   => rw [hl] at h; simp at h
        | some v => rw [hl] at h; simp at h; rw [← h]; exact .free hl
    | seq c₁ c₂ =>
        simp only [run] at h
        cases hr : run n c₁ s with
        | none    => rw [hr] at h; simp at h
        | some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s' h)
    | ite b c₁ c₂ =>
        simp only [run] at h
        cases hb : b.eval s.store with
        | true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s' h)
        | false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s' h)
    | loop b c =>
        simp only [run] at h
        cases hb : b.eval s.store with
        | false =>
            rw [hb] at h
            have hs : s = s' := Option.some.inj h
            subst hs
            exact .loopFalse hb
        | true  =>
            rw [hb] at h
            cases hr : run n c s with
            | none    => rw [hr] at h; simp at h
            | some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s' h)

/- ex m5-4 run_mono / run_le / run_complete -/
theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s' : State),
    run n c s = some s' → run (n + 1) c s = some s' := by
  intro n
  induction n with
  | zero => intro c s s' h; simp [run] at h
  | succ n ih =>
    intro c s s' h
    cases c with
    | skip => simpa [run] using h
    | assign x e => simpa [run] using h
    | load x l => simpa [run] using h
    | write l e => simpa [run] using h
    | free l => simpa [run] using h
    | seq c₁ c₂ =>
        simp only [run] at h ⊢
        cases hr : run n c₁ s with
        | none    => rw [hr] at h; simp at h
        | some s₁ => rw [hr] at h; rw [ih c₁ s s₁ hr]; exact ih c₂ s₁ s' h
    | ite b c₁ c₂ =>
        simp only [run] at h ⊢
        cases hb : b.eval s.store with
        | true  => rw [hb] at h; exact ih c₁ s s' h
        | false => rw [hb] at h; exact ih c₂ s s' h
    | loop b c =>
        simp only [run] at h ⊢
        cases hb : b.eval s.store with
        | false => rw [hb] at h; exact h
        | true  =>
            rw [hb] at h
            cases hr : run n c s with
            | none    => rw [hr] at h; simp at h
            | some s₁ =>
                rw [hr] at h
                have : run (n + 1) c s = some s₁ := ih c s s₁ hr
                rw [this]
                exact ih _ s₁ s' h

theorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s' : State}
    (h : run n c s = some s') : run m c s = some s' := by
  induction hle with
  | refl => exact h
  | step _ ih => exact run_mono _ _ _ _ ih

theorem run_complete {c : Cmd} {s s' : State} (h : Exec c s s') :
    ∃ n, run n c s = some s' := by
  induction h with
  | skip => exact ⟨1, rfl⟩
  | assign => exact ⟨1, rfl⟩
  | load hl => exact ⟨1, by simp [run, hl]⟩
  | write hl => exact ⟨1, by simp [run, hl]⟩
  | free hl => exact ⟨1, by simp [run, hl]⟩
  | seq _ _ ih₁ ih₂ =>
      obtain ⟨n₁, h₁⟩ := ih₁
      obtain ⟨n₂, h₂⟩ := ih₂
      refine ⟨max n₁ n₂ + 1, ?_⟩
      simp only [run]
      rw [run_le (Nat.le_max_left n₁ n₂) h₁]
      exact run_le (Nat.le_max_right n₁ n₂) h₂
  | iteTrue hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩
  | iteFalse hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩
  | loopFalse hb => exact ⟨1, by simp only [run, hb]⟩
  | loopTrue hb _ _ ihb ihr =>
      obtain ⟨n₁, h₁⟩ := ihb
      obtain ⟨n₂, h₂⟩ := ihr
      refine ⟨max n₁ n₂ + 1, ?_⟩
      simp only [run, hb]
      rw [run_le (Nat.le_max_left n₁ n₂) h₁]
      exact run_le (Nat.le_max_right n₁ n₂) h₂

def spin : Cmd := .loop (.not (.equals (.const 0) (.const 1))) .skip

theorem run_spin_none : ∀ (n : Nat) (s : State), run n spin s = none := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      show (match run n Cmd.skip s with
            | some s' => run n spin s'
            | none    => none) = none
      cases n with
      | zero   => rfl
      | succ m => exact ih s

theorem spin_diverges (s s' : State) : ¬ Exec spin s s' := by
  intro hex
  obtain ⟨n, hn⟩ := run_complete hex
  rw [run_spin_none n s] at hn
  exact absurd hn (by simp)
