/- Edition 2 · new Lean checked against site/lean/prelude/overview.lean -/

def aliasedAfter : Heap := fun x => if x = 4 then some 5 else none

example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5) := by
  intro ⟨h3, _⟩
  simp [aliasedAfter] at h3

/- Group A: the Lean bootstrap I want in Lectures 1-3. -/

-- L1: terms are proofs, application is modus ponens
theorem mp (P Q : Prop) : P → (P → Q) → Q := fun hp hpq => hpq hp

theorem comp (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := fun hp => g (f hp)

theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := fun h => ⟨h.2, h.1⟩

theorem or_comm' (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun h => h.elim Or.inr Or.inl

-- the same, in tactic mode, so the reader sees the two columns
theorem and_comm_tac (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

theorem or_comm_tac (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hp | hq
  · right; exact hp
  · left;  exact hq

-- L2: ∀ and ∃ over Nat, anonymous constructors
theorem exists_three : ∃ n : Nat, n + 1 = 4 := ⟨3, rfl⟩

theorem exists_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) :
    (∃ n, P n) → ∃ n, Q n := by
  intro hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨n, h n hn⟩

-- L2: equality, rfl, rw, calc
theorem two_add_two : 2 + 2 = 4 := rfl

theorem rw_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

theorem calc_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a = b := h1
    _ = c := h2

-- L3: functions as data; funext; congrFun
def twice (f : Nat → Nat) : Nat → Nat := fun n => f (f n)

theorem twice_succ : twice (fun n => n + 1) = fun n => n + 2 := by
  funext n
  rfl

theorem apply_eq {f g : Nat → Nat} (h : f = g) (n : Nat) : f n = g n :=
  congrFun h n
