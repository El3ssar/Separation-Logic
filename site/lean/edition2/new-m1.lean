/- Edition 2 · new Lean checked against site/lean/prelude/m1.lean -/

theorem heap_ext {h₁ h₂ : Heap} (h : ∀ l, h₁ l = h₂ l) : h₁ = h₂ := funext h

theorem erase_erase (h : Heap) (l : Loc) :
    Heap.erase (Heap.erase h l) l = Heap.erase h l := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, hx]

theorem write_erase_same (h : Heap) (l : Loc) (v : Val) :
    Heap.write (Heap.erase h l) l v = Heap.write h l v := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.erase, hx]

theorem erase_write_comm (h : Heap) (l l' : Loc) (v : Val) (hne : l ≠ l') :
    Heap.erase (Heap.write h l v) l' = Heap.write (Heap.erase h l') l v := by
  funext x
  simp only [Heap.write, Heap.erase]
  by_cases hx : x = l'
  · have hxl : x ≠ l := by rw [hx]; exact fun hc => hne hc.symm
    rw [if_pos hx, if_neg hxl, if_pos hx]
  · by_cases hxl : x = l
    · rw [if_neg hx, if_pos hxl, if_pos hxl]
    · rw [if_neg hx, if_neg hxl, if_neg hxl, if_neg hx]

theorem erase_comm (h : Heap) (l₁ l₂ : Loc) :
    Heap.erase (Heap.erase h l₁) l₂ = Heap.erase (Heap.erase h l₂) l₁ := by
  funext x
  by_cases h₁ : x = l₁ <;> by_cases h₂ : x = l₂ <;> simp [Heap.erase, h₁, h₂]

theorem write_empty (l : Loc) (v : Val) :
    Heap.write Heap.empty l v = Heap.singleton l v := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.empty, Heap.singleton, hx]

theorem update_idem (f : Nat → Nat) (x : Nat) : update f x (f x) = f := by
  funext y
  by_cases h : y = x <;> simp [update, h]

theorem write_of_eq {h : Heap} {l : Loc} {v : Val} (hl : h l = some v) :
    Heap.write h l v = h := by
  funext x
  by_cases hx : x = l
  · subst hx; rw [write_same]; exact hl.symm
  · rw [write_other h l x v hx]


def ptsAtLeast (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h l = some v
def ptsExactly (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h = Heap.singleton l v

def twoCells : Heap := Heap.write (Heap.singleton 4 3) 9 7

example : ptsAtLeast 4 3 (fun _ => 0) twoCells := by
  show twoCells 4 = some 3
  rw [show twoCells = Heap.write (Heap.singleton 4 3) 9 7 from rfl,
      write_other (Heap.singleton 4 3) 9 4 7 (by simp), singleton_same]

example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by
  intro h
  have h9 := congrFun h 9
  rw [show twoCells = Heap.write (Heap.singleton 4 3) 9 7 from rfl, write_same,
      singleton_other 4 9 3 (by simp)] at h9
  exact absurd h9 (by simp)

example : Heap.erase twoCells 4 ≠ Heap.empty := by
  intro h
  have h9 := congrFun h 9
  rw [erase_other twoCells 4 9 (by simp),
      show twoCells = Heap.write (Heap.singleton 4 3) 9 7 from rfl, write_same] at h9
  exact absurd h9 (by simp [Heap.empty])
