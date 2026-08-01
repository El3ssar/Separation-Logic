/- ===== Unit 06 · `heap-laws` · LAB — equations between heaps ===== -/

theorem heap_ext {h₁ h₂ : Heap} (h : ∀ l, h₁ l = h₂ l) : h₁ = h₂ := funext h

/- ex m1-5 write_shadow -/
theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, hx]

/- ex m1-6 erase_write_same -/
theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.erase (Heap.write h l v) l = Heap.erase h l := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]

/- ex m1-7 write_comm -/
theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by
  funext x
  unfold Heap.write
  by_cases hx₁ : x = l₁
  · have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne
    rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]
  · by_cases hx₂ : x = l₂
    · rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]
    · rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]

/- ex m1-8 write_singleton / erase_singleton -/
theorem write_singleton (l : Loc) (v w : Val) :
    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]

theorem erase_singleton (l : Loc) (v : Val) :
    Heap.erase (Heap.singleton l v) l = Heap.empty := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]

/- ex x14 erase_erase / write_of_eq -/
theorem erase_erase (h : Heap) (l : Loc) :
    Heap.erase (Heap.erase h l) l = Heap.erase h l := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, hx]

theorem write_of_eq {h : Heap} {l : Loc} {v : Val} (hl : h l = some v) :
    Heap.write h l v = h := by
  funext x
  by_cases hx : x = l
  · subst hx; rw [write_same]; exact hl.symm
  · rw [write_other h l x v hx]

/- ex x15 erase_write_comm -/
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

theorem write_erase_same (h : Heap) (l : Loc) (v : Val) :
    Heap.write (Heap.erase h l) l v = Heap.write h l v := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.erase, hx]

theorem erase_comm (h : Heap) (l₁ l₂ : Loc) :
    Heap.erase (Heap.erase h l₁) l₂ = Heap.erase (Heap.erase h l₂) l₁ := by
  funext x
  by_cases h₁ : x = l₁ <;> by_cases h₂ : x = l₂ <;> simp [Heap.erase, h₁, h₂]

theorem write_empty (l : Loc) (v : Val) :
    Heap.write Heap.empty l v = Heap.singleton l v := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.empty, Heap.singleton, hx]
