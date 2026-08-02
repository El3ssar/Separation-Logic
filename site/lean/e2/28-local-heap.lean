/- ===== Unit 25 · `local-heap` · Locality of `write` and `free` ===== -/

theorem write_union_no_disjointness (h hFrame : Heap) (l : Loc) (v : Val) :
    Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame := by
  funext x
  by_cases hx : x = l
  · subst hx
    rw [write_same, union_of_some hFrame (write_same h x v)]
  · rw [write_other (Heap.union h hFrame) l x v hx]
    have hw : Heap.write h l v x = h x := write_other h l x v hx
    cases hh : h x with
    | none => rw [union_of_none hFrame hh, union_of_none hFrame (hw.trans hh)]
    | some w => rw [union_of_some hFrame hh, union_of_some hFrame (hw.trans hh)]

/- ex m8-2 heapLocal_write -/
theorem heapLocal_write (l : Loc) (e : Atom) : HeapLocal (.write l e) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | write hl =>
      have hl' : h l = _ := hl
      have hdw : Heap.disjoint (Heap.write h l (e.eval σ)) hFrame := by
        intro x
        rcases hd x with hx | hx
        · by_cases hxl : x = l
          · subst hxl; rw [hl'] at hx; exact absurd hx (by simp)
          · left; rw [write_other h l x (e.eval σ) hxl]; exact hx
        · exact Or.inr hx
      refine ⟨hdw, ⟨σ, Heap.write (Heap.union h hFrame) l (e.eval σ)⟩,
              Exec.write (union_of_some hFrame hl'), rfl, ?_⟩
      show Heap.write (Heap.union h hFrame) l (e.eval σ)
             = Heap.union (Heap.write h l (e.eval σ)) hFrame
      funext x
      by_cases hxl : x = l
      · subst hxl
        rw [write_same (Heap.union h hFrame) x (e.eval σ),
            union_of_some hFrame (write_same h x (e.eval σ))]
      · rw [write_other (Heap.union h hFrame) l x (e.eval σ) hxl]
        have hwx : Heap.write h l (e.eval σ) x = h x := write_other h l x (e.eval σ) hxl
        cases hx : h x with
        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]
        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]

/- ex m8-3 heapLocal_free -/
theorem heapLocal_free (l : Loc) : HeapLocal (.free l) := by
  intro σ h hFrame s' hd hex
  cases hex with
  | free hl =>
      have hl' : h l = _ := hl
      have hde : Heap.disjoint (Heap.erase h l) hFrame := by
        intro x
        rcases hd x with hx | hx
        · left
          by_cases hxl : x = l
          · subst hxl; exact erase_same h x
          · rw [erase_other h l x hxl]; exact hx
        · exact Or.inr hx
      refine ⟨hde, ⟨σ, Heap.erase (Heap.union h hFrame) l⟩,
              Exec.free (union_of_some hFrame hl'), rfl, ?_⟩
      show Heap.erase (Heap.union h hFrame) l = Heap.union (Heap.erase h l) hFrame
      funext x
      by_cases hxl : x = l
      · subst hxl
        rw [erase_same (Heap.union h hFrame) x,
            union_of_none hFrame (erase_same h x)]
        rcases hd x with hx | hx
        · rw [hx] at hl'; exact absurd hl' (by simp)
        · exact hx.symm
      · rw [erase_other (Heap.union h hFrame) l x hxl]
        have hex' : Heap.erase h l x = h x := erase_other h l x hxl
        cases hx : h x with
        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hex'.trans hx)]
        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hex'.trans hx)]
