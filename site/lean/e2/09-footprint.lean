/- ===== Unit 07 · `footprint` · How much do you own? ===== -/

def ptsAtLeast (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h l = some v
def ptsExactly (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h = Heap.singleton l v

def twoCells : Heap := Heap.write (Heap.singleton 4 3) 9 7

/- ex x16 a two-cell heap satisfies the loose reading -/
example : ptsAtLeast 4 3 (fun _ => 0) twoCells := by
  have hne : (4 : Loc) ≠ 9 := by simp
  show twoCells 4 = some 3
  unfold twoCells
  rw [write_other (Heap.singleton 4 3) 9 4 7 hne, singleton_same]

/- ex x17 it does not satisfy the exact reading -/
example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by
  intro h
  have hne : (9 : Loc) ≠ 4 := by simp
  have h9 := congrFun h 9
  unfold twoCells at h9
  rw [write_same, singleton_other 4 9 3 hne] at h9
  exact some_ne_none 7 h9

/- ex x18 after `free`, the heap is not empty -/
example : Heap.erase twoCells 4 ≠ Heap.empty := by
  intro h
  have hne : (9 : Loc) ≠ 4 := by simp
  have h9 := congrFun h 9
  rw [erase_other twoCells 4 9 hne] at h9
  unfold twoCells at h9
  rw [write_same] at h9
  exact some_ne_none 7 h9
