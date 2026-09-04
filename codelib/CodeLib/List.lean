import Mathlib.Data.List.Sort

/-! Small list transformations shared by the example proofs. -/

namespace List

theorem extract_append {values : List α} {start mid stop : Nat}
    (hstart : start ≤ mid) (hmid : mid ≤ stop) :
    values.extract start mid ++ values.extract mid stop =
      values.extract start stop := by
  simp only [List.extract]
  have hdrop : values.drop mid = (values.drop start).drop (mid - start) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hdrop, ← List.take_add]; congr 1; omega

theorem take_extract_drop {values : List α} {start stop : Nat}
    (hstart : start ≤ stop) :
    values.take start ++ values.extract start stop ++ values.drop stop = values := by
  have hstop : start + (stop - start) = stop := Nat.add_sub_of_le hstart
  rw [List.extract, ← List.take_add, hstop]
  exact List.take_append_drop stop values

theorem extract_eq_of_take_eq {a b : List α} {start stop k : Nat}
    (hstop : stop ≤ k) (htake : a.take k = b.take k) :
    a.extract start stop = b.extract start stop := by
  simp only [List.extract, ← List.drop_take]
  simpa [List.take_take, Nat.min_eq_left hstop] using
    congrArg (List.drop start) (congrArg (List.take stop) htake)

theorem extract_eq_of_drop_eq {a b : List α} {start stop k : Nat}
    (hstart : k ≤ start) (hdrop : a.drop k = b.drop k) :
    a.extract start stop = b.extract start stop := by
  simp only [List.extract]
  congr 1
  simpa [List.drop_drop, Nat.add_sub_of_le hstart] using
    congrArg (List.drop (start - k)) hdrop

theorem pairwise_of_length_le_one {relation : α → α → Prop} {values : List α}
    (h : values.length ≤ 1) : values.Pairwise relation := by
  match values, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

/-- Exchange two in-bounds elements, using `getElem!` defaults out of bounds. -/
def swapElems [Inhabited α] (values : List α) (i j : Nat) : List α :=
  (values.set i values[j]!).set j values[i]!

theorem swapElems_eq_set [Inhabited α] (values : List α) {i j : Nat}
    (hi : i < values.length) (hj : j < values.length) :
    swapElems values i j = (values.set i values[j]).set j values[i] := by
  simp [swapElems, getElem!_pos values i hi, getElem!_pos values j hj]

@[simp] theorem swapElems_length [Inhabited α] (values : List α) (i j : Nat) :
    (swapElems values i j).length = values.length := by
  simp [swapElems, List.length_set]

theorem swapElems_get_i [Inhabited α] (values : List α) {i j : Nat}
    (hi : i < values.length) (hj : j < values.length) :
    (swapElems values i j)[i]! = values[j]! := by
  unfold swapElems
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

theorem swapElems_get_j [Inhabited α] (values : List α) {i j : Nat}
    (hi : i < values.length) (hj : j < values.length) :
    (swapElems values i j)[j]! = values[i]! := by
  unfold swapElems
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

theorem swapElems_get_other [Inhabited α] (values : List α) {i j k : Nat}
    (hki : k ≠ i) (hkj : k ≠ j) :
    (swapElems values i j)[k]! = values[k]! := by
  unfold swapElems
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

theorem swapElems_take_of_le [Inhabited α] (values : List α) {i j n : Nat}
    (hin : n ≤ i) (hjn : n ≤ j) :
    (swapElems values i j).take n = values.take n := by
  unfold swapElems
  rw [List.take_set, List.take_set]
  have hlen : (List.take n values).length ≤ n := List.length_take_le n values
  rw [List.set_eq_of_length_le (by rw [List.length_set]; exact hlen.trans hjn),
    List.set_eq_of_length_le (hlen.trans hin)]

theorem swapElems_drop_of_lt [Inhabited α] (values : List α) {i j n : Nat}
    (hin : i < n) (hjn : j < n) :
    (swapElems values i j).drop n = values.drop n := by
  unfold swapElems
  rw [List.drop_set_of_lt hjn, List.drop_set_of_lt hin]

theorem swapElems_perm [Inhabited α] [BEq α] [LawfulBEq α]
    (values : List α) {i j : Nat}
    (hi : i < values.length) (hj : j < values.length) :
    (swapElems values i j).Perm values := by
  rw [List.perm_iff_count]
  intro value
  simp only [swapElems]
  rw [getElem!_pos values i hi, getElem!_pos values j hj]
  have hlen : (values.set i values[j]).length = values.length := List.length_set
  rw [List.count_set (hlen ▸ hj), List.count_set hi]
  have hset_j : ((values.set i values[j])[j] == value) = (values[j] == value) := by
    congr 1
    simp [List.getElem_set]
  rw [hset_j]
  have hle : (if values[i] == value then 1 else 0) ≤ values.count value := by
    split_ifs with h
    · exact List.count_pos_iff.mpr
        ((beq_iff_eq.mp h) ▸ List.getElem_mem hi)
    · exact Nat.zero_le _
  omega

end List
