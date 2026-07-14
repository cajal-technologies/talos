import Project.MergeSort.Spec
import Project.MergeSort.Framing
import Mathlib.Data.List.Sort

namespace Project.MergeSort.Spec

open Wasm Project.MergeSort.Framing

/-- The merge of two sorted lists is sorted. -/
theorem merge_sorted {left right : List UInt32}
    (hl : left.Pairwise (· ≤ ·)) (hr : right.Pairwise (· ≤ ·)) :
    (List.merge left right (· ≤ ·)).Pairwise (· ≤ ·) := by
  simpa using hl.merge hr

/-- The merge of two lists is a permutation of their concatenation. -/
theorem merge_perm (left right : List UInt32) :
    (List.merge left right (· ≤ ·)).Perm (left ++ right) :=
  @List.merge_perm_append UInt32 (· ≤ ·) left right

/-- If both halves are sorted permutations of their originals, the merged result
    is sorted and a permutation of both originals concatenated. -/
theorem sort_recursive
    {left right left_orig right_orig : List UInt32}
    (hl_sorted : left.Pairwise (· ≤ ·))
    (hr_sorted : right.Pairwise (· ≤ ·))
    (hl_perm : left.Perm left_orig)
    (hr_perm : right.Perm right_orig) :
    (List.merge left right (· ≤ ·)).Pairwise (· ≤ ·) ∧
    (List.merge left right (· ≤ ·)).Perm (left_orig ++ right_orig) :=
  ⟨merge_sorted hl_sorted hr_sorted,
   (merge_perm left right).trans (hl_perm.append hr_perm)⟩

/-- `wordsAt` can be split at any position `mid ≤ n` into the first `mid` words
    and the remaining `n - mid` words at the shifted base. -/
theorem wordsAt_split (m : Mem) (ptr : UInt32) (n mid : Nat) (h : mid ≤ n) :
    wordsAt m ptr n =
      wordsAt m ptr mid ++ wordsAt m (ptr + 4 * UInt32.ofNat mid) (n - mid) := by
  simp only [wordsAt]
  conv_lhs => rw [show n = mid + (n - mid) from (Nat.add_sub_cancel' h).symm]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  apply congrArg (m.read32)
  rw [UInt32.ofNat_add, UInt32.mul_add, ← UInt32.add_assoc]

theorem merge_cons_le {x y : UInt32} {xs ys : List UInt32} (h : x ≤ y) :
    List.merge (x :: xs) (y :: ys) (· ≤ ·) = x :: List.merge xs (y :: ys) (· ≤ ·) := by
  simp [h]

theorem merge_cons_gt {x y : UInt32} {xs ys : List UInt32} (h : ¬(x ≤ y)) :
    List.merge (x :: xs) (y :: ys) (· ≤ ·) = y :: List.merge (x :: xs) ys (· ≤ ·) := by
  simp [h]

theorem wordsAt_drop_eq (m : Wasm.Mem) (base : UInt32) (n i : Nat) :
    (wordsAt m base n).drop i = wordsAt m (base + 4 * UInt32.ofNat i) (n - i) := by
  apply List.ext_getElem
  · simp [wordsAt_length]
  · intro k hk1 hk2
    have hi : i + k < n := by simp [List.length_drop, wordsAt_length] at hk1; omega
    rw [List.getElem_drop]
    simp only [wordsAt]
    simp only [List.getElem_map, List.getElem_range]
    congr 1
    rw [UInt32.ofNat_add, UInt32.mul_add, ← UInt32.add_assoc]

theorem wordsAt_write32_extend (m : Wasm.Mem) (base : UInt32) (k : Nat) (v : UInt32)
    (h_addr : ∀ i, i ≤ k → (base + 4 * UInt32.ofNat i).toNat = base.toNat + 4 * i)
    (h_bnd : base.toNat + 4 * k + 4 ≤ m.pages * 65536)
    (hub : m.pages * 65536 ≤ 4294967296) :
    wordsAt (m.write32 (base + 4 * UInt32.ofNat k) v) base (k + 1) =
      wordsAt m base k ++ [v] := by
  have g1 : wordsAt (m.write32 (base + 4 * UInt32.ofNat k) v) base k = wordsAt m base k := by
    apply wordsAt_write32_of_disjoint
    · omega
    · right; rw [h_addr k (le_refl k)]
  have g2 : wordsAt (m.write32 (base + 4 * UInt32.ofNat k) v) (base + 4 * UInt32.ofNat k) 1 = [v] := by
    simp [wordsAt, Mem.read32_write32_same]
  conv_lhs => rw [wordsAt_split _ _ _ k (by omega)]
  simp only [show k + 1 - k = 1 from by omega, g1, g2]

theorem merge_nil_left (xs : List UInt32) : List.merge [] xs (· ≤ ·) = xs := by
  simp [List.merge]

theorem merge_nil_right (xs : List UInt32) : List.merge xs [] (· ≤ ·) = xs := by
  induction xs with
  | nil => simp [List.merge]
  | cons x xs ih => simp [List.merge, ih]

end Project.MergeSort.Spec
