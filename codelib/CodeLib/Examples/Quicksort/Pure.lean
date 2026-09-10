import CodeLib.Examples.Quicksort
import CodeLib.List

/-!
# Pure mathematics used by the quicksort proof

This file contains no Iris assertions or machine states.
-/

namespace Wasm.Examples.Quicksort

abbrev swapElems : List UInt32 → Nat → Nat → List UInt32 := List.swapElems

private theorem segment_cons_pivot {values : List UInt32} {p hi : Nat}
    (hphi : p < hi) (hhilen : hi ≤ values.length) :
    segment values p hi = values[p]! :: segment values (p + 1) hi := by
  simp only [segment]
  have hp : p < values.length := Nat.lt_of_lt_of_le hphi hhilen
  rw [List.drop_eq_getElem_cons hp, show hi - p = (hi - p - 1) + 1 from by omega,
      List.take_succ_cons, getElem!_pos values p hp]
  congr 1

private theorem mem_segment {output : List UInt32} {lo hi : Nat} {x : UInt32}
    (hhi : hi ≤ output.length) (hx : x ∈ segment output lo hi) :
    ∃ k, lo ≤ k ∧ k < hi ∧ output[k]! = x := by
  simp only [segment] at hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨k, hklen, hkval⟩ := hx
  have hkdiff : k < hi - lo := Nat.lt_of_lt_of_le hklen (List.length_take_le _ _)
  refine ⟨lo + k, Nat.le_add_right lo k, by omega, ?_⟩
  rw [getElem!_pos output (lo + k) (by omega)]
  rw [List.getElem_take] at hkval
  rw [List.getElem_drop' (by omega)]; exact hkval

private theorem compose_sorted (output : List UInt32) (lo hi p : Nat)
    (hlo : lo ≤ p) (hp : p < hi) (hhi : hi ≤ output.length)
    (hleft : List.Pairwise (· ≤ ·) (segment output lo p))
    (hright : List.Pairwise (· ≤ ·) (segment output (p + 1) hi))
    (hleft_cond : ∀ x ∈ segment output lo p, x ≤ output[p]!)
    (hright_cond : ∀ x ∈ segment output (p + 1) hi, x > output[p]!) :
    List.Pairwise (· ≤ ·) (segment output lo hi) := by
  rw [show segment output lo hi = segment output lo p ++ output[p]! :: segment output (p + 1) hi
      from by rw [← segment_cons_pivot hp hhi, List.extract_append hlo (by omega)]]
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hleft, ⟨?_, hright⟩, ?_⟩
  · intro y hy; exact UInt32.le_of_lt (hright_cond y hy)
  · intro x hx y hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hleft_cond x hx
    · exact UInt32.le_trans (hleft_cond x hx) (UInt32.le_of_lt (hright_cond y hy))

/-- loop invariant for the lomuto partition scan:
    [lo, i) ≤ pivot, [i, j) > pivot, arr[hi-1] = pivot -/
def PartitionLoopInvariant
    (input current : List UInt32) (lo hi i j : Nat) (pivot : UInt32) : Prop :=
  lo ≤ i ∧ i ≤ j ∧ j ≤ hi - 1 ∧ hi ≤ input.length ∧
  current.length = input.length ∧
  current.take lo = input.take lo ∧
  current.drop hi = input.drop hi ∧
  current[hi - 1]! = pivot ∧
  List.Perm (segment input lo hi) (segment current lo hi) ∧
  (∀ k, lo ≤ k → k < i → current[k]! ≤ pivot) ∧
  (∀ k, i ≤ k → k < j → pivot < current[k]!)

theorem partitionLoopInvariant_start
    (input : List UInt32) (lo hi : Nat) (pivot : UInt32)
    (hbounds : lo < hi ∧ hi ≤ input.length)
    (hpivot : input[hi - 1]! = pivot) :
    PartitionLoopInvariant input input lo hi lo lo pivot := by
  obtain ⟨hlohi, hilen⟩ := hbounds
  refine ⟨le_refl lo, le_refl lo, by omega, hilen, rfl, rfl, rfl, hpivot,
    List.Perm.refl _,
    fun k hk hlt => by omega,
    fun k hk hlt => by omega⟩

theorem PartitionLoopInvariant.skipStep
    {input current : List UInt32} {lo hi i j : Nat} {pivot : UInt32}
    (h : PartitionLoopInvariant input current lo hi i j pivot)
    (hj : j < hi - 1)
    (hgt : pivot < current[j]!) :
    PartitionLoopInvariant input current lo hi i (j + 1) pivot := by
  unfold PartitionLoopInvariant at h ⊢
  obtain ⟨hli, hij, hjh, hilen, hlen, htake, hdrop, hpiv, hperm, hle, hgt'⟩ := h
  refine ⟨hli, by omega, by omega, hilen, hlen, htake, hdrop, hpiv, hperm, hle,
    fun k hik hkj1 => ?_⟩
  by_cases hkj : k = j
  · subst hkj; exact hgt
  · exact hgt' k hik (by omega)

theorem PartitionLoopInvariant.swapStep
    {input current : List UInt32} {lo hi i j : Nat} {pivot : UInt32}
    (h : PartitionLoopInvariant input current lo hi i j pivot)
    (hj : j < hi - 1)
    (hle : ¬ pivot < current[j]!) :
    PartitionLoopInvariant input (List.swapElems current i j) lo hi (i + 1) (j + 1) pivot := by
  unfold PartitionLoopInvariant at h ⊢
  rcases h with ⟨hli, hij, hjhi, hhilen, hlen, htake_lo, hdrop_hi, hpivot, hperm,
    hle_zone, hgt_zone⟩
  have hilen : i < current.length := by omega
  have hjlen : j < current.length := by omega
  refine ⟨by omega, by omega, by omega, hhilen,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.swapElems_length]; exact hlen
  · rw [List.swapElems_take_of_le (hin := by omega) (hjn := by omega)]; exact htake_lo
  · rw [List.swapElems_drop_of_lt (hin := by omega) (hjn := by omega)]; exact hdrop_hi
  · rw [List.swapElems_get_other (hki := by omega) (hkj := by omega)]; exact hpivot
  · -- permutation
    have hlo_hi : lo ≤ hi := by omega
    have htake : (List.swapElems current i j).take lo = current.take lo :=
      List.swapElems_take_of_le current (hin := by omega) (hjn := by omega)
    have hdrop : (List.swapElems current i j).drop hi = current.drop hi :=
      List.swapElems_drop_of_lt current (hin := by omega) (hjn := by omega)
    have hswap_perm := List.swapElems_perm current hilen hjlen
    have heq1 : current.take lo ++ segment (List.swapElems current i j) lo hi ++ current.drop hi
        = List.swapElems current i j := by
      have h := List.take_extract_drop (values := List.swapElems current i j) hlo_hi
      rwa [htake, hdrop] at h
    have heq2 : current.take lo ++ segment current lo hi ++ current.drop hi = current :=
      List.take_extract_drop hlo_hi
    have hperm_full :
        (current.take lo ++ segment (List.swapElems current i j) lo hi ++ current.drop hi).Perm
        (current.take lo ++ segment current lo hi ++ current.drop hi) := by
      rw [heq1, heq2]; exact hswap_perm
    have hseg_perm : (segment (List.swapElems current i j) lo hi).Perm (segment current lo hi) :=
      List.perm_append_left_iff (current.take lo) |>.mp
        (List.perm_append_right_iff (current.drop hi) |>.mp hperm_full)
    exact hperm.trans hseg_perm.symm
  · intro k hlo hki1
    by_cases hki : k = i
    · subst hki; rw [List.swapElems_get_i current hilen hjlen]
      exact UInt32.not_lt.mp hle
    · rw [List.swapElems_get_other (hki := hki) (hkj := by omega)]; exact hle_zone k hlo (by omega)
  · intro k hik hkj1
    by_cases hkj : k = j
    · subst hkj; rw [List.swapElems_get_j current hilen hjlen]
      exact hgt_zone i (Nat.le_refl i) (by omega)
    · rw [List.swapElems_get_other (hki := by omega) (hkj := hkj)]
      exact hgt_zone k (by omega) (by omega)

theorem PartitionLoopInvariant.placePivot
    {input current : List UInt32} {lo hi i : Nat} {pivot : UInt32}
    (h : PartitionLoopInvariant input current lo hi i (hi - 1) pivot)
    (hhi_pos : 0 < hi) :
    PartitionRange input (List.swapElems current i (hi - 1)) lo hi i := by
  rcases h with ⟨hli, hij, _, hhilen, hlen, htake_lo, hdrop_hi, hpivot, hperm,
    hle_zone, hgt_zone⟩
  have hilen : i < current.length := by omega
  have hhm1len : hi - 1 < current.length := by omega
  have hswaplen := List.swapElems_length current i (hi - 1)
  have hlo_hi : lo ≤ hi := by omega
  -- permutation field (same List.take_extract_drop cancellation as swapStep)
  have htake : (List.swapElems current i (hi - 1)).take lo = current.take lo :=
    List.swapElems_take_of_le current (hin := by omega) (hjn := by omega)
  have hdrop : (List.swapElems current i (hi - 1)).drop hi = current.drop hi :=
    List.swapElems_drop_of_lt current (hin := by omega) (hjn := by omega)
  have hswap_perm := List.swapElems_perm current hilen hhm1len
  have heq1 :
      current.take lo ++ segment (List.swapElems current i (hi - 1)) lo hi ++
        current.drop hi = List.swapElems current i (hi - 1) := by
    have h := List.take_extract_drop (values := List.swapElems current i (hi - 1)) hlo_hi
    rwa [htake, hdrop] at h
  have heq2 : current.take lo ++ segment current lo hi ++ current.drop hi = current :=
    List.take_extract_drop hlo_hi
  have hperm_full :
      (current.take lo ++ segment (List.swapElems current i (hi - 1)) lo hi ++ current.drop hi).Perm
      (current.take lo ++ segment current lo hi ++ current.drop hi) := by
    rw [heq1, heq2]; exact hswap_perm
  have hseg_perm :
      (segment (List.swapElems current i (hi - 1)) lo hi).Perm
        (segment current lo hi) :=
    List.perm_append_left_iff (current.take lo) |>.mp
      (List.perm_append_right_iff (current.drop hi) |>.mp hperm_full)
  have hpiv_at_i : (List.swapElems current i (hi - 1))[i]! = pivot := by
    rw [List.swapElems_get_i current hilen hhm1len]; exact hpivot
  refine ⟨hli, by omega, hhilen,
    by rw [hswaplen]; exact hlen,
    by rw [htake]; exact htake_lo,
    by rw [hdrop]; exact hdrop_hi,
    hperm.trans hseg_perm.symm,
    ?_, ?_⟩
  · -- left: ∀ x ∈ segment output lo i, x ≤ output[i]!
    intro x hx
    rw [hpiv_at_i]
    obtain ⟨k, hlo, hki, hkval⟩ := mem_segment (hi := i) (by omega) hx
    rw [← hkval, List.swapElems_get_other (hki := by omega) (hkj := by omega)]
    exact hle_zone k hlo hki
  · -- right: ∀ x ∈ segment output (i+1) hi, x > output[i]!
    intro x hx
    rw [hpiv_at_i]
    obtain ⟨k, hki1, hkhi, hkval⟩ := mem_segment (hi := hi) (by omega) hx
    rw [← hkval]
    by_cases hkhim1 : k = hi - 1
    · rw [hkhim1, List.swapElems_get_j current hilen hhm1len]
      exact hgt_zone i (le_refl i) (by omega)
    · rw [List.swapElems_get_other (hki := by omega) (hkj := hkhim1)]
      exact hgt_zone k (by omega) (by omega)

theorem quicksort_base
    (input : List UInt32) (lo hi : Nat)
    (_ : hi ≤ input.length)
    (hbase : hi - lo < 2) :
    Sorted (segment input lo hi) :=
  List.pairwise_of_length_le_one (by simp [segment, List.length_drop]; omega)

theorem quicksort_compose
    (input output : List UInt32) (lo hi p : Nat)
    (hpartition : PartitionRange input output lo hi p)
    (hleft : Sorted (segment output lo p))
    (hright : Sorted (segment output (p + 1) hi)) :
    Sorted (segment output lo hi) ∧
    List.Perm (segment input lo hi) (segment output lo hi) := by
  obtain ⟨hlo, hp, hhi, hlen, htake, hdrop, hperm, hleft_cond, hright_cond⟩ := hpartition
  exact ⟨compose_sorted output lo hi p hlo hp (hlen.symm ▸ hhi) hleft hright
           hleft_cond hright_cond,
         hperm⟩

theorem partitionRange_after_sorts
    {values output_p out_l out_r : List UInt32} {lo hi pivotIdx : Nat}
    (hpart : PartitionRange values output_p lo hi pivotIdx)
    (hlen_l : out_l.length = output_p.length)
    (htake_l : out_l.take lo = output_p.take lo)
    (hdrop_l : out_l.drop pivotIdx = output_p.drop pivotIdx)
    (hperm_l : List.Perm (segment output_p lo pivotIdx) (segment out_l lo pivotIdx))
    (hlen_r : out_r.length = out_l.length)
    (htake_r : out_r.take (pivotIdx + 1) = out_l.take (pivotIdx + 1))
    (hdrop_r : out_r.drop hi = out_l.drop hi)
    (hperm_r : List.Perm (segment out_l (pivotIdx + 1) hi) (segment out_r (pivotIdx + 1) hi)) :
    PartitionRange values out_r lo hi pivotIdx := by
  obtain ⟨hlo, hphi, hhilen, hlen_p, htake_p, hdrop_p, hperm_p, hleft_p, hright_p⟩ := hpart
  have hhilen_r : hi ≤ out_r.length := by omega
  -- segment equalities
  have hseg_r_lo_p : segment out_r lo pivotIdx = segment out_l lo pivotIdx :=
    List.extract_eq_of_take_eq (by omega) htake_r
  have hseg_l_p1_hi : segment out_l (pivotIdx + 1) hi = segment output_p (pivotIdx + 1) hi :=
    List.extract_eq_of_drop_eq (by omega) hdrop_l
  -- pivot element equalities
  have hpiv_l : out_l[pivotIdx]! = output_p[pivotIdx]! :=
    List.getElem!_eq_of_drop_eq (le_refl _) hdrop_l
  have hpiv_r : out_r[pivotIdx]! = out_l[pivotIdx]! :=
    List.getElem!_eq_of_take_eq (by omega) htake_r
  -- perm of whole segment
  have hperm_op_r : List.Perm (segment output_p lo hi) (segment out_r lo hi) := by
    have lhs_eq : segment output_p lo hi =
        segment output_p lo pivotIdx ++ output_p[pivotIdx]! :: segment output_p (pivotIdx + 1) hi := by
      rw [← segment_cons_pivot hphi (by omega), List.extract_append hlo (by omega)]
    have rhs_eq : segment out_r lo hi =
        segment out_r lo pivotIdx ++ out_r[pivotIdx]! :: segment out_r (pivotIdx + 1) hi := by
      rw [← segment_cons_pivot hphi hhilen_r, List.extract_append hlo (by omega)]
    rw [lhs_eq, rhs_eq, hseg_r_lo_p, hpiv_r, ← hpiv_l, ← hseg_l_p1_hi]
    exact hperm_l.append (List.Perm.cons _ hperm_r)
  -- take lo chain
  have htake_r_lo := List.take_eq_of_take_eq (by omega : lo ≤ pivotIdx + 1) htake_r
  -- drop hi chain
  have hdrop_l_hi := List.drop_eq_of_drop_eq (by omega : pivotIdx ≤ hi) hdrop_l
  exact ⟨hlo, hphi, hhilen, by omega,
    by rw [htake_r_lo, htake_l, htake_p],
    by rw [hdrop_r, hdrop_l_hi, hdrop_p],
    hperm_p.trans hperm_op_r,
    by rw [hseg_r_lo_p, hpiv_r, hpiv_l]
       intro x hx; exact hleft_p x (hperm_l.symm.subset hx),
    by intro x hx; rw [hpiv_r, hpiv_l]
       apply hright_p; rw [← hseg_l_p1_hi]; exact hperm_r.symm.subset hx⟩

theorem segment_sorted_of_take_eq {a b : List UInt32} {lo hi k : Nat}
    (hhik : hi ≤ k) (htake : a.take k = b.take k)
    (h : Sorted (segment b lo hi)) : Sorted (segment a lo hi) := by
  change Sorted (a.extract lo hi)
  change Sorted (b.extract lo hi) at h
  rw [List.extract_eq_of_take_eq hhik htake]; exact h

end Wasm.Examples.Quicksort
