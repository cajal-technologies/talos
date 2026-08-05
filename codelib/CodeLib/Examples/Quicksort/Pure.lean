import CodeLib.Examples.Quicksort

/-!
# Pure mathematics used by the quicksort proof

This file contains no Iris assertions or machine states.
-/

namespace Wasm.Examples.Quicksort

-- no List.swap in Mathlib; Function.swap resolves that name instead
def swapElems (l : List UInt32) (i j : Nat) : List UInt32 :=
  (l.set i (l[j]!)).set j (l[i]!)

theorem swapElems_length (l : List UInt32) (i j : Nat) :
    (swapElems l i j).length = l.length := by
  unfold swapElems; simp [List.length_set]

theorem swapElems_get_i (l : List UInt32) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) :
    (swapElems l i j)[i]! = l[j]! := by
  unfold swapElems
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split_ifs; all_goals simp_all

theorem swapElems_get_j (l : List UInt32) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) :
    (swapElems l i j)[j]! = l[i]! := by
  unfold swapElems
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split_ifs; all_goals simp_all

theorem swapElems_get_other (l : List UInt32) {i j k : Nat}
    (hki : k ≠ i) (hkj : k ≠ j) :
    (swapElems l i j)[k]! = l[k]! := by
  unfold swapElems
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split_ifs; all_goals simp_all

theorem swapElems_take_of_le (l : List UInt32) {i j n : Nat}
    (hin : n ≤ i) (hjn : n ≤ j) :
    (swapElems l i j).take n = l.take n := by
  unfold swapElems; rw [List.take_set, List.take_set]
  have hlen : (List.take n l).length ≤ n := List.length_take_le n l
  rw [List.set_eq_of_length_le (by rw [List.length_set]; exact Nat.le_trans hlen hjn),
      List.set_eq_of_length_le (Nat.le_trans hlen hin)]

theorem swapElems_drop_of_lt (l : List UInt32) {i j n : Nat}
    (hin : i < n) (hjn : j < n) :
    (swapElems l i j).drop n = l.drop n := by
  unfold swapElems
  rw [List.drop_set_of_lt hjn, List.drop_set_of_lt hin]

theorem swapElems_perm (l : List UInt32) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) :
    (swapElems l i j).Perm l := by
  rw [List.perm_iff_count]; intro b; simp only [swapElems]
  have hi_eq : l[i]! = l[i] := getElem!_pos l i hi
  have hj_eq : l[j]! = l[j] := getElem!_pos l j hj
  rw [hi_eq, hj_eq]
  have hlen1 : (l.set i l[j]).length = l.length := List.length_set
  rw [List.count_set (hlen1 ▸ hj), List.count_set hi]
  have hset_j : ((l.set i l[j])[j] == b) = (l[j] == b) := by
    congr 1; simp [List.getElem_set]
  rw [hset_j]
  have hle : (if l[i] == b then 1 else 0) ≤ l.count b := by
    split_ifs with h
    · exact List.count_pos_iff.mpr ((beq_iff_eq.mp h) ▸ List.getElem_mem hi)
    · exact Nat.zero_le _
  omega

private theorem take_segment_drop {values : List UInt32} {start stop : Nat}
    (hstart : start ≤ stop) :
    values.take start ++ segment values start stop ++ values.drop stop = values := by
  have hstop : start + (stop - start) = stop := Nat.add_sub_of_le hstart
  rw [segment, ← List.take_add, hstop]
  exact List.take_append_drop stop values

private theorem segment_append {values : List UInt32} {start mid stop : Nat}
    (hstart : start ≤ mid) (hmid : mid ≤ stop) :
    segment values start mid ++ segment values mid stop = segment values start stop := by
  simp only [segment]
  have hdrop : values.drop mid = (values.drop start).drop (mid - start) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hdrop, ← List.take_add]; congr 1; omega

private theorem sorted_of_length_le_one {values : List UInt32}
    (h : values.length ≤ 1) : values.Pairwise (· ≤ ·) := by
  match values, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

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
  rw [List.getElem_drop' (by omega)]
  exact hkval

private theorem uint32_le_of_lt {a b : UInt32} (h : a < b) : a ≤ b := by
  change a.toNat < b.toNat at h; change a.toNat ≤ b.toNat; exact Nat.le_of_lt h

private theorem uint32_le_trans {a b c : UInt32} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  change a.toNat ≤ b.toNat at h1; change b.toNat ≤ c.toNat at h2
  change a.toNat ≤ c.toNat; exact Nat.le_trans h1 h2

private theorem compose_sorted (output : List UInt32) (lo hi p : Nat)
    (hlo : lo ≤ p) (hp : p < hi) (hhi : hi ≤ output.length)
    (hleft : List.Pairwise (· ≤ ·) (segment output lo p))
    (hright : List.Pairwise (· ≤ ·) (segment output (p + 1) hi))
    (hleft_cond : ∀ x ∈ segment output lo p, x ≤ output[p]!)
    (hright_cond : ∀ x ∈ segment output (p + 1) hi, x > output[p]!) :
    List.Pairwise (· ≤ ·) (segment output lo hi) := by
  rw [show segment output lo hi = segment output lo p ++ output[p]! :: segment output (p + 1) hi
      from by rw [← segment_cons_pivot hp hhi, segment_append hlo (by omega)]]
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hleft, ⟨?_, hright⟩, ?_⟩
  · intro y hy; exact uint32_le_of_lt (hright_cond y hy)
  · intro x hx y hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hleft_cond x hx
    · exact uint32_le_trans (hleft_cond x hx) (uint32_le_of_lt (hright_cond y hy))

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
    PartitionLoopInvariant input (swapElems current i j) lo hi (i + 1) (j + 1) pivot := by
  unfold PartitionLoopInvariant at h ⊢
  rcases h with ⟨hli, hij, hjhi, hhilen, hlen, htake_lo, hdrop_hi, hpivot, hperm,
    hle_zone, hgt_zone⟩
  have hilen : i < current.length := by omega
  have hjlen : j < current.length := by omega
  refine ⟨by omega, by omega, by omega, hhilen,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [swapElems_length]; exact hlen
  · rw [swapElems_take_of_le (hin := by omega) (hjn := by omega)]; exact htake_lo
  · rw [swapElems_drop_of_lt (hin := by omega) (hjn := by omega)]; exact hdrop_hi
  · rw [swapElems_get_other (hki := by omega) (hkj := by omega)]; exact hpivot
  · -- permutation
    have hlo_hi : lo ≤ hi := by omega
    have htake : (swapElems current i j).take lo = current.take lo :=
      swapElems_take_of_le current (hin := by omega) (hjn := by omega)
    have hdrop : (swapElems current i j).drop hi = current.drop hi :=
      swapElems_drop_of_lt current (hin := by omega) (hjn := by omega)
    have hswap_perm := swapElems_perm current hilen hjlen
    have heq1 : current.take lo ++ segment (swapElems current i j) lo hi ++ current.drop hi
        = swapElems current i j := by
      have h := take_segment_drop (values := swapElems current i j) hlo_hi
      rwa [htake, hdrop] at h
    have heq2 : current.take lo ++ segment current lo hi ++ current.drop hi = current :=
      take_segment_drop hlo_hi
    have hperm_full :
        (current.take lo ++ segment (swapElems current i j) lo hi ++ current.drop hi).Perm
        (current.take lo ++ segment current lo hi ++ current.drop hi) := by
      rw [heq1, heq2]; exact hswap_perm
    have hseg_perm : (segment (swapElems current i j) lo hi).Perm (segment current lo hi) :=
      List.perm_append_left_iff (current.take lo) |>.mp
        (List.perm_append_right_iff (current.drop hi) |>.mp hperm_full)
    exact hperm.trans hseg_perm.symm
  · intro k hlo hki1
    by_cases hki : k = i
    · subst hki
      rw [swapElems_get_i current hilen hjlen]
      exact UInt32.not_lt.mp hle
    · rw [swapElems_get_other (hki := hki) (hkj := by omega)]
      exact hle_zone k hlo (by omega)
  · intro k hik hkj1
    by_cases hkj : k = j
    · subst hkj
      rw [swapElems_get_j current hilen hjlen]
      exact hgt_zone i (Nat.le_refl i) (by omega)
    · rw [swapElems_get_other (hki := by omega) (hkj := hkj)]
      exact hgt_zone k (by omega) (by omega)

theorem PartitionLoopInvariant.placePivot
    {input current : List UInt32} {lo hi i : Nat} {pivot : UInt32}
    (h : PartitionLoopInvariant input current lo hi i (hi - 1) pivot)
    (hhi_pos : 0 < hi) :
    PartitionRange input (swapElems current i (hi - 1)) lo hi i := by
  rcases h with ⟨hli, hij, _, hhilen, hlen, htake_lo, hdrop_hi, hpivot, hperm,
    hle_zone, hgt_zone⟩
  have hilen : i < current.length := by omega
  have hhm1len : hi - 1 < current.length := by omega
  have hswaplen := swapElems_length current i (hi - 1)
  have hlo_hi : lo ≤ hi := by omega
  -- permutation field (same take_segment_drop cancellation as swapStep)
  have htake : (swapElems current i (hi - 1)).take lo = current.take lo :=
    swapElems_take_of_le current (hin := by omega) (hjn := by omega)
  have hdrop : (swapElems current i (hi - 1)).drop hi = current.drop hi :=
    swapElems_drop_of_lt current (hin := by omega) (hjn := by omega)
  have hswap_perm := swapElems_perm current hilen hhm1len
  have heq1 : current.take lo ++ segment (swapElems current i (hi - 1)) lo hi ++ current.drop hi
      = swapElems current i (hi - 1) := by
    have h := take_segment_drop (values := swapElems current i (hi - 1)) hlo_hi
    rwa [htake, hdrop] at h
  have heq2 : current.take lo ++ segment current lo hi ++ current.drop hi = current :=
    take_segment_drop hlo_hi
  have hperm_full :
      (current.take lo ++ segment (swapElems current i (hi - 1)) lo hi ++ current.drop hi).Perm
      (current.take lo ++ segment current lo hi ++ current.drop hi) := by
    rw [heq1, heq2]; exact hswap_perm
  have hseg_perm : (segment (swapElems current i (hi - 1)) lo hi).Perm (segment current lo hi) :=
    List.perm_append_left_iff (current.take lo) |>.mp
      (List.perm_append_right_iff (current.drop hi) |>.mp hperm_full)
  have hpiv_at_i : (swapElems current i (hi - 1))[i]! = pivot := by
    rw [swapElems_get_i current hilen hhm1len]; exact hpivot
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
    rw [← hkval, swapElems_get_other (hki := by omega) (hkj := by omega)]
    exact hle_zone k hlo hki
  · -- right: ∀ x ∈ segment output (i+1) hi, x > output[i]!
    intro x hx
    rw [hpiv_at_i]
    obtain ⟨k, hki1, hkhi, hkval⟩ := mem_segment (hi := hi) (by omega) hx
    rw [← hkval]
    by_cases hkhim1 : k = hi - 1
    · rw [hkhim1, swapElems_get_j current hilen hhm1len]
      exact hgt_zone i (le_refl i) (by omega)
    · rw [swapElems_get_other (hki := by omega) (hkj := hkhim1)]
      exact hgt_zone k (by omega) (by omega)

theorem quicksort_base
    (input : List UInt32) (lo hi : Nat)
    (_ : hi ≤ input.length)
    (hbase : hi - lo < 2) :
    Sorted (segment input lo hi) := by
  apply sorted_of_length_le_one
  simp [segment, List.length_drop]
  omega

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

private theorem segment_take_drop_eq (l : List UInt32) (lo hi : Nat) (hlohi : lo ≤ hi) :
    segment l lo hi = (l.take hi).drop lo := by
  induction l generalizing lo hi with
  | nil => simp [segment]
  | cons head l ih =>
    cases lo with
    | zero => simp [segment]
    | succ lo =>
      cases hi with
      | zero => omega
      | succ hi =>
        simp only [segment, List.take_succ_cons, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
        exact ih lo hi (by omega)

private theorem segment_eq_of_take {a b : List UInt32} {lo hi k : Nat}
    (hlohi : lo ≤ hi) (hhik : hi ≤ k) (htake : a.take k = b.take k) :
    segment a lo hi = segment b lo hi := by
  rw [segment_take_drop_eq a lo hi hlohi, segment_take_drop_eq b lo hi hlohi]
  congr 1
  rw [show a.take hi = (a.take k).take hi from by
        rw [List.take_take]; simp [Nat.min_eq_left hhik],
      show b.take hi = (b.take k).take hi from by
        rw [List.take_take]; simp [Nat.min_eq_left hhik],
      htake]

private theorem segment_eq_of_drop {a b : List UInt32} {lo hi k : Nat}
    (hklo : k ≤ lo) (hdrop : a.drop k = b.drop k) :
    segment a lo hi = segment b lo hi := by
  simp only [segment]
  congr 1
  have step : ∀ l : List UInt32, l.drop lo = (l.drop k).drop (lo - k) := fun l => by
    rw [List.drop_drop]; congr 1; omega
  rw [step a, step b, hdrop]

private theorem getElem!_eq_of_take {a b : List UInt32} {k i : Nat}
    (hik : i < k) (htake : a.take k = b.take k) :
    a[i]! = b[i]! := by
  simp only [List.getElem!_eq_getElem?_getD]
  rw [show a[i]? = (a.take k)[i]? from by simp [List.getElem?_take, hik],
      show b[i]? = (b.take k)[i]? from by simp [List.getElem?_take, hik],
      htake]

private theorem getElem!_eq_of_drop {a b : List UInt32} {k i : Nat}
    (hki : k ≤ i) (hdrop : a.drop k = b.drop k) :
    a[i]! = b[i]! := by
  simp only [List.getElem!_eq_getElem?_getD]
  have ha : a[i]? = (a.drop k)[i - k]? := by
    rw [List.getElem?_drop]; congr 1; omega
  have hb : b[i]? = (b.drop k)[i - k]? := by
    rw [List.getElem?_drop]; congr 1; omega
  rw [ha, hb, hdrop]

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
    segment_eq_of_take (by omega) (by omega) htake_r
  have hseg_l_p1_hi : segment out_l (pivotIdx + 1) hi = segment output_p (pivotIdx + 1) hi :=
    segment_eq_of_drop (by omega) hdrop_l
  -- pivot element equalities
  have hpiv_l : out_l[pivotIdx]! = output_p[pivotIdx]! :=
    getElem!_eq_of_drop (le_refl _) hdrop_l
  have hpiv_r : out_r[pivotIdx]! = out_l[pivotIdx]! :=
    getElem!_eq_of_take (by omega) htake_r
  -- perm of whole segment
  have hperm_op_r : List.Perm (segment output_p lo hi) (segment out_r lo hi) := by
    have lhs_eq : segment output_p lo hi =
        segment output_p lo pivotIdx ++ output_p[pivotIdx]! :: segment output_p (pivotIdx + 1) hi := by
      rw [← segment_cons_pivot hphi (by omega), segment_append hlo (by omega)]
    have rhs_eq : segment out_r lo hi =
        segment out_r lo pivotIdx ++ out_r[pivotIdx]! :: segment out_r (pivotIdx + 1) hi := by
      rw [← segment_cons_pivot hphi hhilen_r, segment_append hlo (by omega)]
    rw [lhs_eq, rhs_eq, hseg_r_lo_p, hpiv_r, ← hpiv_l, ← hseg_l_p1_hi]
    exact hperm_l.append (List.Perm.cons _ hperm_r)
  -- take lo chain
  have htake_r_lo : out_r.take lo = out_l.take lo := by
    have := congr_arg (·.take lo) htake_r
    simp only [List.take_take, Nat.min_eq_left (by omega : lo ≤ pivotIdx + 1)] at this
    exact this
  -- drop hi chain
  have hdrop_l_hi : out_l.drop hi = output_p.drop hi := by
    have step : ∀ l : List UInt32, l.drop hi = (l.drop pivotIdx).drop (hi - pivotIdx) := fun l => by
      rw [List.drop_drop]; congr 1; omega
    rw [step out_l, step output_p, hdrop_l]
  exact ⟨hlo, hphi, hhilen, by omega,
    by rw [htake_r_lo, htake_l, htake_p],
    by rw [hdrop_r, hdrop_l_hi, hdrop_p],
    hperm_p.trans hperm_op_r,
    by rw [hseg_r_lo_p, hpiv_r, hpiv_l]
       intro x hx; exact hleft_p x (hperm_l.symm.subset hx),
    by intro x hx; rw [hpiv_r, hpiv_l]
       apply hright_p; rw [← hseg_l_p1_hi]; exact hperm_r.symm.subset hx⟩

theorem segment_sorted_of_take_eq {a b : List UInt32} {lo hi k : Nat}
    (hlohi : lo ≤ hi) (hhik : hi ≤ k) (htake : a.take k = b.take k)
    (h : Sorted (segment b lo hi)) : Sorted (segment a lo hi) := by
  rw [segment_eq_of_take hlohi hhik htake]; exact h

end Wasm.Examples.Quicksort
