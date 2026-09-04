import CodeLib.Examples.SelectionSort
import CodeLib.List
import CodeLib.UInt64
import Mathlib.Data.List.Sort

/-! Pure list facts shared by the recursive and loop proofs. -/

namespace Wasm.Examples.SelectionSort

def Sorted (values : List UInt64) : Prop :=
  values.Pairwise (· ≤ ·)

abbrev swapElems : List UInt64 → Nat → Nat → List UInt64 := List.swapElems

/-- `best` is a minimum of the half-open range `[start, scan)`. -/
def MinScan (values : List UInt64) (start best scan : Nat) : Prop :=
  start ≤ best ∧ best < scan ∧ scan ≤ values.length ∧
    ∀ k, start ≤ k → k < scan → values[best]! ≤ values[k]!

theorem minScan_start (values : List UInt64) {start : Nat}
    (hstart : start < values.length) :
    MinScan values start start (start + 1) := by
  refine ⟨Nat.le_refl _, by omega, by omega, ?_⟩
  intro k hk hks
  have : k = start := by omega
  subst k
  exact UInt64.le_refl _

theorem MinScan.step (values : List UInt64) {start best scan : Nat}
    (h : MinScan values start best scan) (hscan : scan < values.length) :
    MinScan values start
      (if values[scan]! < values[best]! then scan else best) (scan + 1) := by
  rcases h with ⟨hstartBest, hbestScan, hscanLength, hmin⟩
  by_cases hlt : values[scan]! < values[best]!
  · simp only [if_pos hlt]
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro k hk hks
    by_cases hkscan : k = scan
    · subst k; exact UInt64.le_refl _
    · exact UInt64.le_trans (UInt64.le_of_lt hlt)
        (hmin k hk (by omega))
  · simp only [if_neg hlt]
    refine ⟨hstartBest, by omega, by omega, ?_⟩
    intro k hk hks
    by_cases hkscan : k = scan
    · subst k; exact UInt64.le_of_not_lt hlt
    · exact hmin k hk (by omega)

/-- Prefix `[0, fixed)` is sorted, contains the globally least `fixed`
elements, and the whole current array is a permutation of the input. -/
def OuterInvariant
    (input current : List UInt64) (fixed : Nat) : Prop :=
  current.length = input.length ∧
  List.Perm input current ∧
  fixed ≤ current.length ∧
  Sorted (current.take fixed) ∧
  ∀ x ∈ current.take fixed, ∀ y ∈ current.drop fixed, x ≤ y

theorem outerInvariant_start (input : List UInt64) :
    OuterInvariant input input 0 := by
  refine ⟨rfl, List.Perm.refl _, Nat.zero_le _, ?_, ?_⟩
  · exact List.Pairwise.nil
  · intro x hx
    simp at hx

theorem OuterInvariant.step
    {input current : List UInt64} {fixed best : Nat}
    (hout : OuterInvariant input current fixed)
    (hfixed : fixed < current.length)
    (hbest : fixed ≤ best ∧ best < current.length)
    (hmin : ∀ k, fixed ≤ k → k < current.length →
      current[best]! ≤ current[k]!) :
    OuterInvariant input (List.swapElems current fixed best) (fixed + 1) := by
  rcases hout with ⟨hlength, hperm, hfixedLe, hsorted, hcross⟩
  let updated := List.swapElems current fixed best
  have hupdatedLength : updated.length = current.length :=
    List.swapElems_length current fixed best
  have htake : updated.take (fixed + 1) =
      current.take fixed ++ [current[best]!] := by
    rw [List.take_succ_eq_append_getElem (hupdatedLength ▸ hfixed)]
    rw [List.swapElems_take_of_le current (Nat.le_refl fixed) hbest.1]
    rw [show updated[fixed] = updated[fixed]! from
      (getElem!_pos updated fixed (hupdatedLength ▸ hfixed)).symm]
    exact congrArg (current.take fixed ++ [·])
      (List.swapElems_get_i current hfixed hbest.2)
  have suffixMem (k : Nat) (hkLower : fixed ≤ k)
      (hkUpper : k < current.length) : current[k]! ∈ current.drop fixed := by
    rw [List.mem_iff_getElem]
    refine ⟨k - fixed, ?_, ?_⟩
    · simp only [List.length_drop]; omega
    · rw [List.getElem_drop]
      rw [getElem!_pos current k hkUpper]
      congr 1
      omega
  have updatedSuffix (y : UInt64) (hy : y ∈ updated.drop (fixed + 1)) :
      ∃ k, fixed < k ∧ k < current.length ∧ updated[k]! = y := by
    rw [List.mem_iff_getElem] at hy
    rcases hy with ⟨offset, hoffset, hy⟩
    have hkUpdated : fixed + 1 + offset < updated.length := by
      simp only [List.length_drop] at hoffset
      rw [hupdatedLength] at hoffset ⊢; omega
    refine ⟨fixed + 1 + offset, by omega, ?_, ?_⟩
    · rw [hupdatedLength] at hkUpdated; exact hkUpdated
    · rw [getElem!_pos updated (fixed + 1 + offset) hkUpdated]
      rw [← hy, List.getElem_drop]
  refine ⟨hupdatedLength.trans hlength,
    hperm.trans (List.swapElems_perm current hfixed hbest.2).symm, ?_, ?_, ?_⟩
  · rw [hupdatedLength]; omega
  · rw [htake]
    unfold Sorted at hsorted ⊢
    rw [List.pairwise_append]
    refine ⟨hsorted, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact hcross x hx current[best]! (suffixMem best hbest.1 hbest.2)
  · intro x hx y hy
    rw [htake] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases updatedSuffix y hy with ⟨k, hfk, hkLength, hky⟩
    have hsource :
        (updated[k]! = current[fixed]!) ∨
        (updated[k]! = current[k]!) := by
      by_cases hkb : k = best
      · left
        subst k
        exact List.swapElems_get_j current hfixed hbest.2
      · right
        exact List.swapElems_get_other current (by omega) hkb
    rcases hx with hx | rfl
    · rcases hsource with hsource | hsource
      · rw [← hky, hsource]; exact hcross x hx current[fixed]!
          (suffixMem fixed (Nat.le_refl fixed) hfixed)
      · rw [← hky, hsource]; exact hcross x hx current[k]!
          (suffixMem k (by omega) hkLength)
    · rcases hsource with hsource | hsource
      · rw [← hky, hsource]; exact hmin fixed (Nat.le_refl fixed) hfixed
      · rw [← hky, hsource]; exact hmin k (by omega) hkLength

theorem OuterInvariant.sorted
    {input current : List UInt64} {fixed : Nat}
    (h : OuterInvariant input current fixed)
    (hfinished : current.length ≤ fixed + 1) :
    Sorted current := by
  rcases h with ⟨_hlength, _hperm, hfixed, hsorted, hcross⟩
  unfold Sorted at hsorted ⊢
  rw [← List.take_append_drop fixed current]
  rw [List.pairwise_append]
  refine ⟨hsorted, ?_, hcross⟩
  have hsuffixLength : (current.drop fixed).length ≤ 1 := by
    simp only [List.length_drop]; omega
  match hsuffix : current.drop fixed with
  | [] => exact List.Pairwise.nil
  | [_] => exact List.pairwise_singleton _ _
  | _ :: _ :: _ => simp [hsuffix] at hsuffixLength

theorem OuterInvariant.perm
    {input current : List UInt64} {fixed : Nat}
    (h : OuterInvariant input current fixed) :
    List.Perm input current := h.2.1

/-- The pure composition step used by the recursive implementation: place a
minimum at the head, recursively sort the tail, then reattach the head. -/
theorem recursive_compose
    {input : List UInt64} {best : Nat} {tailOutput : List UInt64}
    (hlength : 0 < input.length)
    (hbest : best < input.length)
    (hmin : ∀ k, k < input.length → input[best]! ≤ input[k]!)
    (htailPerm : List.Perm (List.drop 1 (List.swapElems input 0 best)) tailOutput)
    (htailSorted : Sorted tailOutput) :
    let output := (List.swapElems input 0 best)[0]! :: tailOutput
    List.Perm input output ∧ Sorted output := by
  let updated := List.swapElems input 0 best
  have houter : OuterInvariant input updated 1 :=
    (outerInvariant_start input).step hlength ⟨Nat.zero_le _, hbest⟩
      (fun k _hk hklen => hmin k hklen)
  have hupdatedLength : updated.length = input.length :=
    List.swapElems_length input 0 best
  have hupdatedNonempty : 0 < updated.length := by omega
  have hdecomp : updated = updated[0]! :: updated.drop 1 := by
    cases hUpdated : updated with
    | nil =>
        have hlength := congrArg List.length hUpdated
        simp only [List.length_nil] at hlength; omega
    | cons head tail => simp
  dsimp only
  constructor
  · exact houter.perm.trans (hdecomp ▸ htailPerm.cons updated[0]!)
  · unfold Sorted at htailSorted ⊢
    rw [List.pairwise_cons]
    refine ⟨?_, htailSorted⟩
    intro y hy
    have hyUpdated : y ∈ updated.drop 1 := htailPerm.mem_iff.mpr hy
    apply houter.2.2.2.2 updated[0]!
    · have htake : updated.take 1 = [updated[0]!] := by
        cases hUpdated : updated with
        | nil =>
            have hlength := congrArg List.length hUpdated
            simp only [List.length_nil] at hlength; omega
        | cons head tail => simp
      rw [htake]
      simp
    · exact hyUpdated

end Wasm.Examples.SelectionSort
