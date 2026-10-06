import HexEncodeStdio.ReadToEndResourceCost

/-! # Conservative public resource formulas for the hex consumer

These are arithmetic bounds used by the operational export certificate.
The threshold at 10008 bytes is exact for the conservative page formula;
it is not asserted to be the exact physical growth threshold of the program.
The work measure counts semantic transitions and explicitly charged bytes,
not machine cycles or elapsed time.
-/

namespace Project.HexEncodeStdio.ResourceBounds

open ReadToEndResourceCost

/-- Initial pages or enough pages for the conservative complete heap frontier. -/
def pageBound (input : List UInt8) : Nat :=
  max 17 (AllocatorResourceCost.requiredPages (completeFrontierBound input.length))

/-- Whole-export budget: scalar/byte-input work plus every newly added byte. -/
def workBound (input : List UInt8) : Nat :=
  675 * input.length + 1234 + 65536 * (pageBound input - 17)

theorem completeFrontierBound_eq (n : Nat) :
    completeFrontierBound n = 1054064 + 4 * n + max 8 (2 * n) := by
  unfold completeFrontierBound inputFrontierBound capacityBound
  omega

theorem completeFrontierBound_eq_of_four_le (n : Nat) (h : 4 ≤ n) :
    completeFrontierBound n = 1054064 + 6 * n := by
  rw [completeFrontierBound_eq]
  omega

/-- Exact numerical meaning of the conservative initial-size hypothesis. -/
theorem inputFits_iff (n : Nat) : InputFits n ↔ n ≤ 357738263 := by
  unfold InputFits
  rw [completeFrontierBound_eq]
  change 1054064 + 4*n + max 8 (2*n) < 2147483648 ↔ _
  omega

theorem requiredPages_le_iff (finish pages : Nat) :
    AllocatorResourceCost.requiredPages finish ≤ pages ↔ finish ≤ 65536 * pages := by
  unfold AllocatorResourceCost.requiredPages
  omega

theorem completeFrontierBound_mono {m n : Nat} (h : m ≤ n) :
    completeFrontierBound m ≤ completeFrontierBound n := by
  rw [completeFrontierBound_eq, completeFrontierBound_eq]
  omega

theorem pageBound_mono {input other : List UInt8} (h : input.length ≤ other.length) :
    pageBound input ≤ pageBound other := by
  have hf := completeFrontierBound_mono h
  unfold pageBound AllocatorResourceCost.requiredPages
  omega

theorem initial_pages_le (input : List UInt8) : 17 ≤ pageBound input :=
  Nat.le_max_left _ _

theorem complete_frontier_le (input : List UInt8) :
    completeFrontierBound input.length ≤ 65536 * pageBound input := by
  apply (requiredPages_le_iff _ _).mp
  exact Nat.le_max_right _ _

/-- This characterizes the formula, rather than exact physical memory usage. -/
theorem pageBound_eq_seventeen_iff (input : List UInt8) :
    pageBound input = 17 ↔ input.length ≤ 10008 := by
  unfold pageBound AllocatorResourceCost.requiredPages
  rw [completeFrontierBound_eq]
  omega

theorem pageBound_eq_seventeen (input : List UInt8) (h : input.length ≤ 10008) :
    pageBound input = 17 := (pageBound_eq_seventeen_iff input).mpr h

theorem pageBound_le_of_fits (input : List UInt8) (h : InputFits input.length) :
    pageBound input ≤ 32768 := by
  have required := (AllocatorResourceCost.required_bound _ h).1
  unfold pageBound
  omega

theorem workBound_mono {input other : List UInt8} (h : input.length ≤ other.length) :
    workBound input ≤ workBound other := by
  have hp := pageBound_mono h
  unfold workBound
  omega

theorem workBound_eq_of_small (input : List UInt8) (h : input.length ≤ 10008) :
    workBound input = 675 * input.length + 1234 := by
  simp only [workBound, pageBound_eq_seventeen input h, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

theorem workBound_le_of_fits (input : List UInt8) (h : InputFits input.length) :
    workBound input ≤ 243619698295 := by
  have hn := (inputFits_iff input.length).mp h
  have hp := pageBound_le_of_fits input h
  unfold workBound
  omega

/-- Kernel-reduced checks of the conservative formulas. No operational claim
is inferred from evaluating these closed expressions. -/
theorem empty_bounds : pageBound [] = 17 ∧ workBound [] = 1234 := by decide

theorem page_boundary_before :
    pageBound (List.replicate 10008 (0 : UInt8)) = 17 := by
  simp only [pageBound, List.length_replicate]
  decide

theorem page_boundary_after :
    pageBound (List.replicate 10009 (0 : UInt8)) = 18 := by
  simp only [pageBound, List.length_replicate]
  decide

theorem input_boundary_before : InputFits 357738263 := by
  unfold InputFits
  decide

theorem input_boundary_after : ¬ InputFits 357738264 := by
  unfold InputFits
  decide

/-- The next integer reaches the excluded signed boundary exactly. -/
theorem input_limit_frontiers :
    completeFrontierBound 357738263 = 2147483642 ∧
      completeFrontierBound 357738264 = 2147483648 := by decide

end Project.HexEncodeStdio.ResourceBounds
