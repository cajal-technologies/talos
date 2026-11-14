import Init.Data.UInt.Lemmas
import Mathlib.Data.Nat.Dist

/-!
# Arithmetic refinement for `total_variation`

The two unsigned differences are exact. Their sum wraps modulo `2^64`.
-/

namespace Project.TotalVariation.Arithmetic

/-- The exact unsigned expression used in the existing operational contract. -/
def absDiffValue (a b : UInt64) : UInt64 :=
  if a < b then b - a else a - b

/-- The machine expression; addition intentionally wraps. -/
def machineValue (a b c : UInt64) : UInt64 :=
  absDiffValue a b + absDiffValue b c

/-- Neither selected subtraction underflows. -/
theorem absDiffValue_toNat (a b : UInt64) :
    (absDiffValue a b).toNat = Nat.dist a.toNat b.toNat := by
  unfold absDiffValue
  by_cases h : a < b
  · rw [ite_eq_left h]
    have hn : a.toNat < b.toNat := UInt64.lt_iff_toNat_lt.mp h
    have hle : a ≤ b := UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hn)
    rw [UInt64.toNat_sub_of_le b a hle]
    exact (Nat.dist_eq_sub_of_le (Nat.le_of_lt hn)).symm
  · rw [ite_eq_right h]
    have hle : b ≤ a := UInt64.not_lt.mp h
    have hn : b.toNat ≤ a.toNat := UInt64.le_iff_toNat_le.mp hle
    rw [UInt64.toNat_sub_of_le a b hle]
    exact (Nat.dist_eq_sub_of_le_right hn).symm

/-- Exact machine semantics, including inputs whose sum overflows. -/
theorem machineValue_toNat (a b c : UInt64) :
    (machineValue a b c).toNat =
      (Nat.dist a.toNat b.toNat + Nat.dist b.toNat c.toNat) % (2 ^ 64) := by
  simp only [machineValue, UInt64.toNat_add, absDiffValue_toNat]

end Project.TotalVariation.Arithmetic
