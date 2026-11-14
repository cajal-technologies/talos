import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic refinement for `total_variation`

These lemmas concern the UInt64 expression in the existing body-level
specification. They make no execution or termination claim. Natural subtraction
is truncated, so `absDiffNat` is the sum of the two one-sided differences.
-/

namespace Project.TotalVariation.Arithmetic

/-- The exact unsigned expression used in the existing operational contract. -/
def absDiffValue (a b : UInt64) : UInt64 :=
  if a < b then b - a else a - b

/-- Absolute difference of the natural-number interpretations. -/
def absDiffNat (a b : UInt64) : Nat :=
  (a.toNat - b.toNat) + (b.toNat - a.toNat)

/-- The machine expression; addition intentionally wraps. -/
def machineValue (a b c : UInt64) : UInt64 :=
  absDiffValue a b + absDiffValue b c

/-- The unbounded mathematical total variation of three integer values. -/
def mathematicalValue (a b c : UInt64) : Nat :=
  absDiffNat a b + absDiffNat b c

/-- Neither selected subtraction underflows. -/
theorem absDiffValue_toNat (a b : UInt64) :
    (absDiffValue a b).toNat = absDiffNat a b := by
  unfold absDiffValue
  by_cases h : a < b
  · rw [ite_eq_left h]
    have hn : a.toNat < b.toNat := UInt64.lt_iff_toNat_lt.mp h
    have hle : a ≤ b := UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hn)
    rw [UInt64.toNat_sub_of_le b a hle]
    unfold absDiffNat
    omega
  · rw [ite_eq_right h]
    have hle : b ≤ a := UInt64.not_lt.mp h
    have hn : b.toNat ≤ a.toNat := UInt64.le_iff_toNat_le.mp hle
    rw [UInt64.toNat_sub_of_le a b hle]
    unfold absDiffNat
    omega

/-- Exact machine semantics, including inputs whose sum overflows. -/
theorem machineValue_toNat (a b c : UInt64) :
    (machineValue a b c).toNat = mathematicalValue a b c % (2 ^ 64) := by
  simp only [machineValue, UInt64.toNat_add, absDiffValue_toNat, mathematicalValue]

/-- Under the explicit representability bound there is no loss to wrapping. -/
theorem machineValue_toNat_of_noOverflow (a b c : UInt64)
    (h : mathematicalValue a b c < 2 ^ 64) :
    (machineValue a b c).toNat = mathematicalValue a b c := by
  rw [machineValue_toNat, Nat.mod_eq_of_lt h]

/-- The no-overflow condition is necessary as well as sufficient. -/
theorem machineValue_exact_iff (a b c : UInt64) :
    (machineValue a b c).toNat = mathematicalValue a b c ↔
      mathematicalValue a b c < 2 ^ 64 := by
  constructor
  · intro h
    have hbound := UInt64.toNat_lt_size (machineValue a b c)
    change (machineValue a b c).toNat < 2 ^ 64 at hbound
    rw [h] at hbound
    exact hbound
  · exact machineValue_toNat_of_noOverflow a b c

/-- There can be at most one carry out of the sum of two differences. -/
theorem mathematicalValue_lt_two_moduli (a b c : UInt64) :
    mathematicalValue a b c < 2 * (2 ^ 64) := by
  have hab := UInt64.toNat_lt_size (absDiffValue a b)
  have hbc := UInt64.toNat_lt_size (absDiffValue b c)
  rw [absDiffValue_toNat] at hab hbc
  change absDiffNat a b < 2 ^ 64 at hab
  change absDiffNat b c < 2 ^ 64 at hbc
  unfold mathematicalValue
  omega

/-- An equivalent single-wrap presentation of the modulo contract. -/
theorem machineValue_toNat_cases (a b c : UInt64) :
    (machineValue a b c).toNat =
      if mathematicalValue a b c < 2 ^ 64 then mathematicalValue a b c
      else mathematicalValue a b c - 2 ^ 64 := by
  rw [machineValue_toNat]
  split
  · rename_i h
    exact Nat.mod_eq_of_lt h
  · rename_i h
    have hbound := mathematicalValue_lt_two_moduli a b c
    omega

end Project.TotalVariation.Arithmetic
