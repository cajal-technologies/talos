import Project.RustHashMap.CollectBodyContracts
import CodeLib.RustStd.HashMap.CapacityClz

/-!
# The capacity arithmetic of `reserve_rehash_inner`

Absolute `func 17` computes the bucket count of the fresh table in two
forms.  For fewer than fifteen items WAT 3653 to 3663 gives
`if cap < 4 then 4 else (cap &&& 8) + 8`.  For fifteen or more WAT 3079 to
3100 gives `(0xFFFFFFFF >>> clz (cap * 8 / 7 - 1)) + 1`.  The model has one
form, `Table.capacityToBuckets`.

This module proves the two compiled forms equal to the model, bounds the
result by `2 ^ 27`, and reads the four `u32` operations of the body off
their `Nat` counterparts.  Nothing here mentions the separation logic.
-/

namespace Project.RustHashMap.Func14Capacity

open Wasm
open Wasm.RustStd.HashMap
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.CollectBodyContracts

/-! ## The two compiled forms -/

/-- Fewer than four items take four buckets. -/
theorem buckets_tiny {a : Nat} (h1 : 1 ≤ a) (h4 : a < 4) :
    Table.capacityToBuckets a = 4 := by
  unfold Table.capacityToBuckets
  rw [if_pos (by omega)]
  show (if max 3 a < 4 then 4 else if max 3 a < 8 then 8 else 16) = 4
  rw [if_pos (by omega)]

/-- Four to fourteen items take the masked form of WAT 3653 to 3663. -/
theorem buckets_small {a : Nat} (h4 : 4 ≤ a) (h15 : a < 15) :
    (a &&& 8) + 8 = Table.capacityToBuckets a := by
  interval_cases a <;> decide

/-- Fifteen or more items take the `clz` form of WAT 3079 to 3100. -/
theorem buckets_big {a : Nat} (h15 : 15 ≤ a) (hmax : a ≤ maxTableCapacity) :
    ((0xFFFFFFFF : UInt32) >>>
        UInt32.ofNat (clz32 32 (UInt32.ofNat (a * 8 / 7 - 1)))).toNat + 1
      = Table.capacityToBuckets a := by
  have hmaxEq : maxTableCapacity = 117440512 := rfl
  rw [hmaxEq] at hmax
  have hc2 : 2 ≤ a * 8 / 7 := by omega
  have hcub : a * 8 / 7 ≤ 2 ^ 32 :=
    le_trans (Nat.div_le_self (a * 8) 7) (by omega)
  rw [Table.nextPow2_eq_wasm_clz hc2 hcub]
  unfold Table.capacityToBuckets
  rw [if_neg (by omega)]

/-! ## Bounds on the bucket count -/

/-- The fresh table always has at least four buckets. -/
theorem buckets_ge_four {a : Nat} (h1 : 1 ≤ a) (hmax : a ≤ maxTableCapacity) :
    4 ≤ Table.capacityToBuckets a := by
  have hmaxEq : maxTableCapacity = 117440512 := rfl
  rw [hmaxEq] at hmax
  unfold Table.capacityToBuckets
  by_cases h15 : a < 15
  · rw [if_pos h15]
    show 4 ≤ if max 3 a < 4 then 4 else if max 3 a < 8 then 8 else 16
    split_ifs <;> omega
  · rw [if_neg h15]
    obtain ⟨m, -, hp, hnm, -⟩ :=
      Table.nextPow2_spec (n := a * 8 / 7) (by omega)
    rw [hp]
    have : 17 ≤ a * 8 / 7 := by omega
    omega

/-- The capacity bound of `Func14Spec` keeps the bucket count at `2 ^ 27` or
below, which is what the allocation guard at WAT 3679 needs. -/
theorem buckets_le {a : Nat} (hmax : a ≤ maxTableCapacity) :
    Table.capacityToBuckets a ≤ 2 ^ 27 := by
  have hmaxEq : maxTableCapacity = 117440512 := rfl
  rw [hmaxEq] at hmax
  unfold Table.capacityToBuckets
  by_cases h15 : a < 15
  · rw [if_pos h15]
    show (if max 3 a < 4 then 4 else if max 3 a < 8 then 8 else 16) ≤ 2 ^ 27
    split_ifs <;> omega
  · rw [if_neg h15]
    obtain ⟨m, -, hp, hnm, hor⟩ :=
      Table.nextPow2_spec (n := a * 8 / 7) (by omega)
    rw [hp]
    rcases hor with rfl | hlt
    · omega
    · by_contra hgt
      have hm : 28 ≤ m := by
        by_contra hlt27
        exact hgt (Nat.pow_le_pow_right (by omega) (by omega))
      have : (2 : Nat) ^ 27 ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega

/-- The bucket count is a power of two, which `TableRefinement` calls a
`Shape`. -/
theorem buckets_shape {a : Nat} (hmax : a ≤ maxTableCapacity) :
    Table.Shape (Table.capacityToBuckets a) := by
  have hmaxEq : maxTableCapacity = 117440512 := rfl
  rw [hmaxEq] at hmax
  exact (Table.capacityToBuckets_spec (cap := a) (by omega)).1

/-- The growth counter that WAT 3729 to 3742 computes is the model
`bucket_mask_to_capacity` of the new mask. -/
theorem growthLeft_eq {b : Nat} (hb : 1 ≤ b) :
    (if b < 9 then b - 1 else b / 8 * 7) =
      Table.bucketMaskToCapacity (b - 1) := by
  unfold Table.bucketMaskToCapacity
  by_cases h9 : b < 9
  · rw [if_pos h9, if_pos (by omega)]
  · rw [if_neg h9, if_neg (by omega), show b - 1 + 1 = b from by omega]

/-! ## The `u32` operations of the body -/

theorem toNat_shr3 (x : UInt32) : (x >>> 3).toNat = x.toNat / 8 := by
  rw [UInt32.toNat_shiftRight, show UInt32.toNat 3 % 32 = 3 from by decide,
    Nat.shiftRight_eq_div_pow]

theorem toNat_shl3 {x : UInt32} (h : x.toNat < 2 ^ 29) :
    (x <<< 3).toNat = x.toNat * 8 := by
  rw [UInt32.toNat_shiftLeft, show UInt32.toNat 3 % 32 = 3 from by decide,
    Nat.shiftLeft_eq]
  norm_num
  omega

theorem toNat_pred {x : UInt32} (h : 1 ≤ x.toNat) :
    (x + 4294967295).toNat = x.toNat - 1 := by
  have hx : x.toNat < 4294967296 := x.toBitVec.isLt
  rw [UInt32.toNat_add]
  show (x.toNat + 4294967295) % 4294967296 = x.toNat - 1
  omega

theorem toNat_add_lit {x : UInt32} {k : Nat}
    (h : x.toNat + k < 4294967296) :
    (x + UInt32.ofNat k).toNat = x.toNat + k := by
  have hk : (UInt32.ofNat k).toNat = k := by simp; omega
  rw [UInt32.toNat_add, hk]
  show (x.toNat + k) % 4294967296 = x.toNat + k
  omega

end Project.RustHashMap.Func14Capacity
