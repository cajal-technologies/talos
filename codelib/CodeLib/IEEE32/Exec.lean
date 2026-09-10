import Interpreter.Wasm.Float
import Lean.Elab.Tactic.Omega

/-! Kernel-checked IEEE-754 comparison and saturating-conversion facts.
The operations are the reference interpreter's pure integer definitions. -/

open Wasm

namespace IEEE32Exec
theorem f32Ne_self_iff_isNaN (x : UInt32) : f32Ne x x = f32IsNaN x := by
  simp only [f32Ne, f32Eq, IEEE754.eq, f32IsNaN]
  cases IEEE754.isNaN IEEE754.binary32 x.toNat <;> simp
theorem i32TruncSatF32S_nan {x : UInt32} (h : f32IsNaN x = true) :
    i32TruncSatF32S x = 0 := by
  unfold f32IsNaN IEEE754.isNaN at h
  unfold i32TruncSatF32S IEEE754.saturate
  cases hd : IEEE754.decode IEEE754.binary32 x.toNat <;> simp [hd] at h ⊢ <;> rfl
theorem f32Ge_positive_bound {x : UInt32}
    (hnan : f32IsNaN x = false) (hge : f32Ge x 1325400064 = true) :
    1325400064 ≤ x.toNat ∧ x.toNat < 2147483648 := by
  have hn : IEEE754.isNaN IEEE754.binary32 x.toNat = false := hnan
  have hc : IEEE754.isNaN IEEE754.binary32 1325400064 = false := by decide +kernel
  change IEEE754.le IEEE754.binary32 1325400064 x.toNat = true at hge
  simp only [IEEE754.le, IEEE754.lt, IEEE754.eq, hn, hc, IEEE754.isZero,
    show IEEE754.binary32.signBit = 2147483648 from rfl] at hge
  by_cases hs : x.toNat ≥ 2147483648 <;> simp [hs] at hge <;> omega
end IEEE32Exec

namespace Wasm.IEEE754
theorem saturate32_positive {n : Nat}
    (hlo : 1325400064 ≤ n) (hhi : n < 2147483648)
    (hnan : isNaN binary32 n = false) :
    saturate binary32 n (-2147483648) 2147483647 = 2147483647 := by
  have hs : n / 2147483648 % 2 = 0 := by omega
  have he : 158 ≤ n / 8388608 % 256 := by omega
  have hd : decode binary32 n =
      if n / 8388608 % 256 == 255 then
        if n % 8388608 == 0 then .infinity false else .nan
      else .finite false (8388608 + n % 8388608) ((n / 8388608 % 256 : Nat) - 150) := by
    simp only [decode, binary32, Format.signBit, Format.hiddenBit,
      Format.maxExponentField, Format.minExponent]
    simp [hs, show n / 8388608 % 256 ≠ 0 by omega]
    congr 2 <;> omega
  by_cases hmax : n / 8388608 % 256 = 255
  · by_cases hz : n % 8388608 = 0
    · simp [saturate, hd, hmax, hz]
    · simp [isNaN, hd, hmax, hz] at hnan
  · have hex : (0 : Int) ≤ (n / 8388608 % 256 : Nat) - 150 := by omega
    have hex8 : 8 ≤ ((n / 8388608 % 256 : Nat) - 150 : Int).toNat := by omega
    have hp : 256 ≤ 2 ^ ((n / 8388608 % 256 : Nat) - 150 : Int).toNat :=
      Nat.pow_le_pow_right (show 0 < 2 by decide) hex8
    have hm : 2147483648 ≤
        (8388608 + n % 8388608) * 2 ^ ((n / 8388608 % 256 : Nat) - 150 : Int).toNat := by
      have := Nat.mul_le_mul (show 8388608 ≤ 8388608 + n % 8388608 by omega) hp
      omega
    simp only [saturate, truncInt, hd, show (n / 8388608 % 256 == 255) = false from beq_eq_false_iff_ne.mpr hmax,
      Bool.false_eq_true, hex, ↓reduceIte, Option.getD_some, signed]
    omega
end Wasm.IEEE754
namespace Wasm.IEEE754
theorem saturate32_negative {n : Nat}
    (hlo : 3472883712 ≤ n) (hhi : n < 4294967296)
    (hnan : isNaN binary32 n = false) :
    saturate binary32 n (-2147483648) 2147483647 = -2147483648 := by
  have hs : n / 2147483648 % 2 = 1 := by omega
  have he : 158 ≤ n / 8388608 % 256 := by omega
  have hd : decode binary32 n =
      if n / 8388608 % 256 == 255 then
        if n % 8388608 == 0 then .infinity true else .nan
      else .finite true (8388608 + n % 8388608) ((n / 8388608 % 256 : Nat) - 150) := by
    simp only [decode, binary32, Format.signBit, Format.hiddenBit,
      Format.maxExponentField, Format.minExponent]
    simp [hs, show n / 8388608 % 256 ≠ 0 by omega]
    congr 2 <;> omega
  by_cases hmax : n / 8388608 % 256 = 255
  · by_cases hz : n % 8388608 = 0
    · simp [saturate, hd, hmax, hz]
    · simp [isNaN, hd, hmax, hz] at hnan
  · have hex : (0 : Int) ≤ (n / 8388608 % 256 : Nat) - 150 := by omega
    have hex8 : 8 ≤ ((n / 8388608 % 256 : Nat) - 150 : Int).toNat := by omega
    have hp : 256 ≤ 2 ^ ((n / 8388608 % 256 : Nat) - 150 : Int).toNat :=
      Nat.pow_le_pow_right (show 0 < 2 by decide) hex8
    have hm : 2147483648 ≤
        (8388608 + n % 8388608) * 2 ^ ((n / 8388608 % 256 : Nat) - 150 : Int).toNat := by
      have := Nat.mul_le_mul (show 8388608 ≤ 8388608 + n % 8388608 by omega) hp
      omega
    simp only [saturate, truncInt, hd, show (n / 8388608 % 256 == 255) = false from beq_eq_false_iff_ne.mpr hmax,
      Bool.false_eq_true, hex, ↓reduceIte, Option.getD_some, signed]
    omega
end Wasm.IEEE754

namespace IEEE32Exec
theorem f32Lt_negative_bound {x : UInt32}
    (hnan : f32IsNaN x = false) (hlt : f32Lt x 3472883712 = true) :
    3472883712 < x.toNat := by
  have hn : IEEE754.isNaN IEEE754.binary32 x.toNat = false := hnan
  have hc : IEEE754.isNaN IEEE754.binary32 3472883712 = false := by decide +kernel
  change IEEE754.lt IEEE754.binary32 x.toNat 3472883712 = true at hlt
  simp only [IEEE754.lt, hn, hc, IEEE754.isZero,
    show IEEE754.binary32.signBit = 2147483648 from rfl] at hlt
  by_cases hs : x.toNat ≥ 2147483648 <;> simp [hs] at hlt <;> omega

theorem i32TruncSatF32S_large_pos {x : UInt32}
    (hnan : f32Ne x x = false) (hge : f32Ge x 1325400064 = true) :
    i32TruncSatF32S x = 0x7FFFFFFF := by
  rw [f32Ne_self_iff_isNaN] at hnan
  obtain ⟨hlo, hhi⟩ := f32Ge_positive_bound hnan hge
  unfold i32TruncSatF32S
  rw [IEEE754.saturate32_positive hlo hhi hnan]
  rfl

theorem i32TruncSatF32S_large_neg {x : UInt32}
    (hnan : f32Ne x x = false) (hlt : f32Lt x 3472883712 = true) :
    i32TruncSatF32S x = 0x80000000 := by
  rw [f32Ne_self_iff_isNaN] at hnan
  have hlo := f32Lt_negative_bound hnan hlt
  unfold i32TruncSatF32S
  rw [IEEE754.saturate32_negative (by omega) x.toNat_lt hnan]
  rfl
end IEEE32Exec
