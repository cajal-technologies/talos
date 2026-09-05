import Std.Tactic.BVDecide

/-!
# `UInt32` arithmetic helpers used by corpus specs

Small bridge lemmas connecting `UInt32` bitwise operations to the
`Nat` view that user-facing specifications prefer.

`and_one_eq_zero_iff_toNat_mod_two` is consumed by the verifier's scaffolded
starter proof (`verifier/template/project/lean/Project/IsEven/Spec.lean`), so
the module is live even though nothing in `programs/lean` references it yet. It
overlaps the width-generic parity bridge in `UInt64.lean`; both are candidates
to fold into one shared low-bit lemma once that consolidation is done (keep this
public name as a corollary — the template simp-references it).
-/

namespace UInt32

theorem ofNat_succ (n : Nat) :
    UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) := by
  simpa only [UInt32.ofNat_one] using (UInt32.ofNat_add n 1).symm

end UInt32

/-- Reassembling the four little-endian bytes of a 32-bit natural recovers it. -/
theorem Nat.reassemble32_of_lt (n : Nat) (h : n < 2 ^ 32) :
    n % 2 ^ 8 ||| (((n >>> 8) % 2 ^ 8) <<< 8) % 2 ^ 32 |||
      (((n >>> 16) % 2 ^ 8) <<< 16) % 2 ^ 32 |||
      (((n >>> 24) % 2 ^ 8) <<< 24) % 2 ^ 32 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hi8 : i < 8
  · simp [hi8, show i < 32 by omega, show ¬i ≥ 8 by omega,
      show ¬i ≥ 16 by omega, show ¬i ≥ 24 by omega]
  by_cases hi16 : i < 16
  · have heq : 8 + (i - 8) = i := by omega
    simp [hi8, heq, show i ≥ 8 by omega, show i < 32 by omega,
      show i - 8 < 8 by omega, show ¬i ≥ 16 by omega, show ¬i ≥ 24 by omega]
  by_cases hi24 : i < 24
  · have heq : 16 + (i - 16) = i := by omega
    simp [hi8, heq, show i ≥ 16 by omega, show i < 32 by omega,
      show ¬i - 8 < 8 by omega, show i - 16 < 8 by omega, show ¬i ≥ 24 by omega]
  by_cases hi32 : i < 32
  · have heq : 24 + (i - 24) = i := by omega
    simp [hi8, hi32, heq, show i ≥ 24 by omega, show ¬i - 8 < 8 by omega,
      show ¬i - 16 < 8 by omega, show i - 24 < 8 by omega]
  · have hibound : n.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi8, hibound, show ¬i < 32 by omega, show ¬i - 8 < 8 by omega,
      show ¬i - 16 < 8 by omega, show ¬i - 24 < 8 by omega]

namespace Wasm

/-- The reverse `UInt32` inequality follows when strict comparison fails. -/
theorem UInt32.le_of_not_lt {a b : UInt32} (h : ¬a < b) : b ≤ a := by
  change ¬a.toNat < b.toNat at h
  exact Nat.le_of_not_lt h

/-- The reverse `UInt32` inequality follows when non-strict comparison fails. -/
theorem UInt32.le_of_not_le {a b : UInt32} (h : ¬a ≤ b) : b ≤ a := by
  change ¬a.toNat ≤ b.toNat at h
  exact Nat.le_of_lt (Nat.lt_of_not_le h)

/-- `n &&& 1 = 0` (bitwise low-bit zero) is equivalent to
`n.toNat % 2 = 0` (semantic evenness). The forward proof factors
through `BitVec.toNat_and` and the standard `Nat.and_one_is_mod`. -/
theorem UInt32.and_one_eq_zero_iff_toNat_mod_two (n : UInt32) :
    n &&& 1 = 0 ↔ n.toNat % 2 = 0 := by
  have hN : (n &&& 1).toNat = n.toNat % 2 := by
    show (n.toBitVec &&& (1 : UInt32).toBitVec).toNat = _
    rw [BitVec.toNat_and]
    show n.toNat &&& 1 = _
    exact Nat.and_one_is_mod n.toNat
  constructor
  · intro h
    have : (n &&& 1).toNat = (0 : UInt32).toNat := by rw [h]
    rw [hN] at this
    simpa using this
  · intro h
    have h1 : (n &&& 1).toNat = 0 := by rw [hN]; exact h
    have h2 : (n &&& 1).toNat = (0 : UInt32).toNat := by simpa using h1
    exact UInt32.toNat.inj h2

end Wasm
