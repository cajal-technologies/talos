import CodeLib.WordCodec
import Mathlib.Data.Nat.Bitwise

/-!
# `CodeLib.WordCodec.UInt32`

The four-byte little-endian `u32` codec, as a `WordCodec UInt32`.

`decode_encode` is proved through `Nat.testBit` and `omega` rather than by
bit-blasting, so no theorem stated over this codec depends on a reflection
axiom.  `CodeLib.Examples.MergeSort.StdIO.codec` is the same codec proved by
`bv_decide`; it lives under `Examples`, which `RustStd` does not import.

`Project.Mergesort.Spec` carries an identical private copy (`encodeWord`,
`decodeWord`, `u32Codec`).  A follow-up that may touch `programs/` can replace
that copy with this definition.

Consumer: `CodeLib.RustStd.Vec.Codec`, which puts `u32le` in front of a packed
`Vec` as its element count.
-/

namespace Wasm.WordCodec

/-- The four little-endian bytes of a 32-bit word. -/
def encodeU32 (value : UInt32) : List UInt8 :=
  [ value.toUInt8
  , (value >>> 8).toUInt8
  , (value >>> 16).toUInt8
  , (value >>> 24).toUInt8 ]

/-- Read one four-byte little-endian word.  Total, as `WordCodec.decode`
requires; `deserialize` only ever applies it to chunks of width four. -/
def decodeU32 : List UInt8 → UInt32
  | b₀ :: b₁ :: b₂ :: b₃ :: _ =>
      b₀.toUInt32 ||| (b₁.toUInt32 <<< 8) |||
        (b₂.toUInt32 <<< 16) ||| (b₃.toUInt32 <<< 24)
  | _ => 0

/-- Kernel-checked reconstruction of a 32-bit natural from its four bytes. -/
private theorem reassembleLE32 (n : Nat) (h : n < 2 ^ 32) :
    n % 2 ^ 8 ||| (((n >>> 8) % 2 ^ 8) <<< 8) % 2 ^ 32 |||
      (((n >>> 16) % 2 ^ 8) <<< 16) % 2 ^ 32 |||
      (((n >>> 24) % 2 ^ 8) <<< 24) % 2 ^ 32 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hi8 : i < 8
  · simp [hi8, show i < 32 by omega, show ¬i ≥ 8 by omega,
      show ¬i ≥ 16 by omega, show ¬i ≥ 24 by omega]
  by_cases hi16 : i < 16
  · have h8le : i ≥ 8 := by omega
    have heq : 8 + (i - 8) = i := by omega
    simp [hi8, h8le, heq, show i < 32 by omega,
      show i - 8 < 8 by omega, show ¬i ≥ 16 by omega,
      show ¬i ≥ 24 by omega]
  by_cases hi24 : i < 24
  · have h16le : i ≥ 16 := by omega
    have heq : 16 + (i - 16) = i := by omega
    simp [hi8, h16le, heq, show i < 32 by omega,
      show ¬i - 8 < 8 by omega, show i - 16 < 8 by omega,
      show ¬i ≥ 24 by omega]
  by_cases hi32 : i < 32
  · have h24le : i ≥ 24 := by omega
    have heq : 24 + (i - 24) = i := by omega
    simp [hi8, hi32, h24le, heq, show ¬i - 8 < 8 by omega,
      show ¬i - 16 < 8 by omega, show i - 24 < 8 by omega]
  · have hibound : n.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le h
        (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hi8, hibound, show ¬i < 32 by omega,
      show ¬i - 8 < 8 by omega, show ¬i - 16 < 8 by omega,
      show ¬i - 24 < 8 by omega]

/-- Four-byte little-endian `u32` words. -/
def u32le : WordCodec UInt32 where
  width := 4
  encode := encodeU32
  decode := decodeU32
  width_pos := by decide
  encode_length := fun _ => rfl
  decode_encode := by
    intro value
    simp only [encodeU32, decodeU32]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft,
      UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
      UInt32.toNat_shiftRight]
    exact reassembleLE32 value.toNat (UInt32.toNat_lt value)

@[simp] theorem u32le_encode_length (value : UInt32) :
    (u32le.encode value).length = 4 := rfl

end Wasm.WordCodec
