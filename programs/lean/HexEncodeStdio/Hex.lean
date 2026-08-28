import Mathlib
import Project.HexStdio.Spec

namespace Project.HexEncodeStdio.Hex

open Project.HexStdio.Spec

def asciiTable : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
   0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

@[simp] theorem encode_nil : encode [] = [] := rfl

@[simp] theorem encode_cons (b : UInt8) (bs : List UInt8) :
    encode (b :: bs) = encodeByte b ++ encode bs := by
  rfl

@[simp] theorem encodeByte_length (b : UInt8) : (encodeByte b).length = 2 := by
  rfl

@[simp] theorem encode_length (bytes : List UInt8) :
    (encode bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b bytes ih => simp [ih]; omega

theorem encode_append (left right : List UInt8) :
    encode (left ++ right) = encode left ++ encode right := by
  simp [encode, List.flatMap_append]

theorem nibble_high_lt (b : UInt8) : b.toNat / 16 < 16 := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  omega

theorem nibble_low_lt (b : UInt8) : b.toNat % 16 < 16 := by
  omega

theorem hexDigit_eq_ascii_table (n : Nat) (hn : n < 16) :
    hexDigit n = asciiTable[n]! := by
  interval_cases n <;> rfl

@[simp] theorem asciiTable_length : asciiTable.length = 16 := by
  rfl

theorem asciiTable_getElem?_hexDigit (n : Nat) (hn : n < 16) :
    asciiTable[n]? = some (hexDigit n) := by
  interval_cases n <;> rfl

theorem low_nibble_u32 (b : UInt8) :
    b.toUInt32 &&& 15 = UInt32.ofNat (b.toNat % 16) := by
  apply UInt32.toNat_inj.mp
  change (b.toUInt32.toBitVec &&& (15 : UInt32).toBitVec).toNat =
    (UInt32.ofNat (b.toNat % 16)).toNat
  rw [BitVec.toNat_and,
    UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
  change b.toNat &&& 15 = b.toNat % 16
  simpa using Nat.and_two_pow_sub_one_eq_mod b.toNat 4

theorem high_nibble_u32 (b : UInt8) :
    b.toUInt32 >>> 4 = UInt32.ofNat (b.toNat / 16) := by
  apply UInt32.toNat_inj.mp
  change (b.toUInt32.toBitVec >>> (4 % 32)).toNat =
    (UInt32.ofNat (b.toNat / 16)).toNat
  rw [BitVec.toNat_ushiftRight,
    UInt32.toNat_ofNat_of_lt'
      (by simp [UInt32.size]; have := UInt8.toNat_lt b; omega)]
  change b.toNat >>> (4 % 32) = b.toNat / 16
  norm_num [Nat.shiftRight_eq_div_pow]

theorem encodeByte_eq_ascii_table (b : UInt8) :
    encodeByte b =
      [asciiTable[b.toNat / 16]!, asciiTable[b.toNat % 16]!] := by
  simp only [encodeByte]
  rw [hexDigit_eq_ascii_table _ (nibble_high_lt b),
      hexDigit_eq_ascii_table _ (nibble_low_lt b)]

theorem encode_take_succ (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    encode (bytes.take (i + 1)) =
      encode (bytes.take i) ++ encodeByte bytes[i] := by
  change (bytes.take (i + 1)).flatMap encodeByte =
    (bytes.take i).flatMap encodeByte ++ encodeByte bytes[i]
  calc
    _ = (bytes.take i ++ [bytes[i]]).flatMap encodeByte :=
      by simpa only using
        congrArg (List.flatMap encodeByte) (List.take_succ_eq_append_getElem hi)
    _ = _ := by
      rw [List.flatMap_append]
      rfl

theorem encode_prefix_high (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    encode (bytes.take i) ++ [hexDigit (bytes[i].toNat / 16)] =
      (encode (bytes.take i) ++ encodeByte bytes[i]).take (2 * i + 1) := by
  have hlen : (encode (bytes.take i)).length = 2 * i := by
    rw [encode_length, List.length_take_of_le hi.le]
  simp [List.take_append, hlen, encodeByte]

theorem encode_prefix_low (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    encode (bytes.take i) ++
        [hexDigit (bytes[i].toNat / 16), hexDigit (bytes[i].toNat % 16)] =
      encode (bytes.take (i + 1)) := by
  rw [encode_take_succ bytes i hi]
  rfl

theorem encode_prefix_complete (bytes : List UInt8) :
    encode (bytes.take bytes.length) = encode bytes := by
  rw [List.take_length]

/-- Encoding commutes with taking a whole number of two-digit byte blocks. -/
theorem encode_take_twice (bytes : List UInt8) (i : Nat)
    (hi : i ≤ bytes.length) :
    (encode bytes).take (2 * i) = encode (bytes.take i) := by
  conv_lhs => rw [← List.take_append_drop i bytes, encode_append]
  have hlen : (encode (bytes.take i)).length = 2 * i := by
    rw [encode_length, List.length_take_of_le hi]
  rw [List.take_append_of_le_length]
  · simp [hlen]
  · omega

theorem encode_take_high (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    (encode bytes).take (2 * i + 1) =
      encode (bytes.take i) ++ [hexDigit (bytes[i].toNat / 16)] := by
  have hi' : i + 1 ≤ bytes.length := by omega
  calc
    (encode bytes).take (2 * i + 1) =
        ((encode bytes).take (2 * (i + 1))).take (2 * i + 1) := by
      simp only [List.take_take]
      congr 2
      omega
    _ = (encode (bytes.take (i + 1))).take (2 * i + 1) := by
      rw [encode_take_twice bytes (i + 1) hi']
    _ = (encode (bytes.take i) ++ encodeByte bytes[i]).take
        (2 * i + 1) := by
      rw [encode_take_succ bytes i hi]
      rfl
    _ = encode (bytes.take i) ++ [hexDigit (bytes[i].toNat / 16)] :=
      (encode_prefix_high bytes i hi).symm

theorem encode_take_low (bytes : List UInt8) (i : Nat)
    (hi : i < bytes.length) :
    (encode bytes).take (2 * i + 2) = encode (bytes.take (i + 1)) := by
  rw [show 2 * i + 2 = 2 * (i + 1) by omega]
  exact encode_take_twice bytes (i + 1) (Nat.succ_le_iff.mpr hi)

theorem take_set_succ {α : Type} (xs : List α) (i : Nat) (x : α)
    (hi : i < xs.length) :
    (xs.set i x).take (i + 1) = xs.take i ++ [x] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simpa [List.set] using ih i hi

theorem hexDigit_toUInt32_ne_sentinel (n : Nat) :
    (hexDigit n).toUInt32 ≠ (1114112 : UInt32) := by
  intro h
  have heq := congrArg UInt32.toNat h
  have hb := UInt8.toNat_lt (hexDigit n)
  norm_num [UInt8.toNat_toUInt32, UInt32.toNat_ofNat] at heq
  omega

theorem hexDigit_toUInt32_lt_128 (n : Nat) (hn : n < 16) :
    (hexDigit n).toUInt32 < (128 : UInt32) := by
  interval_cases n <;> decide

theorem hexDigit_toUInt32_toUInt8 (n : Nat) :
    (hexDigit n).toUInt32.toUInt8 = hexDigit n := by
  apply UInt8.toNat_inj.mp
  simp

end Project.HexEncodeStdio.Hex
