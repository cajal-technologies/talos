import CodeLib.UInt32

/-! Extracting each byte of a little-endian four-byte word. -/

theorem UInt32.packBytes_byte0 (a b c d : UInt8) :
    (a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) |||
      (d.toUInt32 <<< 24)).toUInt8 = a := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt32]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp (disch := omega)

theorem UInt32.packBytes_byte1 (a b c d : UInt8) :
    ((a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) |||
      (d.toUInt32 <<< 24)) >>> 8).toUInt8 = b := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftRight, UInt8.toBitVec_toUInt32]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp (disch := omega) [show 8 + j < 16 by omega, show 8 + j < 24 by omega]

theorem UInt32.packBytes_byte2 (a b c d : UInt8) :
    ((a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) |||
      (d.toUInt32 <<< 24)) >>> 16).toUInt8 = c := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftRight, UInt8.toBitVec_toUInt32]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp (disch := omega) [show 16 + j < 24 by omega]

theorem UInt32.packBytes_byte3 (a b c d : UInt8) :
    ((a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) |||
      (d.toUInt32 <<< 24)) >>> 24).toUInt8 = d := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftRight, UInt8.toBitVec_toUInt32]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp (disch := omega)


/-! Kernel-checked byte reconstruction shared by memory semantics and ownership. -/

/-- Keep byte reconstruction kernel-checked: native decision axioms here would
propagate into the shared 64-bit memory ownership facts and lifting rules. -/
theorem Nat.reassemble64_of_lt (n : Nat) (h : n < 2 ^ 64) :
    n % 2 ^ 8 ||| (((n >>> 8) % 2 ^ 8) <<< 8) % 2 ^ 64 |||
      (((n >>> 16) % 2 ^ 8) <<< 16) % 2 ^ 64 |||
      (((n >>> 24) % 2 ^ 8) <<< 24) % 2 ^ 64 |||
      (((n >>> 32) % 2 ^ 8) <<< 32) % 2 ^ 64 |||
      (((n >>> 40) % 2 ^ 8) <<< 40) % 2 ^ 64 |||
      (((n >>> 48) % 2 ^ 8) <<< 48) % 2 ^ 64 |||
      (((n >>> 56) % 2 ^ 8) <<< 56) % 2 ^ 64 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h8 : i < 8
  · simp [h8, show i < 64 by omega, show ¬ i ≥ 8 by omega, show ¬ i ≥ 16 by omega,
      show ¬ i ≥ 24 by omega, show ¬ i ≥ 32 by omega, show ¬ i ≥ 40 by omega,
      show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h16 : i < 16
  · have heq : 8 + (i - 8) = i := by omega
    simp [h8, heq, show i ≥ 8 by omega, show i < 64 by omega, show i - 8 < 8 by omega,
      show ¬ i ≥ 16 by omega, show ¬ i ≥ 24 by omega, show ¬ i ≥ 32 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h24 : i < 24
  · have heq : 16 + (i - 16) = i := by omega
    simp [h8, heq, show i ≥ 16 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show i - 16 < 8 by omega, show ¬ i ≥ 24 by omega, show ¬ i ≥ 32 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h32 : i < 32
  · have heq : 24 + (i - 24) = i := by omega
    simp [h8, heq, show i ≥ 24 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show i - 24 < 8 by omega, show ¬ i ≥ 32 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h40 : i < 40
  · have heq : 32 + (i - 32) = i := by omega
    simp [h8, heq, show i ≥ 32 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show i - 32 < 8 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h48 : i < 48
  · have heq : 40 + (i - 40) = i := by omega
    simp [h8, heq, show i ≥ 40 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show i - 40 < 8 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h56 : i < 56
  · have heq : 48 + (i - 48) = i := by omega
    simp [h8, heq, show i ≥ 48 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show ¬ i - 40 < 8 by omega, show i - 48 < 8 by omega, show ¬ i ≥ 56 by omega]
  by_cases h64 : i < 64
  · have heq : 56 + (i - 56) = i := by omega
    simp [h8, heq, show i ≥ 56 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show ¬ i - 40 < 8 by omega, show ¬ i - 48 < 8 by omega, show i - 56 < 8 by omega]
  · have hibound : n.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h8, hibound, show ¬ i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show ¬ i - 40 < 8 by omega, show ¬ i - 48 < 8 by omega, show ¬ i - 56 < 8 by omega]
