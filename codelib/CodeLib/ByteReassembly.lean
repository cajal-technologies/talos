import CodeLib.UInt32

/-! Byte projections of two adjacent 32-bit words packed into a 64-bit word. -/

theorem UInt64.pack32_byte0 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 0).toUInt8) =
      (lo >>> 0).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega)

theorem UInt64.pack32_byte1 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 8).toUInt8) =
      (lo >>> 8).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [show 8 + i < 32 by omega]

theorem UInt64.pack32_byte2 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 16).toUInt8) =
      (lo >>> 16).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [show 16 + i < 32 by omega]

theorem UInt64.pack32_byte3 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 24).toUInt8) =
      (lo >>> 24).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [show 24 + i < 32 by omega]

theorem UInt64.pack32_byte4 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 32).toUInt8) =
      (hi >>> 0).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [show ¬ 32 + i < 32 by omega, show 32 + i - 32 = 0 + i by omega]

theorem UInt64.pack32_byte5 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 40).toUInt8) =
      (hi >>> 8).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [show ¬ 40 + i < 32 by omega, show 40 + i - 32 = 8 + i by omega]

theorem UInt64.pack32_byte6 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 48).toUInt8) =
      (hi >>> 16).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [show ¬ 48 + i < 32 by omega, show 48 + i - 32 = 16 + i by omega]

theorem UInt64.pack32_byte7 (lo hi : UInt32) :
    (((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> 56).toUInt8) =
      (hi >>> 24).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [show ¬ 56 + i < 32 by omega, show 56 + i - 32 = 24 + i by omega]

theorem UInt64.packBytes_low32 (a b c d e f g h : UInt8) :
    (a.toUInt64 ||| (b.toUInt64 <<< 8) ||| (c.toUInt64 <<< 16) |||
      (d.toUInt64 <<< 24) ||| (e.toUInt64 <<< 32) ||| (f.toUInt64 <<< 40) |||
      (g.toUInt64 <<< 48) ||| (h.toUInt64 <<< 56)).toUInt32 =
    a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24) := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt64, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt32]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega)


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
