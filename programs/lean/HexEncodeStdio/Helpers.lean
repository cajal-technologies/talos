import CodeLib

/-!
Local helper module for the submission. Solvers may add lemmas and definitions
here (and in sibling modules under `Submission/`) and import them from
`Project.HexEncodeStdio.lean`.
-/

namespace Project.HexEncodeStdio.Helpers

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private theorem byte_high_nat (lo hi i : Nat) (hlo : lo < 2 ^ 32) (hi4 : i < 4) :
    ((lo ||| ((hi <<< 32) % 2 ^ 64)) >>> (32 + 8 * i)) % 2 ^ 8 = (hi >>> (8 * i)) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hk : k < 8
  · have hlofalse : lo.testBit (32 + 8 * i + k) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [hk, hlofalse, Bool.false_or, decide_true, Bool.true_and,
      show 32 ≤ 32 + 8 * i + k by omega, show 32 + 8 * i + k < 64 by omega]
    congr 1
    omega
  · simp only [hk, decide_false, Bool.false_and]

private theorem byte_low_nat (lo hi i : Nat) (hi4 : i < 4) :
    ((lo ||| ((hi <<< 32) % 2 ^ 64)) >>> (8 * i)) % 2 ^ 8 = (lo >>> (8 * i)) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hk : k < 8
  · simp only [hk, decide_true, Bool.true_and, show ¬ (32 ≤ 8 * i + k) by omega,
      decide_false, Bool.false_and, Bool.and_false, Bool.or_false]
  · simp only [hk, decide_false, Bool.false_and]

private theorem packed_u64Byte_low (lo hi : UInt32) (i : Nat) (hi4 : i < 4) :
    u64Byte (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) i = u32Byte lo i := by
  interval_cases i <;>
    (apply UInt8.toNat_inj.mp
     simp only [u64Byte, u32Byte, UInt64.toNat_toUInt8, UInt32.toNat_toUInt8,
       UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_shiftLeft,
       UInt32.toNat_toUInt64, UInt32.toNat_shiftRight, UInt64.toNat_ofNat,
       UInt32.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
     exact byte_low_nat lo.toNat hi.toNat _ (by omega))

private theorem packed_u64Byte_high (lo hi : UInt32) (i : Nat) (hi4 : i < 4) :
    u64Byte (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) (i + 4) = u32Byte hi i := by
  interval_cases i <;>
    (apply UInt8.toNat_inj.mp
     simp only [u64Byte, u32Byte, UInt64.toNat_toUInt8, UInt32.toNat_toUInt8,
       UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_shiftLeft,
       UInt32.toNat_toUInt64, UInt32.toNat_shiftRight, UInt64.toNat_ofNat,
       UInt32.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
     exact byte_high_nat lo.toNat hi.toNat _ (UInt32.toNat_lt lo) (by omega))

/-- Split a little-endian 64-bit cell into its low and high 32-bit halves. -/
theorem pointsTo_u64_pair_split {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
    (memId : Nat) (addr lo hi : UInt32) :
    pointsTo_u64 (α := α) memId addr
        (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) ⊢
      (iprop% pointsTo_u32 memId addr lo ∗
        pointsTo_u32 memId (addr + 4) hi) := by
  rw [(pointsTo_u64_eq memId addr
      (lo.toUInt64 ||| (hi.toUInt64 <<< 32))).to_eq,
    (pointsTo_u32_eq memId addr lo).to_eq,
    (pointsTo_u32_eq memId (addr + 4) hi).to_eq]
  rw [packed_u64Byte_low lo hi 0 (by omega),
    packed_u64Byte_low lo hi 1 (by omega),
    packed_u64Byte_low lo hi 2 (by omega),
    packed_u64Byte_low lo hi 3 (by omega),
    packed_u64Byte_high lo hi 0 (by omega),
    packed_u64Byte_high lo hi 1 (by omega),
    packed_u64Byte_high lo hi 2 (by omega),
    packed_u64Byte_high lo hi 3 (by omega)]
  have h5 : addr + 5 = (addr + 4) + 1 := by bv_normalize (config := { enums := false })
  have h6 : addr + 6 = (addr + 4) + 2 := by bv_normalize (config := { enums := false })
  have h7 : addr + 7 = (addr + 4) + 3 := by bv_normalize (config := { enums := false })
  rw [← h5, ← h6, ← h7]
  iintro H
  icases H with ⟨H0, H⟩
  icases H with ⟨H1, H⟩
  icases H with ⟨H2, H⟩
  icases H with ⟨H3, H⟩
  icases H with ⟨H4, H⟩
  icases H with ⟨H5, H⟩
  icases H with ⟨H6, H7⟩
  isplitl [H0 H1 H2 H3]
  · iframe
  · iframe

/-- Join adjacent low and high 32-bit cells into their little-endian word. -/
theorem pointsTo_u64_pair_join {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
    (memId : Nat) (addr lo hi : UInt32) :
    (iprop% pointsTo_u32 memId addr lo ∗
      pointsTo_u32 memId (addr + 4) hi) ⊢
    pointsTo_u64 (α := α) memId addr
      (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) := by
  rw [(pointsTo_u64_eq memId addr
      (lo.toUInt64 ||| (hi.toUInt64 <<< 32))).to_eq,
    (pointsTo_u32_eq memId addr lo).to_eq,
    (pointsTo_u32_eq memId (addr + 4) hi).to_eq]
  rw [packed_u64Byte_low lo hi 0 (by omega),
    packed_u64Byte_low lo hi 1 (by omega),
    packed_u64Byte_low lo hi 2 (by omega),
    packed_u64Byte_low lo hi 3 (by omega),
    packed_u64Byte_high lo hi 0 (by omega),
    packed_u64Byte_high lo hi 1 (by omega),
    packed_u64Byte_high lo hi 2 (by omega),
    packed_u64Byte_high lo hi 3 (by omega)]
  have h5 : addr + 5 = (addr + 4) + 1 := by bv_normalize (config := { enums := false })
  have h6 : addr + 6 = (addr + 4) + 2 := by bv_normalize (config := { enums := false })
  have h7 : addr + 7 = (addr + 4) + 3 := by bv_normalize (config := { enums := false })
  rw [← h5, ← h6, ← h7]
  iintro H
  icases H with ⟨Hlo, Hhi⟩
  icases Hlo with ⟨H0, Hlo⟩
  icases Hlo with ⟨H1, Hlo⟩
  icases Hlo with ⟨H2, H3⟩
  icases Hhi with ⟨H4, Hhi⟩
  icases Hhi with ⟨H5, Hhi⟩
  icases Hhi with ⟨H6, H7⟩
  iframe

/-- Zero-offset store rule with its points-to address normalized. -/
theorem wp_store8_zero {hlc : HasLC} {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value} {address value : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldByte : UInt8) :
    ▷ (⟨0, address⟩ ↦w oldByte) -∗
    ▷ ((⟨0, address⟩ ↦w value.toUInt8) -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) -∗
    WP (.running ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
      .store8 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} := by
  simpa only [UInt32.add_zero] using
    (Wasm.SmallStep.wp_store8 (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (value := value) oldByte (by simp))

end Project.HexEncodeStdio.Helpers
