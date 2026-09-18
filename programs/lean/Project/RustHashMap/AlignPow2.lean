import Project.RustHashMap.Allocator

/-!
# Bump alignment at every power of two

`Project.RustHashMap.Allocator.classifyBump_success_reachable` asks the caller
for `layout.alignment = 1 ∨ layout.alignment = 4`.  The restriction is in the
proof, not in the compiled allocator: the two branches of that proof use
`align1_mask` and `align4_mask_toNat`, and both are instances of one mask
equation.

The hash map needs one more alignment.  `func 17`, the table resize, calls the
allocator with alignment 8 at WAT 3682 to 3686, so the current contract does
not cover it.

This module removes the restriction.  `alignPow2_mask_toNat` gives the mask
equation at every power of two below `2 ^ 32`, and `classifyBump_success_pow2`
is `classifyBump_success_reachable` with the alignment hypothesis deleted.  No
hypothesis replaces it: `AllocLayout.Valid` already carries
`∃ exponent, alignment = 2 ^ exponent` and `alignment ≤ 2147483648`, which is
all the mask equation needs.

`negOne_add_pred` is the second alignment-specific step of `Func55Proof`.  The
compiled body adds `0xFFFFFFFF` to the alignment word to make the pad, and the
current proof closes that step with one `decide` per alignment.
-/

namespace Project.RustHashMap.AlignPow2

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Allocator
open Project.RustHashMap.Contracts
open scoped Wasm.SmallStep.Outcome

/-! ## The mask -/

/-- The negated power of two, as a natural number. -/
theorem neg_two_pow_toNat (exponent : Nat) (hexponent : exponent ≤ 31) :
    (0 - UInt32.ofNat (2 ^ exponent)).toNat = 4294967296 - 2 ^ exponent := by
  have hupper : (2 : Nat) ^ exponent ≤ 2 ^ 31 :=
    Nat.pow_le_pow_right (by decide) hexponent
  have hlower : (0 : Nat) < 2 ^ exponent := Nat.two_pow_pos exponent
  have hpow : (2 : Nat) ^ 31 = 2147483648 := by norm_num
  rw [hpow] at hupper
  have hword : (UInt32.ofNat (2 ^ exponent)).toNat = 2 ^ exponent :=
    UInt32.toNat_ofNat_of_lt'
      (by change (2 : Nat) ^ exponent < 4294967296; omega)
  simp only [UInt32.toNat_sub, UInt32.toNat_ofNat, hword]
  omega

/-- The negated power of two is the all-ones word shifted left. -/
theorem neg_two_pow_toBitVec (exponent : Nat) (hexponent : exponent ≤ 31) :
    ((0 : UInt32) - UInt32.ofNat (2 ^ exponent)).toBitVec
      = BitVec.allOnes 32 <<< exponent := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_allOnes]
  have hleft : ((0 : UInt32) - UInt32.ofNat (2 ^ exponent)).toBitVec.toNat
      = 4294967296 - 2 ^ exponent := neg_two_pow_toNat exponent hexponent
  rw [hleft, Nat.shiftLeft_eq]
  have hupper : (2 : Nat) ^ exponent ≤ 2 ^ 31 :=
    Nat.pow_le_pow_right (by decide) hexponent
  have hlower : (0 : Nat) < 2 ^ exponent := Nat.two_pow_pos exponent
  have hpow : (2 : Nat) ^ 31 = 2147483648 := by norm_num
  rw [hpow] at hupper
  norm_num
  omega

/-- The alignment mask at every power of two: rounding down by a mask is
subtraction of the remainder.  This is `align4_mask_toNat` of `Allocator.lean`
with the exponent left free. -/
theorem alignPow2_mask_toNat (x : UInt32) (exponent : Nat)
    (hexponent : exponent ≤ 31) :
    (x &&& (0 - UInt32.ofNat (2 ^ exponent))).toNat
      = x.toNat - x.toNat % 2 ^ exponent := by
  change (x.toBitVec &&&
      ((0 - UInt32.ofNat (2 ^ exponent) : UInt32).toBitVec)).toNat =
    x.toBitVec.toNat - x.toBitVec.toNat % 2 ^ exponent
  rw [neg_two_pow_toBitVec exponent hexponent, ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hlt : x.toBitVec.toNat < 2 ^ 32 := x.toBitVec.isLt
  have hle :
      x.toBitVec.toNat / 2 ^ exponent * 2 ^ exponent ≤ x.toBitVec.toNat :=
    Nat.div_mul_le_self _ _
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hdivmod := Nat.div_add_mod x.toBitVec.toNat (2 ^ exponent)
  omega

/-! ## The bump classification -/

/-- A valid layout has an exponent below 32. -/
theorem exponent_le_31 {layout : AllocLayout} {exponent : Nat}
    (hvalid : layout.Valid) (hexp : layout.alignment = 2 ^ exponent) :
    exponent ≤ 31 := by
  have halignLe : layout.alignment ≤ 2147483648 := hvalid.2.2.2.1
  by_contra hcontra
  have h32 : (2 : Nat) ^ 32 ≤ 2 ^ exponent :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [← hexp] at h32
  norm_num at h32
  omega

/-- `classifyBump_success_reachable` at every alignment.  The hypothesis
`layout.alignment = 1 ∨ layout.alignment = 4` is deleted and nothing replaces
it: `AllocLayout.Valid` already says that the alignment is a power of two below
`2 ^ 32`. -/
theorem classifyBump_success_pow2
    (frontier : Nat) (layout : AllocLayout) (base finish : UInt32)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvalid : layout.Valid)
    (hclassify : classifyBump frontier layout = .success base finish) :
    frontier ≤ base.toNat ∧
    base ≠ 0 ∧
    base.toNat % layout.alignment = 0 ∧
    base.toNat + layout.size < UInt32.size ∧
    base.toNat + layout.size < 2147483648 ∧
    finish.toNat = base.toNat + layout.size ∧
    AllocationMetaValid (liveMeta base layout) := by
  have hraw := classifyBump_success_facts frontier layout base finish hclassify
  dsimp only at hraw
  rcases hraw with ⟨hsum, hbase, hendWord, hendSigned, hfinish⟩
  obtain ⟨exponent, hexp⟩ := hvalid.2.2.1
  have hpos : 0 < layout.alignment := hvalid.2.1
  have hexponent : exponent ≤ 31 := exponent_le_31 hvalid hexp
  have hsumWord : (UInt32.ofNat (frontier + (layout.alignment - 1))).toNat
      = frontier + (layout.alignment - 1) := UInt32.toNat_ofNat_of_lt' hsum
  have hmask := alignPow2_mask_toNat
    (UInt32.ofNat (frontier + (layout.alignment - 1))) exponent hexponent
  rw [hsumWord, ← hexp] at hmask
  have hbaseNat : base.toNat
      = (frontier + (layout.alignment - 1))
        - (frontier + (layout.alignment - 1)) % layout.alignment := by
    rw [hbase]; exact hmask
  have hrem : (frontier + (layout.alignment - 1)) % layout.alignment
      < layout.alignment := Nat.mod_lt _ hpos
  have hstart : frontier ≤ base.toNat := by omega
  have hmod : base.toNat % layout.alignment = 0 := by
    rw [hbaseNat]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub_mod _)
  have hheapBasePositive : 0 < heapBase.toNat := by decide
  have hnonnull : base ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    simp only [UInt32.toNat_zero] at hzeroNat
    omega
  exact ⟨hstart, hnonnull, hmod, hendWord, hendSigned, hfinish,
    hvalid, hnonnull, hmod⟩

/-! ## The pad word -/

/-- The compiled allocator makes the alignment pad by adding `0xFFFFFFFF` to
the alignment word.  `Func55Proof` closes that step with one `decide` per
alignment; this is the same step at every alignment. -/
theorem negOne_add_pred (alignmentWord : UInt32) (alignment : Nat)
    (hword : alignmentWord.toNat = alignment)
    (hpos : 0 < alignment) (hle : alignment ≤ 2147483648) :
    (0xFFFFFFFF : UInt32) + alignmentWord = UInt32.ofNat (alignment - 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, hword,
    UInt32.toNat_ofNat_of_lt' (by change alignment - 1 < 4294967296; omega)]
  change (4294967295 + alignment) % 4294967296 = alignment - 1
  omega

/-! ## The commit -/

/-- `Allocator.BumpHeap_commit` at every power of two.
`classifyBump_success_pow2` gives the range facts, so the alignment
disjunct disappears here as well. -/
theorem BumpHeap_commit_pow2 {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (frontier : Nat) (history : AllocationHistory)
    (base finish : UInt32) (layout : AllocLayout) (bytes : List UInt8)
    (ownedPages : Nat)
    (hheapBase : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hvalid : layout.Valid)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hbytesLength : bytes.length = layout.size)
    (hphysical : finish.toNat ≤ ownedPages * 65536) :
    pointsTo_u32 0 allocatorCursor finish ∗
      heapFrontierOwn finish.toNat ∗
      AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗
      memoryPagesOwn ownedPages ∗
      Slices.ByteSlice 0 base bytes ==∗
      BumpHeap heapId finish finish.toNat
          (history.allocate base layout) ∗
        LiveBlock heapId history.nextId base layout bytes :=
  BumpHeap_commit_of_facts heapId frontier history base finish layout bytes
    ownedPages hheapBase hwf
    (classifyBump_success_pow2 frontier layout base finish hheapBase hvalid
      hclassify)
    hbytesLength hphysical

end Project.RustHashMap.AlignPow2
