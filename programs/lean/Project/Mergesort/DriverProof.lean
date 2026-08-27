import Project.Mergesort.ContractProofs

set_option maxRecDepth 1048576

/-!
# Generated merge-sort driver proof

This file proves `func3` in phases.  The first phase below consumes the raw
entry stack region and executes the generated prologue, producing the exact
empty `ExportFrame` representation used by the reviewed driver contract.
-/

namespace Project.Mergesort.DriverProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

/-- The first instruction after the generated stack/Vec initialization. -/
private def func3AfterInit : Program :=
  Project.Mergesort.func3.drop 21

/-- Exact locals after the generated stack/Vec initialization. -/
private def func3InitializedLocals : Locals :=
  { locals :=
      [.i32 driverBase, .i32 0, .i32 4, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] }

/-- Two adjacent little-endian 32-bit cells are the corresponding 64-bit
cell.  The generated prologue uses a single `i64.store` for the capacity and
pointer fields, while the authoritative Vec representation exposes them as
two `i32` cells. -/
private theorem pointsTo_u32_pair_as_u64
    [WasmHeapGS Universal.State]
    (ptr lo hi : UInt32) :
    iprop(pointsTo_u32 0 ptr lo ∗ pointsTo_u32 0 (ptr + 4) hi) ⊣⊢
      pointsTo_u64 0 ptr
        (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) := by
  let combined : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
  have h0 : u64Byte combined 0 = u32Byte lo 0 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h1 : u64Byte combined 1 = u32Byte lo 1 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h2 : u64Byte combined 2 = u32Byte lo 2 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h3 : u64Byte combined 3 = u32Byte lo 3 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h4 : u64Byte combined 4 = u32Byte hi 0 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h5 : u64Byte combined 5 = u32Byte hi 1 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h6 : u64Byte combined 6 = u32Byte hi 2 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h7 : u64Byte combined 7 = u32Byte hi 3 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  change iprop(pointsTo_u32 0 ptr lo ∗ pointsTo_u32 0 (ptr + 4) hi) ⊣⊢
    pointsTo_u64 0 ptr combined
  unfold pointsTo_u32 pointsTo_u64
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [show ptr + 4 + 1 = ptr + 5 by bv_decide]
  rw [show ptr + 4 + 2 = ptr + 6 by bv_decide]
  rw [show ptr + 4 + 3 = ptr + 7 by bv_decide]
  constructor
  · iintro H
    icases H with ⟨Hlo, Hhi⟩
    icases Hlo with ⟨H0, H1, H2, H3⟩
    icases Hhi with ⟨H4, H5, H6, H7⟩
    iframe
  · iintro H
    icases H with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
    iframe

/-- The offset-zero form of `twp_store64`, stated without the syntactic
`address + 0` in its owned cell. -/
private theorem twp_store64_zero
    {hlc : HasLC} {α : Type} [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)}
    {params localValues values : List Value}
    {address : UInt32} {value : UInt64}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldWord : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    pointsTo_u64 0 address oldWord -∗
    (pointsTo_u64 0 address value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues,
        .i64 value :: .i32 address :: values⟩,
      .store64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  simpa only [UInt32.add_zero, Nat.add_zero] using
    (twp_store64 (α := α) (Terminal := ObservableOutcome)
      (address := address) (offset := 0) (value := value) oldWord
      (by simp) (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4) (by simpa using h5)
      (by simpa using h6) (by simpa using h7))

/-- Execute the generated `func3` prologue from raw entry ownership to the
reviewed initialized-frame representation.  No allocator, host call, or
driver semantic assumption is used here. -/
theorem twp_func3_initialize
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (entryBytes : List UInt8)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      StackPointer entryStackTop ∗
      StackRegion entryStackLow entryBytes ∗
      ⌜entryBytes.length = 288⌝ ∗
      (∀ reserveBytes : List UInt8,
        ∀ outputBytes : List UInt8,
        StackPointer driverBase -∗
        StackReserve reserveBase reserveBytes -∗
        ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes -∗
        WP (.running
          ⟨func3InitializedLocals, func3AfterInit, 0, [], [], calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
          0, [], [], calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hsp, Hentry, %hentryLength, Hcont⟩
  ihave HentryParts :
      iprop(StackRegion entryStackLow entryBytes ∗
        ⌜entryBytes.length = 288⌝) $$ [Hentry]
  · isplitl [Hentry]
    · iexact Hentry
    · ipureintro
      exact hentryLength
  icases (EntryStack_split entryBytes).mp $$ HentryParts with
    ⟨%reserveBytes, %frameBytes, %hentryParts, Hreserve, Hframe⟩
  icases (DriverFrame_split frameBytes hentryParts.2.2).mp $$ Hframe with
    ⟨%headerBytes, %chunkBytes, %outputBytes, %hframeParts,
      Hheader, Hchunk, Houtput⟩
  have hdecode := serialize_decodeWords_of_length headerBytes 3 (by omega)
  obtain ⟨oldCapacity, oldPointer, oldLength, hdecoded⟩ :
      ∃ a b c : UInt32, decodeWords headerBytes = [a, b, c] := by
    rcases hwords : decodeWords headerBytes with _ | ⟨a, rest⟩
    · simp [hwords] at hdecode
    rcases hrest : rest with _ | ⟨b, rest⟩
    · simp [hwords, hrest] at hdecode
    rcases hrest2 : rest with _ | ⟨c, rest⟩
    · simp [hwords, hrest, hrest2] at hdecode
    rcases rest with _ | ⟨d, rest⟩
    · exact ⟨a, b, c, by simp⟩
    · simp [hwords, hrest, hrest2] at hdecode
  ihave HwordSlice := (ByteSlice_as_decodedWordSlice
      driverBase headerBytes 3 (by decide) hframeParts.2.1).mp $$ Hheader
  isimp only [WordSlice,
    Project.Mergesort.Representations.ByteSlice] at HwordSlice
  icases HwordSlice with ⟨%_halign, %_hwordNowrap, HwordBytes⟩
  ihave Harray : arrayAt 0 driverBase (decodeWords headerBytes) $$
      [HwordBytes]
  · iapply (arrayAt_eq_wordCells driverBase
      (decodeWords headerBytes)).mpr
    iexact HwordBytes
  isimp only [hdecoded] at Harray
  isimp only [arrayAt] at Harray
  icases Harray with ⟨HoldCapacity, HoldPointer, HoldLength, _Hemp⟩
  ihave HoldLength' :
      pointsTo_u32 0 (driverBase + 8) oldLength $$ [HoldLength]
  · rw [← show driverBase + 4 + 4 = driverBase + 8 by decide]
    iexact HoldLength
  ihave HoldPair := (pointsTo_u32_pair_as_u64
      driverBase oldCapacity oldPointer).mp $$ [HoldCapacity HoldPointer]
  · iframe
  isimp only [StackPointer] at Hsp
  simp only [Project.Mergesort.func3]
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  rw [show entryStackTop - 272 = driverBase by decide]
  iapply twp_localTee rfl
  simp [Project.Mergesort.func3Def, Function.toLocals]
  iapply twp_globalSet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length_nil, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldLength (by decide) (by decide) (by decide)
      (by decide) $$ HoldLength'
  iintro Hlength
  iapply twp_localGet rfl
  iapply twp_pureStep _ _ _ (fun _ => Step.constI64)
  iapply twp_store64_zero (address := driverBase)
      (value := 4294967296)
      (oldCapacity.toUInt64 ||| (oldPointer.toUInt64 <<< 32))
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HoldPair
  iintro Hpair
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show 12 + driverBase = driverBase + 12 by decide]
  iapply twp_const
  iapply twp_const
  isimp only [Project.Mergesort.Representations.ByteSlice] at Hchunk
  icases Hchunk with ⟨%hchunkNowrap, HchunkBytes⟩
  iapply twp_memoryFill32 chunkBytes (by
      simp [hframeParts.2.2.1]) (by decide) (by
      simpa [hframeParts.2.2.1, UInt32.size] using hchunkNowrap) $$
      HchunkBytes
  iintro HchunkBytes
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length_nil, Nat.reduceSub, List.set]
  ihave HpairWords :
      iprop(pointsTo_u32 0 driverBase 0 ∗
        pointsTo_u32 0 (driverBase + 4) 1) $$ [Hpair]
  · iapply (pointsTo_u32_pair_as_u64 driverBase 0 1).mpr
    rw [show (0 : UInt32).toUInt64 ||| ((1 : UInt32).toUInt64 <<< 32) =
      (4294967296 : UInt64) by decide]
    iexact Hpair
  icases HpairWords with ⟨Hcapacity, Hpointer⟩
  ihave Harray :
      arrayAt 0 driverBase [0, 1, 0] $$ [Hcapacity Hpointer Hlength]
  · isimp only [arrayAt]
    isplitl [Hcapacity]
    · iexact Hcapacity
    isplitl [Hpointer]
    · iexact Hpointer
    isplitl [Hlength]
    · rw [show driverBase + 4 + 4 = driverBase + 8 by decide]
      iexact Hlength
    · itrivial
  ihave HheaderBytes : WordCells driverBase [0, 1, 0] $$ [Harray]
  · iapply (arrayAt_eq_wordCells driverBase [0, 1, 0]).mp
    iexact Harray
  ihave Hheader : Project.Mergesort.Representations.ByteSlice
      driverBase emptyVecHeaderBytes $$ [HheaderBytes]
  · unfold Project.Mergesort.Representations.ByteSlice emptyVecHeaderBytes
    isplitl []
    · ipureintro
      decide
    · iexact HheaderBytes
  ihave Hchunk : Project.Mergesort.Representations.ByteSlice
      (driverBase + 12) (List.replicate 256 0) $$ [HchunkBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    isplitl []
    · ipureintro
      simpa [hframeParts.2.2.1] using hchunkNowrap
    · rw [← hframeParts.2.2.1]
      rw [← show (0 : UInt32).toUInt8 = (0 : UInt8) by decide]
      iexact HchunkBytes
  ihave Hexport := ExportFrame_empty heapId (List.replicate 256 0)
      outputBytes (by simp) hframeParts.2.2.2 $$ [Hheader Hchunk Houtput]
  · iframe
  ihave Hsp' : StackPointer driverBase $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  isimp only [List.replicate] at Hexport
  ihave Hdone := Hcont $$ %reserveBytes %outputBytes Hsp' Hreserve Hexport
  isimp only [func3InitializedLocals, func3AfterInit,
    Project.Mergesort.func3, List.drop_succ_cons, List.drop_zero,
    ValueType.zero] at Hdone
  isimp only [ValueType.zero]
  iexact Hdone

end Project.Mergesort.DriverProof
