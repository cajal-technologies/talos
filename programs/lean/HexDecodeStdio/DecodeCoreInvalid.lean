import HexDecodeStdio.DecodeCore
import HexDecodeStdio.DecodeIteratorInvalid
import HexDecodeStdio.DecodeIteratorInvalidLow
import HexDecodeStdio.HexMath

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

set_option maxHeartbeats 5000000 in
/-- If the first byte of a nonempty even input is invalid, the core decoder
returns the generated `InvalidHexCharacter` result with index zero. -/
theorem twp_decode_invalid_high_first
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (out inputPtr len sp : UInt32) (hi lo : UInt8)
    (oldMarker oldErrorIndex oldInputLen oldInputPtr oldErrorPtr : UInt32)
    (oldPair : UInt64) (oldTag oldPayload : UInt8)
    (oldOutCap oldOutPtr oldOutLen : UInt32)
    (heven : len &&& (1 : UInt32) = 0) (hlen : 2 ≤ len.toNat)
    (hhi : hexValue hi = none)
    (hmarker : Offset32Facts (sp - 96) 32)
    (herrorIndexBase : Offset32Facts (sp - 96) 36)
    (hpairNoWrap : ((sp - 96) + 48).toNat =
      (sp - 96).toNat + (48 : UInt32).toNat)
    (hpair : Address64Facts ((sp - 96) + 48))
    (hinputLen : Offset32Facts (sp - 96) 44)
    (hinputPtr : Offset32Facts (sp - 96) 40)
    (herrorPtr : Offset32Facts (sp - 96) 56)
    (hiterLen : Offset32Facts ((sp - 96) + 40) 4)
    (hiterError : Offset32Facts ((sp - 96) + 40) 16)
    (hiterChunk : Offset32Facts ((sp - 96) + 40) 8)
    (hiterPtr : Offset32Facts ((sp - 96) + 40) 0)
    (hiterIndex : Offset32Facts ((sp - 96) + 40) 12)
    (herrorWord : Offset32Facts (32 + (sp - 96)) 0)
    (herrorIndex : Offset32Facts (32 + (sp - 96)) 4)
    (hinput0 : (inputPtr + 0).toNat = inputPtr.toNat)
    (hinput1 : (inputPtr + 1).toNat = inputPtr.toNat + 1)
    (htagAddr : Offset32Facts (sp - 96) 24)
    (houtCap : Offset32Facts out 0)
    (houtPtr : Offset32Facts out 4)
    (houtLen : Offset32Facts out 8)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u32 0 ((sp - 96) + 32) oldMarker ∗
      pointsTo_u32 0 ((sp - 96) + 36) oldErrorIndex ∗
      pointsTo_u64 0 ((sp - 96) + 48) oldPair ∗
      pointsTo_u32 0 ((sp - 96) + 44) oldInputLen ∗
      pointsTo_u32 0 ((sp - 96) + 40) oldInputPtr ∗
      pointsTo_u32 0 ((sp - 96) + 56) oldErrorPtr ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, (sp - 96) + 24⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, ((sp - 96) + 24) + 1⟩ (DFrac.own 1) (some oldPayload) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 0⟩ (DFrac.own 1) (some hi) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 1⟩ (DFrac.own 1) (some lo) ∗
      pointsTo_u32 0 out oldOutCap ∗
      pointsTo_u32 0 (out + 4) oldOutPtr ∗
      pointsTo_u32 0 (out + 8) oldOutLen -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u32 0 out 2147483648 ∗
      pointsTo_u32 0 (out + 4) (hi.toUInt32 &&& 255) ∗
      pointsTo_u32 0 (out + 8) 0 -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 len, .i32 inputPtr, .i32 out] ++ stack },
        [.call 8] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hmarker, HerrorIndex, Hpair, HinputLen,
    HinputPtr, HerrorPtr, Htag, Hpayload, Hhi, Hlo,
    HoutCap, HoutPtr, HoutLen⟩ Hcont
  simp only [List.singleton_append]
  iapply twp_call «module» 8 func5Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero, func5]
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localTee rfl
  iapply twp_globalSet $$ Hsp
  iintro Hframe
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [heven]
  simp
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldMarker hmarker.noWrap hmarker.one hmarker.two
      hmarker.three $$ Hmarker
  iintro Hmarker
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 (address := sp - 96) (offset := 48) (value := 2)
      oldPair hpairNoWrap hpair.one hpair.two hpair.three hpair.four
      hpair.five hpair.six hpair.seven $$ Hpair
  iintro Hpair
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldInputLen hinputLen.noWrap hinputLen.one
      hinputLen.two hinputLen.three $$ HinputLen
  iintro HinputLen
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldInputPtr hinputPtr.noWrap hinputPtr.one
      hinputPtr.two hinputPtr.three $$ HinputPtr
  iintro HinputPtr
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_store32 oldErrorPtr herrorPtr.noWrap herrorPtr.one
      herrorPtr.two herrorPtr.three $$ HerrorPtr
  iintro HerrorPtr
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  ihave HpairWords := pointsTo_u64_two_as_u32 ((sp - 96) + 48) |>.mp $$ Hpair
  icases HpairWords with ⟨HchunkRaw, HindexRaw⟩
  have hlenEq : (sp - 96) + 44 = ((sp - 96) + 40) + 4 := by bv_decide
  have hchunkEq : (sp - 96) + 48 = ((sp - 96) + 40) + 8 := by bv_decide
  have hindexEq : ((sp - 96) + 48) + 4 = ((sp - 96) + 40) + 12 := by bv_decide
  have herrorPtrEq : (sp - 96) + 56 = ((sp - 96) + 40) + 16 := by bv_decide
  have herrorWordEq : (sp - 96) + 32 = (32 + (sp - 96)) + 0 := by bv_decide
  have herrorIndexEq : (sp - 96) + 36 = (32 + (sp - 96)) + 4 := by bv_decide
  ihave HlenIter : pointsTo_u32 0 (((sp - 96) + 40) + 4) len $$ [HinputLen]
  · rw [← hlenEq]; iexact HinputLen
  ihave Hchunk : pointsTo_u32 0 (((sp - 96) + 40) + 8) 2 $$ [HchunkRaw]
  · rw [← hchunkEq]; iexact HchunkRaw
  ihave Hindex : pointsTo_u32 0 (((sp - 96) + 40) + 12) 0 $$ [HindexRaw]
  · rw [← hindexEq]; iexact HindexRaw
  ihave HerrorPtrIter : pointsTo_u32 0 (((sp - 96) + 40) + 16)
      (32 + (sp - 96)) $$ [HerrorPtr]
  · rw [← herrorPtrEq]; iexact HerrorPtr
  ihave HerrorWord : pointsTo_u32 0 ((32 + (sp - 96)) + 0) 1114114 $$ [Hmarker]
  · rw [← herrorWordEq]; iexact Hmarker
  ihave HerrorIndexIter : pointsTo_u32 0 ((32 + (sp - 96)) + 4)
      oldErrorIndex $$ [HerrorIndex]
  · rw [← herrorIndexEq]; iexact HerrorIndex
  ihave HhiAddr : pointsTo (GF := WasmHeapGF Universal.State)
      (H := WasmHeapMap) ⟨0, inputPtr⟩ (DFrac.own 1) (some hi) $$ [Hhi]
  · rw [← UInt32.add_zero inputPtr]
    iexact Hhi
  rw [show 40 + (sp - 96) = (sp - 96) + 40 by bv_decide,
    show 24 + (sp - 96) = (sp - 96) + 24 by bv_decide]
  obtain ⟨hhiUpper, hhiLower, hhiDigit⟩ := hexValue_none_tests hi hhi
  iapply twp_decodePair_invalid_high
      (out := (sp - 96) + 24) (iterator := (sp - 96) + 40)
      (inputPtr := inputPtr) (errorPtr := 32 + (sp - 96))
      (len := len) (chunkIndex := 0) hi lo oldTag oldPayload
      1114114 oldErrorIndex hlen hiterLen hiterError hiterChunk hiterPtr
      hiterIndex herrorWord herrorIndex hinput0 hinput1 htagAddr.one
      hhiUpper hhiLower hhiDigit
      (callerParams := [.i32 out, .i32 inputPtr, .i32 len])
      (callerLocalValues := [.i32 (sp - 96), .i32 1, .i32 0])
      (stack := []) $$ [$Hruntime $HlenIter $HerrorPtrIter $Hchunk
        $HinputPtr $Hindex $HerrorWord $HerrorIndexIter $HhiAddr $Hlo
        $Hpayload $Htag]
  iintro ⟨Hruntime, HlenIter, HerrorPtrIter, Hchunk, HinputPtr,
    Hindex, HerrorWord, HerrorIndex, Hhi, Hlo, Hpayload, Htag⟩
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load8U 0 htagAddr.noWrap $$ Htag
  iintro Htag
  iapply twp_eqz rfl
  iapply twp_brIf (by decide) rfl
  iapply twp_block
  iapply twp_localGet rfl
  ihave Hmarker : pointsTo_u32 0 ((sp - 96) + 32)
      (hi.toUInt32 &&& 255) $$ [HerrorWord]
  · rw [herrorWordEq]; iexact HerrorWord
  iapply twp_load32 (hi.toUInt32 &&& 255) hmarker.noWrap hmarker.one
      hmarker.two hmarker.three $$ Hmarker
  iintro Hmarker
  iapply twp_localTee rfl
  iapply twp_const
  have hnotMarker : hi.toUInt32 &&& 255 ≠ 1114114 := by bv_decide
  iapply hdtwp_eq (result := 0) (by simp [hnotMarker])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HerrorIndexBase : pointsTo_u32 0 ((sp - 96) + 36) 0 $$ [HerrorIndex]
  · rw [herrorIndexEq]
    norm_num
    iexact HerrorIndex
  iapply twp_load32 0 herrorIndexBase.noWrap herrorIndexBase.one
      herrorIndexBase.two herrorIndexBase.three $$ HerrorIndexBase
  iintro HerrorIndexBase
  iapply twp_store32 oldOutLen houtLen.noWrap houtLen.one houtLen.two
      houtLen.three $$ HoutLen
  iintro HoutLen
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldOutPtr houtPtr.noWrap houtPtr.one houtPtr.two
      houtPtr.three $$ HoutPtr
  iintro HoutPtr
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32_addr (address := out) (value := 2147483648) oldOutCap
      (by simpa using houtCap.one) (by simpa using houtCap.two)
      (by simpa using houtCap.three) $$ HoutCap
  iintro HoutCap
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  have hrestore : 96 + (sp - 96) = sp := by bv_decide
  rw [hrestore]
  iapply twp_globalSet $$ Hframe
  iintro Hsp
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  iapply Hcont
  iframe

set_option maxHeartbeats 5000000 in
/-- If the second byte of the first pair is invalid after a valid high
nibble, the core decoder returns `InvalidHexCharacter` with index one. -/
theorem twp_decode_invalid_low_first
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (out inputPtr len sp : UInt32) (hi lo : UInt8)
    (oldMarker oldErrorIndex oldInputLen oldInputPtr oldErrorPtr : UInt32)
    (oldPair : UInt64) (oldTag oldPayload : UInt8)
    (oldOutCap oldOutPtr oldOutLen : UInt32)
    (heven : len &&& (1 : UInt32) = 0) (hlen : 2 ≤ len.toNat)
    (hiRoute : HexRoute) (hhiValid : hiRoute.valid hi)
    (hlo : hexValue lo = none)
    (hmarker : Offset32Facts (sp - 96) 32)
    (herrorIndexBase : Offset32Facts (sp - 96) 36)
    (hpairNoWrap : ((sp - 96) + 48).toNat =
      (sp - 96).toNat + (48 : UInt32).toNat)
    (hpair : Address64Facts ((sp - 96) + 48))
    (hinputLen : Offset32Facts (sp - 96) 44)
    (hinputPtr : Offset32Facts (sp - 96) 40)
    (herrorPtr : Offset32Facts (sp - 96) 56)
    (hiterLen : Offset32Facts ((sp - 96) + 40) 4)
    (hiterError : Offset32Facts ((sp - 96) + 40) 16)
    (hiterChunk : Offset32Facts ((sp - 96) + 40) 8)
    (hiterPtr : Offset32Facts ((sp - 96) + 40) 0)
    (hiterIndex : Offset32Facts ((sp - 96) + 40) 12)
    (herrorWord : Offset32Facts (32 + (sp - 96)) 0)
    (herrorIndex : Offset32Facts (32 + (sp - 96)) 4)
    (hinput0 : (inputPtr + 0).toNat = inputPtr.toNat)
    (hinput1 : (inputPtr + 1).toNat = inputPtr.toNat + 1)
    (htagAddr : Offset32Facts (sp - 96) 24)
    (houtCap : Offset32Facts out 0)
    (houtPtr : Offset32Facts out 4)
    (houtLen : Offset32Facts out 8)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u32 0 ((sp - 96) + 32) oldMarker ∗
      pointsTo_u32 0 ((sp - 96) + 36) oldErrorIndex ∗
      pointsTo_u64 0 ((sp - 96) + 48) oldPair ∗
      pointsTo_u32 0 ((sp - 96) + 44) oldInputLen ∗
      pointsTo_u32 0 ((sp - 96) + 40) oldInputPtr ∗
      pointsTo_u32 0 ((sp - 96) + 56) oldErrorPtr ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, (sp - 96) + 24⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, ((sp - 96) + 24) + 1⟩ (DFrac.own 1) (some oldPayload) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 0⟩ (DFrac.own 1) (some hi) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 1⟩ (DFrac.own 1) (some lo) ∗
      pointsTo_u32 0 out oldOutCap ∗
      pointsTo_u32 0 (out + 4) oldOutPtr ∗
      pointsTo_u32 0 (out + 8) oldOutLen -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u32 0 out 2147483648 ∗
      pointsTo_u32 0 (out + 4) (lo.toUInt32 &&& 255) ∗
      pointsTo_u32 0 (out + 8) 1 -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 len, .i32 inputPtr, .i32 out] ++ stack },
        [.call 8] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hmarker, HerrorIndex, Hpair, HinputLen,
    HinputPtr, HerrorPtr, Htag, Hpayload, Hhi, Hlo,
    HoutCap, HoutPtr, HoutLen⟩ Hcont
  simp only [List.singleton_append]
  iapply twp_call «module» 8 func5Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero, func5]
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localTee rfl
  iapply twp_globalSet $$ Hsp
  iintro Hframe
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [heven]
  simp
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldMarker hmarker.noWrap hmarker.one hmarker.two
      hmarker.three $$ Hmarker
  iintro Hmarker
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 (address := sp - 96) (offset := 48) (value := 2)
      oldPair hpairNoWrap hpair.one hpair.two hpair.three hpair.four
      hpair.five hpair.six hpair.seven $$ Hpair
  iintro Hpair
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldInputLen hinputLen.noWrap hinputLen.one
      hinputLen.two hinputLen.three $$ HinputLen
  iintro HinputLen
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldInputPtr hinputPtr.noWrap hinputPtr.one
      hinputPtr.two hinputPtr.three $$ HinputPtr
  iintro HinputPtr
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_store32 oldErrorPtr herrorPtr.noWrap herrorPtr.one
      herrorPtr.two herrorPtr.three $$ HerrorPtr
  iintro HerrorPtr
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  ihave HpairWords := pointsTo_u64_two_as_u32 ((sp - 96) + 48) |>.mp $$ Hpair
  icases HpairWords with ⟨HchunkRaw, HindexRaw⟩
  have hlenEq : (sp - 96) + 44 = ((sp - 96) + 40) + 4 := by bv_decide
  have hchunkEq : (sp - 96) + 48 = ((sp - 96) + 40) + 8 := by bv_decide
  have hindexEq : ((sp - 96) + 48) + 4 = ((sp - 96) + 40) + 12 := by bv_decide
  have herrorPtrEq : (sp - 96) + 56 = ((sp - 96) + 40) + 16 := by bv_decide
  have herrorWordEq : (sp - 96) + 32 = (32 + (sp - 96)) + 0 := by bv_decide
  have herrorIndexEq : (sp - 96) + 36 = (32 + (sp - 96)) + 4 := by bv_decide
  ihave HlenIter : pointsTo_u32 0 (((sp - 96) + 40) + 4) len $$ [HinputLen]
  · rw [← hlenEq]; iexact HinputLen
  ihave Hchunk : pointsTo_u32 0 (((sp - 96) + 40) + 8) 2 $$ [HchunkRaw]
  · rw [← hchunkEq]; iexact HchunkRaw
  ihave Hindex : pointsTo_u32 0 (((sp - 96) + 40) + 12) 0 $$ [HindexRaw]
  · rw [← hindexEq]; iexact HindexRaw
  ihave HerrorPtrIter : pointsTo_u32 0 (((sp - 96) + 40) + 16)
      (32 + (sp - 96)) $$ [HerrorPtr]
  · rw [← herrorPtrEq]; iexact HerrorPtr
  ihave HerrorWord : pointsTo_u32 0 ((32 + (sp - 96)) + 0) 1114114 $$ [Hmarker]
  · rw [← herrorWordEq]; iexact Hmarker
  ihave HerrorIndexIter : pointsTo_u32 0 ((32 + (sp - 96)) + 4)
      oldErrorIndex $$ [HerrorIndex]
  · rw [← herrorIndexEq]; iexact HerrorIndex
  ihave HhiAddr : pointsTo (GF := WasmHeapGF Universal.State)
      (H := WasmHeapMap) ⟨0, inputPtr⟩ (DFrac.own 1) (some hi) $$ [Hhi]
  · rw [← UInt32.add_zero inputPtr]
    iexact Hhi
  rw [show 40 + (sp - 96) = (sp - 96) + 40 by bv_decide,
    show 24 + (sp - 96) = (sp - 96) + 24 by bv_decide]
  obtain ⟨hloUpper, hloLower, hloDigit⟩ := hexValue_none_tests lo hlo
  iapply twp_decodePair_invalid_low
      (out := (sp - 96) + 24) (iterator := (sp - 96) + 40)
      (inputPtr := inputPtr) (errorPtr := 32 + (sp - 96))
      (len := len) (chunkIndex := 0) hi lo oldTag oldPayload
      1114114 oldErrorIndex hlen hiterLen hiterError hiterChunk hiterPtr
      hiterIndex herrorWord herrorIndex hinput0 hinput1 htagAddr.one
      hiRoute hhiValid hloUpper hloLower hloDigit
      (callerParams := [.i32 out, .i32 inputPtr, .i32 len])
      (callerLocalValues := [.i32 (sp - 96), .i32 1, .i32 0])
      (stack := []) $$ [$Hruntime $HlenIter $HerrorPtrIter $Hchunk
        $HinputPtr $Hindex $HerrorWord $HerrorIndexIter $HhiAddr $Hlo
        $Hpayload $Htag]
  iintro ⟨Hruntime, HlenIter, HerrorPtrIter, Hchunk, HinputPtr,
    Hindex, HerrorWord, HerrorIndex, Hhi, Hlo, Hpayload, Htag⟩
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load8U 0 htagAddr.noWrap $$ Htag
  iintro Htag
  iapply twp_eqz rfl
  iapply twp_brIf (by decide) rfl
  iapply twp_block
  iapply twp_localGet rfl
  ihave Hmarker : pointsTo_u32 0 ((sp - 96) + 32)
      (lo.toUInt32 &&& 255) $$ [HerrorWord]
  · rw [herrorWordEq]; iexact HerrorWord
  iapply twp_load32 (lo.toUInt32 &&& 255) hmarker.noWrap hmarker.one
      hmarker.two hmarker.three $$ Hmarker
  iintro Hmarker
  iapply twp_localTee rfl
  iapply twp_const
  have hnotMarker : lo.toUInt32 &&& 255 ≠ 1114114 := by bv_decide
  iapply hdtwp_eq (result := 0) (by simp [hnotMarker])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HerrorIndexBase : pointsTo_u32 0 ((sp - 96) + 36) 1 $$ [HerrorIndex]
  · rw [herrorIndexEq]
    rw [show ((((0 : UInt32) <<< (1 : UInt32)) ||| 1) &&& 255) |||
        (((0 : UInt32) <<< (1 : UInt32)) &&& 4294967040) = 1 by bv_decide]
    iexact HerrorIndex
  iapply twp_load32 1 herrorIndexBase.noWrap herrorIndexBase.one
      herrorIndexBase.two herrorIndexBase.three $$ HerrorIndexBase
  iintro HerrorIndexBase
  iapply twp_store32 oldOutLen houtLen.noWrap houtLen.one houtLen.two
      houtLen.three $$ HoutLen
  iintro HoutLen
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldOutPtr houtPtr.noWrap houtPtr.one houtPtr.two
      houtPtr.three $$ HoutPtr
  iintro HoutPtr
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32_addr (address := out) (value := 2147483648) oldOutCap
      (by simpa using houtCap.one) (by simpa using houtCap.two)
      (by simpa using houtCap.three) $$ HoutCap
  iintro HoutCap
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  have hrestore : 96 + (sp - 96) = sp := by bv_decide
  rw [hrestore]
  iapply twp_globalSet $$ Hframe
  iintro Hsp
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  iapply Hcont
  iframe


end Project.HexDecodeStdio
