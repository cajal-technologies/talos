import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.TotalLifting
import HexDecodeStdio.DecodeIterator

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

structure Address64Facts (address : UInt32) : Prop where
  one : (address + 1).toNat = address.toNat + 1
  two : (address + 2).toNat = address.toNat + 2
  three : (address + 3).toNat = address.toNat + 3
  four : (address + 4).toNat = address.toNat + 4
  five : (address + 5).toNat = address.toNat + 5
  six : (address + 6).toNat = address.toNat + 6
  seven : (address + 7).toNat = address.toNat + 7

theorem address64Facts (address : UInt32)
    (hroom : address.toNat + 8 ≤ UInt32.size) : Address64Facts address := by
  have hroom' : address.toNat + 8 ≤ 4294967296 := by
    simpa only [UInt32.size] using hroom
  constructor
  · simpa using UInt32.add_ofNat_toNat_noWrap address 1 (by decide) (by omega)
  · simpa using UInt32.add_ofNat_toNat_noWrap address 2 (by decide) (by omega)
  · simpa using UInt32.add_ofNat_toNat_noWrap address 3 (by decide) (by omega)
  · simpa using UInt32.add_ofNat_toNat_noWrap address 4 (by decide) (by omega)
  · simpa using UInt32.add_ofNat_toNat_noWrap address 5 (by decide) (by omega)
  · simpa using UInt32.add_ofNat_toNat_noWrap address 6 (by decide) (by omega)
  · simpa using UInt32.add_ofNat_toNat_noWrap address 7 (by decide) (by omega)

theorem pointsTo_u64_two_as_u32 [WasmSmallStepGS hlc Universal.State]
    (address : UInt32) :
    pointsTo_u64 (α := Universal.State) 0 address 2 ⊣⊢
      pointsTo_u32 0 address 2 ∗ pointsTo_u32 0 (address + 4) 0 := by
  simp only [pointsTo_u64, pointsTo_u32, u64Byte, u32Byte]
  rw [show address + 4 + 1 = address + 5 by bv_decide,
    show address + 4 + 2 = address + 6 by bv_decide,
    show address + 4 + 3 = address + 7 by bv_decide]
  have e1 : (((2 : UInt64) >>> 8).toUInt8) =
      (((2 : UInt32) >>> 8).toUInt8) := by decide
  have e2 : (((2 : UInt64) >>> 16).toUInt8) =
      (((2 : UInt32) >>> 16).toUInt8) := by decide
  have e3 : (((2 : UInt64) >>> 24).toUInt8) =
      (((2 : UInt32) >>> 24).toUInt8) := by decide
  have e4 : (((2 : UInt64) >>> 32).toUInt8) = 0 := by decide
  have e5 : (((2 : UInt64) >>> 40).toUInt8) = 0 := by decide
  have e6 : (((2 : UInt64) >>> 48).toUInt8) = 0 := by decide
  have e7 : (((2 : UInt64) >>> 56).toUInt8) = 0 := by decide
  rw [e1, e2, e3, e4, e5, e6, e7]
  norm_num
  constructor
  · iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
    isplitl [H0 H1 H2 H3]
    · isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      isplitl [H2] <;> iassumption
    isplitl [H4]
    · iexact H4
    isplitl [H5]
    · iexact H5
    isplitl [H6] <;> iassumption
  · iintro ⟨⟨H0, H1, H2, H3⟩, H4, H5, H6, H7⟩
    isplitl [H0]
    · iexact H0
    isplitl [H1]
    · iexact H1
    isplitl [H2]
    · iexact H2
    isplitl [H3]
    · iexact H3
    isplitl [H4]
    · iexact H4
    isplitl [H5]
    · iexact H5
    isplitl [H6] <;> iassumption

set_option maxHeartbeats 2000000 in
/-- Odd input lengths take the generated decoder's early error return and do
not inspect or allocate an input/output byte. -/
theorem twp_decode_odd
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (out inputPtr len sp : UInt32) (oldResult : UInt64)
    (hodd : len &&& (1 : UInt32) ≠ 0)
    (hsp : 96 ≤ sp.toNat)
    (hout : out.toNat + 8 ≤ UInt32.size)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 out oldResult -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 out 4785076751564800 -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 len, .i32 inputPtr, .i32 out] ++ stack },
        [.call 8] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hout⟩ Hcont
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
  iapply twp_brIf hodd rfl
  simp
  iapply twp_localGet rfl
  iapply twp_constI64
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := address64Facts out hout
  iapply twp_store64_addr (address := out)
      (value := 4785076751564800) oldResult
      h1 h2 h3 h4 h5 h6 h7 $$ Hout
  iintro Hout
  iapply twp_exitControl rfl
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

set_option maxHeartbeats 4000000 in
/-- The generated core decoder returns the empty successful vector on an
empty input.  This is the non-allocating base case of its pair loop. -/
theorem twp_decode_empty
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (out inputPtr sp : UInt32)
    (oldMarker oldInputLen oldInputPtr oldErrorPtr : UInt32)
    (oldPair : UInt64) (oldTag oldPayload : UInt8)
    (oldOutCap oldOutPtr oldOutLen : UInt32)
    (hmarker : Offset32Facts (sp - 96) 32)
    (hpairNoWrap : ((sp - 96) + 48).toNat =
      (sp - 96).toNat + (48 : UInt32).toNat)
    (hpair : Address64Facts ((sp - 96) + 48))
    (hinputLen : Offset32Facts (sp - 96) 44)
    (hinputPtr : Offset32Facts (sp - 96) 40)
    (herrorPtr : Offset32Facts (sp - 96) 56)
    (hiterLen : Offset32Facts ((sp - 96) + 40) 4)
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
      pointsTo_u64 0 ((sp - 96) + 48) oldPair ∗
      pointsTo_u32 0 ((sp - 96) + 44) oldInputLen ∗
      pointsTo_u32 0 ((sp - 96) + 40) oldInputPtr ∗
      pointsTo_u32 0 ((sp - 96) + 56) oldErrorPtr ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, (sp - 96) + 24⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, ((sp - 96) + 24) + 1⟩ (DFrac.own 1) (some oldPayload) ∗
      pointsTo_u32 0 out oldOutCap ∗
      pointsTo_u32 0 (out + 4) oldOutPtr ∗
      pointsTo_u32 0 (out + 8) oldOutLen -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u32 0 out 0 ∗
      pointsTo_u32 0 (out + 4) 1 ∗
      pointsTo_u32 0 (out + 8) 0 -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 0, .i32 inputPtr, .i32 out] ++ stack },
        [.call 8] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hmarker, Hpair, HinputLen, HinputPtr,
    HerrorPtr, Htag, Hpayload, HoutCap, HoutPtr, HoutLen⟩ Hcont
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
  have hlenEq : (sp - 96) + 44 = ((sp - 96) + 40) + 4 := by bv_decide
  ihave HinputLenIter :
      pointsTo_u32 0 (((sp - 96) + 40) + 4) 0 $$ [HinputLen]
  · rw [← hlenEq]
    iexact HinputLen
  rw [show 40 + (sp - 96) = (sp - 96) + 40 by bv_decide,
    show 24 + (sp - 96) = (sp - 96) + 24 by bv_decide]
  iapply twp_decodePair_empty
      (out := (sp - 96) + 24) (iterator := (sp - 96) + 40)
      oldTag oldPayload hiterLen.noWrap hiterLen.one hiterLen.two
      hiterLen.three htagAddr.one
      (callerParams := [.i32 out, .i32 inputPtr, .i32 0])
      (callerLocalValues := [.i32 (sp - 96), .i32 1, .i32 0])
      (stack := []) $$ [$Hruntime $HinputLenIter $Hpayload $Htag]
  iintro ⟨Hruntime, HinputLen, Hpayload, Htag⟩
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
  iapply twp_load32 1114114 hmarker.noWrap hmarker.one hmarker.two
      hmarker.three $$ Hmarker
  iintro Hmarker
  iapply twp_localTee rfl
  iapply twp_const
  iapply hdtwp_eq rfl
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldOutLen houtLen.noWrap houtLen.one houtLen.two
      houtLen.three $$ HoutLen
  iintro HoutLen
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldOutPtr houtPtr.noWrap houtPtr.one houtPtr.two
      houtPtr.three $$ HoutPtr
  iintro HoutPtr
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32_addr (address := out) (value := 0) oldOutCap
      (by simpa using houtCap.one) (by simpa using houtCap.two)
      (by simpa using houtCap.three) $$ HoutCap
  iintro HoutCap
  iapply twp_br rfl
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
