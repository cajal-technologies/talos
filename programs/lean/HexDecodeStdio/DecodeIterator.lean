import HexDecodeStdio.DecodeSpec
import CodeLib.SepLogic.SmallStepTotalLiftingBytes

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

structure Offset32Facts (base offset : UInt32) : Prop where
  noWrap : (base + offset).toNat = base.toNat + offset.toNat
  one : ((base + offset) + 1).toNat = (base + offset).toNat + 1
  two : ((base + offset) + 2).toNat = (base + offset).toNat + 2
  three : ((base + offset) + 3).toNat = (base + offset).toNat + 3

inductive HexRoute where
  | upper
  | lower
  | decimal
deriving DecidableEq

def HexRoute.valid (route : HexRoute) (byte : UInt8) : Prop :=
  let upper := ((4294967231 + byte.toUInt32) &&& 255) < 6
  let lower := ((4294967199 + byte.toUInt32) &&& 255) < 6
  let decimal := ((4294967248 + byte.toUInt32) &&& 255) < 10
  match route with
  | .upper => upper
  | .lower => ¬ upper ∧ lower
  | .decimal => ¬ upper ∧ ¬ lower ∧ decimal

def HexRoute.nibble (route : HexRoute) (byte : UInt8) : UInt32 :=
  match route with
  | .upper => 4294967241 + byte.toUInt32
  | .lower => 4294967209 + byte.toUInt32
  | .decimal => 4294967248 + byte.toUInt32

private def pairLocals (out iterator : UInt32) : Locals :=
  ⟨[.i32 out, .i32 iterator],
    [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩

/-- Empty-input leg of the two-byte iterator.  It returns `none` (tag byte
zero) without inspecting an input byte. -/
theorem twp_decodePair_empty
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (out iterator : UInt32) (oldTag oldPayload : UInt8)
    (hiter : (iterator + 4).toNat = iterator.toNat + 4)
    (hiter1 : ((iterator + 4) + 1).toNat = (iterator + 4).toNat + 1)
    (hiter2 : ((iterator + 4) + 2).toNat = (iterator + 4).toNat + 2)
    (hiter3 : ((iterator + 4) + 3).toNat = (iterator + 4).toNat + 3)
    (hout1 : (out + 1).toNat = out.toNat + 1)
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 (iterator + 4) 0 ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out + 1⟩ (DFrac.own 1) (some oldPayload) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some oldTag) -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 (iterator + 4) 0 ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out + 1⟩ (DFrac.own 1) (some (0 : UInt8)) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some (0 : UInt8)) -∗
      WP (.running
        ⟨⟨callerParams, callerLocalValues, stack⟩, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨callerParams, callerLocalValues, .i32 iterator :: .i32 out :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hlen, Hpayload, Htag⟩ Hcont
  iapply twp_call «module» 3 func0Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime'
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero, func0]
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 0 hiter hiter1 hiter2 hiter3 $$ Hlen
  iintro Hlen'
  iapply twp_localTee rfl
  iapply twp_brIfZero
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_br rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store8 oldPayload hout1 $$ Hpayload
  iintro Hpayload'
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  simp [Locals.set?, Locals.set]
  iapply twp_store8_addr (address := out) (value := 0) oldTag $$ Htag
  iintro Htag'
  iapply twp_returnFromCallFallthrough
    (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime'
  iintro Hruntime''
  simp only [func0Def, List.take_zero, List.nil_append,
    List.drop_succ_cons, List.drop_zero]
  iapply Hcont
  simp
  iframe

/-- Successful leg of the generated two-byte iterator for every accepted
uppercase, lowercase, or decimal pair. -/
theorem twp_decodePair_valid
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (out iterator inputPtr errorPtr len chunkIndex : UInt32)
    (hi lo : UInt8) (oldTag oldPayload : UInt8)
    (hlen : 2 ≤ len.toNat)
    (hlenAddr : Offset32Facts iterator 4)
    (herrorAddr : Offset32Facts iterator 16)
    (hchunkAddr : Offset32Facts iterator 8)
    (hptrAddr : Offset32Facts iterator 0)
    (hindexAddr : Offset32Facts iterator 12)
    (hinput0 : (inputPtr + 0).toNat = inputPtr.toNat)
    (hinput1 : (inputPtr + 1).toNat = inputPtr.toNat + 1)
    (hout1 : (out + 1).toNat = out.toNat + 1)
    (hiRoute loRoute : HexRoute)
    (hhiValid : hiRoute.valid hi) (hloValid : loRoute.valid lo)
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 (iterator + 4) len ∗
      pointsTo_u32 0 (iterator + 16) errorPtr ∗
      pointsTo_u32 0 (iterator + 8) 2 ∗
      pointsTo_u32 0 iterator inputPtr ∗
      pointsTo_u32 0 (iterator + 12) chunkIndex ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 0⟩ (DFrac.own 1) (some hi) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 1⟩ (DFrac.own 1) (some lo) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out + 1⟩ (DFrac.own 1) (some oldPayload) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some oldTag) -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 (iterator + 4) (len - 2) ∗
      pointsTo_u32 0 (iterator + 16) errorPtr ∗
      pointsTo_u32 0 (iterator + 8) 2 ∗
      pointsTo_u32 0 iterator (2 + inputPtr) ∗
      pointsTo_u32 0 (iterator + 12) (1 + chunkIndex) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 0⟩ (DFrac.own 1) (some hi) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 1⟩ (DFrac.own 1) (some lo) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out + 1⟩ (DFrac.own 1)
          (some ((loRoute.nibble lo |||
            (hiRoute.nibble hi <<< (4 : UInt32))).toUInt8)) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some (1 : UInt8)) -∗
      WP (.running
        ⟨⟨callerParams, callerLocalValues, stack⟩, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨callerParams, callerLocalValues, .i32 iterator :: .i32 out :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hlen, Herror, Hchunk, Hptr, Hindex,
    Hhi, Hlo, Hpayload, Htag⟩ Hcont
  iapply twp_call «module» 3 func0Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime'
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero, func0]
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 len hlenAddr.noWrap hlenAddr.one hlenAddr.two
      hlenAddr.three $$ Hlen
  iintro Hlen
  iapply twp_localTee rfl
  have hlen0 : len ≠ 0 := by
    intro hz
    subst len
    simp at hlen
  iapply twp_brIf hlen0 rfl
  iapply twp_localGet rfl
  iapply twp_load32 errorPtr herrorAddr.noWrap herrorAddr.one herrorAddr.two
      herrorAddr.three $$ Herror
  iintro Herror
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 2 hchunkAddr.noWrap hchunkAddr.one hchunkAddr.two
      hchunkAddr.three $$ Hchunk
  iintro Hchunk
  iapply twp_localTee rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU rfl
  iapply twp_select (selected := .i32 2) (by
    by_cases h : (2 : UInt32) < len
    · simp [h]
    · have htwo : (2 : UInt32).toNat = 2 := by decide
      have hnlt : ¬2 < len.toNat := by
        rw [UInt32.lt_iff_toNat_lt, htwo] at h
        exact h
      have heq : len = (2 : UInt32) := by
        apply UInt32.toNat_inj.mp
        omega
      simp [h, heq])
  iapply twp_localTee rfl
  iapply twp_sub
  iapply twp_store32 len hlenAddr.noWrap hlenAddr.one hlenAddr.two
      hlenAddr.three $$ Hlen
  iintro Hlen'
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32_addr inputPtr
      (by simpa using hptrAddr.one) (by simpa using hptrAddr.two)
      (by simpa using hptrAddr.three) $$ Hptr
  iintro Hptr
  iapply twp_localTee rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_store32_addr inputPtr
      (by simpa using hptrAddr.one) (by simpa using hptrAddr.two)
      (by simpa using hptrAddr.three) $$ Hptr
  iintro Hptr'
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  simp
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  simp
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_load32 chunkIndex hindexAddr.noWrap hindexAddr.one
      hindexAddr.two hindexAddr.three $$ Hindex
  iintro Hindex
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load8U_addr hi $$ Hhi
  iintro Hhi
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_add
  iapply twp_const
  iapply twp_and
  iapply twp_const
  iapply twp_ltU rfl
  cases hiRoute <;> simp only [HexRoute.valid] at hhiValid <;>
    first
    | (rcases hhiValid with ⟨hhiUpper, hhiLower, hhiDigit⟩
       simp [hhiUpper]
       iapply twp_brIfZero
       iapply twp_block
       iapply twp_localGet rfl
       iapply twp_const
       iapply twp_add
       iapply twp_const
       iapply twp_and
       iapply twp_const
       iapply twp_ltU rfl
       simp [hhiLower]
       iapply twp_brIfZero
       iapply twp_localGet rfl
       iapply twp_localSet rfl
       iapply twp_localGet rfl
       iapply twp_const
       iapply twp_add
       iapply twp_localTee rfl
       iapply twp_const
       iapply twp_and
       iapply twp_const
       iapply twp_ltU rfl
       simp [hhiDigit]
       iapply twp_brIf (by decide) rfl
       simp)
    | (rcases hhiValid with ⟨hhiUpper, hhiLower⟩
       simp [hhiUpper]
       iapply twp_brIfZero
       iapply twp_block
       iapply twp_localGet rfl
       iapply twp_const
       iapply twp_add
       iapply twp_const
       iapply twp_and
       iapply twp_const
       iapply twp_ltU rfl
       simp [hhiLower]
       iapply twp_brIf (by decide) rfl
       simp
       iapply twp_localGet rfl
       iapply twp_const
       iapply twp_add
       iapply twp_localSet rfl
       iapply twp_br rfl)
    | (simp [hhiValid]
       iapply twp_brIf (by decide) rfl
       simp
       iapply twp_localGet rfl
       iapply twp_const
       iapply twp_add
       iapply twp_localSet rfl
       iapply twp_exitControl rfl
       simp)
  all_goals
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_eq rfl
    simp
    iapply twp_brIfZero
    iapply twp_localGet rfl
    iapply twp_load8U lo hinput1 $$ Hlo
    iintro Hlo
    iapply twp_localTee rfl
    iapply twp_const
    iapply twp_add
    iapply twp_const
    iapply twp_and
    iapply twp_const
    iapply twp_ltU rfl
    cases loRoute <;> simp only [HexRoute.valid] at hloValid <;>
      first
      | (rcases hloValid with ⟨hloUpper, hloLower, hloDigit⟩
         simp [hloUpper]
         iapply twp_brIfZero
         iapply twp_localGet rfl
         iapply twp_const
         iapply twp_add
         iapply twp_const
         iapply twp_and
         iapply twp_const
         iapply twp_ltU rfl
         simp [hloLower]
         iapply twp_brIfZero
         iapply twp_localGet rfl
         iapply twp_const
         iapply twp_add
         iapply twp_localTee rfl
         iapply twp_const
         iapply twp_and
         iapply twp_const
         iapply twp_ltU rfl
         simp [hloDigit]
         iapply twp_brIf (by decide) rfl
         simp)
      | (rcases hloValid with ⟨hloUpper, hloLower⟩
         simp [hloUpper]
         iapply twp_brIfZero
         iapply twp_localGet rfl
         iapply twp_const
         iapply twp_add
         iapply twp_const
         iapply twp_and
         iapply twp_const
         iapply twp_ltU rfl
         simp [hloLower]
         iapply twp_brIf (by decide) rfl
         simp
         iapply twp_localGet rfl
         iapply twp_const
         iapply twp_add
         iapply twp_localSet rfl
         iapply twp_br rfl)
      | (simp [hloValid]
         iapply twp_brIf (by decide) rfl
         simp
         iapply twp_localGet rfl
         iapply twp_const
         iapply twp_add
         iapply twp_localSet rfl
         iapply twp_br rfl)
    all_goals
      iapply twp_localGet rfl
      iapply twp_localGet rfl
      iapply twp_const
      iapply twp_shl
      iapply twp_or
      iapply twp_localSet rfl
      iapply twp_const
      iapply twp_localSet rfl
      iapply twp_exitControl rfl
      simp
      iapply twp_localGet rfl
      iapply twp_localGet rfl
      iapply twp_const
      iapply twp_add
      iapply twp_store32 chunkIndex hindexAddr.noWrap hindexAddr.one
          hindexAddr.two hindexAddr.three $$ Hindex
      iintro Hindex'
      iapply twp_exitControl rfl
      simp
      iapply twp_localGet rfl
      iapply twp_localGet rfl
      iapply twp_store8 oldPayload hout1 $$ Hpayload
      iintro Hpayload'
      iapply twp_localGet rfl
      iapply twp_localGet rfl
      iapply twp_const
      iapply twp_and
      simp
      iapply twp_store8_addr (address := out) (value := 1) oldTag $$ Htag
      iintro Htag'
      iapply twp_returnFromCallFallthrough
          (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime'
      iintro Hruntime''
      simp
      simp [HexRoute.nibble]
      iapply Hcont
      iframe

end Project.HexDecodeStdio
