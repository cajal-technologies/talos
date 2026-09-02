import HexDecodeStdio.DecodeIteratorInvalid

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

/-- Invalid-low-byte leg of the generated two-byte iterator after a valid high nibble. -/
theorem twp_decodePair_invalid_low
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (out iterator inputPtr errorPtr len chunkIndex : UInt32)
    (hi lo : UInt8) (oldTag oldPayload : UInt8)
    (oldErrorWord oldErrorIndex : UInt32)
    (hlen : 2 ≤ len.toNat)
    (hlenAddr : Offset32Facts iterator 4)
    (herrorAddr : Offset32Facts iterator 16)
    (hchunkAddr : Offset32Facts iterator 8)
    (hptrAddr : Offset32Facts iterator 0)
    (hindexAddr : Offset32Facts iterator 12)
    (herrorWordAddr : Offset32Facts errorPtr 0)
    (herrorIndexAddr : Offset32Facts errorPtr 4)
    (hinput0 : (inputPtr + 0).toNat = inputPtr.toNat)
    (hinput1 : (inputPtr + 1).toNat = inputPtr.toNat + 1)
    (hout1 : (out + 1).toNat = out.toNat + 1)
    (hiRoute : HexRoute) (hhiValid : hiRoute.valid hi)
    (hloUpper : ¬ (((4294967231 + lo.toUInt32) &&& 255) < 6))
    (hloLower : ¬ (((4294967199 + lo.toUInt32) &&& 255) < 6))
    (hloDigit : ¬ (((4294967248 + lo.toUInt32) &&& 255) < 10))
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 (iterator + 4) len ∗
      pointsTo_u32 0 (iterator + 16) errorPtr ∗
      pointsTo_u32 0 (iterator + 8) 2 ∗
      pointsTo_u32 0 iterator inputPtr ∗
      pointsTo_u32 0 (iterator + 12) chunkIndex ∗
      pointsTo_u32 0 (errorPtr + 0) oldErrorWord ∗
      pointsTo_u32 0 (errorPtr + 4) oldErrorIndex ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr⟩ (DFrac.own 1) (some hi) ∗
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
      pointsTo_u32 0 (errorPtr + 0) (lo.toUInt32 &&& 255) ∗
      pointsTo_u32 0 (errorPtr + 4)
        ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
          ((chunkIndex <<< (1 : UInt32)) &&& 4294967040)) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr⟩ (DFrac.own 1) (some hi) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, inputPtr + 1⟩ (DFrac.own 1) (some lo) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out + 1⟩ (DFrac.own 1) (some lo) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some (0 : UInt8)) -∗
      WP (.running
        ⟨⟨callerParams, callerLocalValues, stack⟩, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨callerParams, callerLocalValues, .i32 iterator :: .i32 out :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hlen, Herror, Hchunk, Hptr, Hindex,
    HerrorWord, HerrorIndex, Hhi, Hlo, Hpayload, Htag⟩ Hcont
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
    iapply twp_brIfZero
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_or
    iapply twp_localSet rfl
    iapply twp_exitControl rfl
    simp
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_and
    iapply twp_store32_addr (address := errorPtr) oldErrorWord
        (by simpa using herrorWordAddr.one) (by simpa using herrorWordAddr.two)
        (by simpa using herrorWordAddr.three) $$ HerrorWord
    iintro HerrorWord'
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_and
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_and
    iapply twp_or
    iapply twp_store32 oldErrorIndex herrorIndexAddr.noWrap
        herrorIndexAddr.one herrorIndexAddr.two herrorIndexAddr.three $$ HerrorIndex
    iintro HerrorIndex'
    iapply twp_const
    iapply twp_localSet rfl
    iapply twp_br rfl
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
    iapply twp_store8_addr (address := out) (value := 0) oldTag $$ Htag
    iintro Htag'
    iapply twp_returnFromCallFallthrough
        (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime'
    iintro Hruntime''
    simp
    iapply Hcont
    iframe


end Project.HexDecodeStdio
