import HexDecodeStdio.ReadChunk

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

/-- The continuation of `read_to_end` after its first `read_chunk` call. -/
def readToEndAfterFirstRead : Program := func7.drop 21

theorem func7_first_read_split :
    func7 =
      [.globalGet 0, .const 32, .sub, .localTee 1, .globalSet 0,
        .localGet 1, .const 0, .store32 12,
        .localGet 1, .constI64 4294967296, .store64 4,
        .localGet 1, .const 16, .add,
        .localGet 1, .const 31, .add,
        .localGet 1, .const 4, .add, .call 4] ++
        readToEndAfterFirstRead := by
  rfl

/-- Empty-input leg of module function 10 (`read_to_end`). -/
theorem twp_read_to_end_empty
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (out sp : UInt32)
    (oldVec oldRead oldOutVec : UInt64) (oldLen oldOutLen : UInt32)
    (old8 old16 old24 old32 oldResult : UInt64)
    (hinput : host.stdio.input = [])
    (hframe4No : ((sp - 32) + 4).toNat = (sp - 32).toNat + 4)
    (hframe4 : Address64Facts ((sp - 32) + 4))
    (hframe12 : Offset32Facts (sp - 32) 12)
    (hframe16No : ((sp - 32) + 16).toNat = (sp - 32).toNat + 16)
    (hframe16 : Address64Facts ((sp - 32) + 16))
    (hout : Address64Facts out)
    (houtLen : Offset32Facts out 8)
    (h8no : ((((sp - 32) - 48) + 8).toNat =
      ((sp - 32) - 48).toNat + 8))
    (h16no : ((((sp - 32) - 48) + 16).toNat =
      ((sp - 32) - 48).toNat + 16))
    (h24no : ((((sp - 32) - 48) + 24).toNat =
      ((sp - 32) - 48).toNat + 24))
    (h32no : ((((sp - 32) - 48) + 32).toNat =
      ((sp - 32) - 48).toNat + 32))
    (h40no : ((((sp - 32) - 48) + 40).toNat =
      ((sp - 32) - 48).toNat + 40))
    (h44no : ((((sp - 32) - 48) + 44).toNat =
      ((sp - 32) - 48).toNat + 44))
    (h8 : Address64Facts (((sp - 32) - 48) + 8))
    (h16 : Address64Facts (((sp - 32) - 48) + 16))
    (h24 : Address64Facts (((sp - 32) - 48) + 24))
    (h32 : Address64Facts (((sp - 32) - 48) + 32))
    (h44 : Address64Facts (((sp - 32) - 48) + 44))
    (hreadCount : Offset32Facts (((sp - 32) - 48) + 40) 4)
    (hvecCapacity : Offset32Facts ((sp - 32) + 4) 0)
    (hvecLength : Offset32Facts ((sp - 32) + 4) 8)
    (hresultCount : Offset32Facts ((sp - 32) + 16) 4)
    (hbufferNowrap : ((((sp - 32) - 48) + 8).toNat + 32 <
      UInt32.size))
    (hrestore : 32 + (sp - 32) = sp)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 ((sp - 32) + 4) oldVec ∗
      pointsTo_u32 0 ((sp - 32) + 12) oldLen ∗
      pointsTo_u64 0 ((sp - 32) + 16) oldRead ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 8) old8 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 16) old16 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 24) old24 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 32) old32 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 40) oldResult ∗
      pointsTo_u64 0 out oldOutVec ∗
      pointsTo_u32 0 (out + 8) oldOutLen -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 ((sp - 32) + 4) 4294967296 ∗
      pointsTo_u32 0 ((sp - 32) + 12) 0 ∗
      pointsTo_u64 0 ((sp - 32) + 16) (ioWord oldRead 4 0) ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 8) 0 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 16) 0 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 24) 0 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 32) 0 ∗
      pointsTo_u64 0 (((sp - 32) - 48) + 40)
        (ioWord oldResult 4 0) ∗
      pointsTo_u64 0 out 4294967296 ∗
      pointsTo_u32 0 (out + 8) 0 -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 out] ++ stack },
        [.call 10] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hsp, Hvec, Hlen, Hread,
    H8, H16, H24, H32, Hresult, HoutVec, HoutLen⟩ Hcont
  simp only [List.singleton_append]
  iapply twp_call «module» 10 func7Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp only [func7Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  rw [func7_first_read_split]
  simp
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localTee rfl
  iapply twp_globalSet $$ Hsp
  iintro HframeSp
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldLen hframe12.noWrap hframe12.one
      hframe12.two hframe12.three $$ Hlen
  iintro Hlen
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 oldVec hframe4No hframe4.one hframe4.two
      hframe4.three hframe4.four hframe4.five hframe4.six
      hframe4.seven $$ Hvec
  iintro Hvec
  ihave HvecParts :=
    (pointsTo_u64_as_u32s ((sp - 32) + 4) 4294967296).mp $$ Hvec
  icases HvecParts with ⟨Hcapacity, Hdata⟩
  isimp only [show (4294967296 : UInt64).toUInt32 = 0 by decide,
    show ((4294967296 : UInt64) >>> 32).toUInt32 = 1 by decide]
    at Hcapacity Hdata
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show 16 + (sp - 32) = (sp - 32) + 16 by bv_decide,
    show 31 + (sp - 32) = (sp - 32) + 31 by bv_decide,
    show 4 + (sp - 32) = (sp - 32) + 4 by bv_decide]
  ihave HlenVec : pointsTo_u32 0 (((sp - 32) + 4) + 8) 0 $$ [Hlen]
  · rw [show ((sp - 32) + 4) + 8 = (sp - 32) + 12 by bv_decide]
    iexact Hlen
  simp [Locals.set?, Locals.set, ValueType.zero]
  iapply twp_read_chunk_eof (s := s) (E := E) (Φ := Φ)
      host ((sp - 32) + 16) ((sp - 32) + 31)
      ((sp - 32) + 4) (sp - 32) 0 0 old8 old16 old24 old32
      oldResult oldRead hinput h8no h16no h24no h32no h40no h44no
      h8 h16 h24 h32 h44 hreadCount hvecCapacity hvecLength
      hresultCount hbufferNowrap
      (callerParams := [.i32 out])
      (callerLocalValues :=
        [.i32 (sp - 32), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
          .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
          .i64 0])
      (code := readToEndAfterFirstRead) (arity := 0)
      (remainder := []) (controls := [])
      (calls :=
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ } :: calls) $$
      [$Hruntime $Henv $Hhost $HframeSp $H8 $H16 $H24 $H32
        $Hresult $Hcapacity $HlenVec $Hread]
  iintro ⟨Hruntime, Henv, Hhost, HframeSp, Hbuffer, Hresult,
    Hcapacity, Hlen, Hread⟩
  simp only [readToEndAfterFirstRead, func7, List.drop]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  ihave HreadParts :=
    (pointsTo_ioWord ((sp - 32) + 16) oldRead 4 0).mp $$ Hread
  icases HreadParts with ⟨Htag, Hpad1, Hpad2, Hpad3, Hcount⟩
  iapply twp_localGet rfl
  iapply twp_load8U (4 : UInt8) hframe16No $$ Htag
  iintro Htag
  iapply twp_const
  iapply twp_ne rfl
  simp
  iapply twp_brIfZero
  have hbase16 : ((sp - 32) + 16).toNat = (sp - 32).toNat + 16 := by
    exact hframe16No
  have h20no : ((sp - 32) + 20).toNat = (sp - 32).toNat + 20 := by
    rw [show (sp - 32) + 20 = ((sp - 32) + 16) + 4 by bv_decide,
      hresultCount.noWrap, hbase16]
    rw [show (4 : UInt32).toNat = 4 by decide]
  have h20one : (((sp - 32) + 20) + 1).toNat =
      ((sp - 32) + 20).toNat + 1 := by
    simpa only [show (sp - 32) + 20 = ((sp - 32) + 16) + 4 by
      bv_decide] using hresultCount.one
  have h20two : (((sp - 32) + 20) + 2).toNat =
      ((sp - 32) + 20).toNat + 2 := by
    simpa only [show (sp - 32) + 20 = ((sp - 32) + 16) + 4 by
      bv_decide] using hresultCount.two
  have h20three : (((sp - 32) + 20) + 3).toNat =
      ((sp - 32) + 20).toNat + 3 := by
    simpa only [show (sp - 32) + 20 = ((sp - 32) + 16) + 4 by
      bv_decide] using hresultCount.three
  ihave Hcount20 : pointsTo_u32 0 ((sp - 32) + 20) 0 $$ [Hcount]
  · rw [show (sp - 32) + 20 = ((sp - 32) + 16) + 4 by bv_decide]
    iexact Hcount
  iapply twp_localGet rfl
  iapply twp_load32 0 h20no h20one h20two h20three $$ Hcount20
  iintro Hcount20
  iapply twp_eqz rfl
  iapply twp_brIf (by decide) rfl
  simp
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hlen12 : pointsTo_u32 0 ((sp - 32) + 12) 0 $$ [Hlen]
  · rw [show (sp - 32) + 12 = ((sp - 32) + 4) + 8 by bv_decide]
    iexact Hlen
  iapply twp_load32 0 hframe12.noWrap hframe12.one hframe12.two
      hframe12.three $$ Hlen12
  iintro Hlen12
  iapply twp_store32 oldOutLen houtLen.noWrap houtLen.one houtLen.two
      houtLen.three $$ HoutLen
  iintro HoutLen
  ihave Hvec : pointsTo_u64 0 ((sp - 32) + 4) 4294967296 $$
      [Hcapacity Hdata]
  · iapply (pointsTo_u64_as_u32s ((sp - 32) + 4) 4294967296).mpr
    isimp only [show (4294967296 : UInt64).toUInt32 = 0 by decide,
      show ((4294967296 : UInt64) >>> 32).toUInt32 = 1 by decide]
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 4294967296 hframe4No hframe4.one hframe4.two
      hframe4.three hframe4.four hframe4.five hframe4.six
      hframe4.seven $$ Hvec
  iintro Hvec
  ihave HoutVec0 : pointsTo_u64 0 (out + 0) oldOutVec $$ [HoutVec]
  · rw [UInt32.add_zero]
    iexact HoutVec
  iapply twp_store64 oldOutVec (by simp) (by simpa using hout.one)
      (by simpa using hout.two) (by simpa using hout.three)
      (by simpa using hout.four) (by simpa using hout.five)
      (by simpa using hout.six) (by simpa using hout.seven) $$ HoutVec0
  iintro HoutVec
  isimp only [UInt32.add_zero] at HoutVec
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [hrestore]
  iapply twp_globalSet $$ HframeSp
  iintro Hsp
  iapply twp_returnFromCallFallthrough $$ Hruntime
  iintro Hruntime
  simp
  ihave Hread : pointsTo_u64 0 ((sp - 32) + 16) (ioWord oldRead 4 0) $$
      [Htag Hpad1 Hpad2 Hpad3 Hcount20]
  · iapply (pointsTo_ioWord ((sp - 32) + 16) oldRead 4 0).mpr
    rw [show ((sp - 32) + 16) + 4 = (sp - 32) + 20 by bv_decide]
    iframe
  ihave HbufferRep : pointsToBytes 0 (((sp - 32) - 48) + 8)
      (List.replicate 32 (0 : UInt8)) $$ [Hbuffer]
  · isimp only [List.replicate_succ, List.replicate_zero]
    iexact Hbuffer
  ihave HbufferParts :=
    (four_u64_zero_as_bytes (((sp - 32) - 48) + 8)).mpr $$ HbufferRep
  icases HbufferParts with ⟨H8, H16, H24, H32⟩
  isimp only [show (((sp - 32) - 48) + 8) + 8 =
      ((sp - 32) - 48) + 16 by bv_decide] at H16
  isimp only [show (((sp - 32) - 48) + 8) + 16 =
      ((sp - 32) - 48) + 24 by bv_decide] at H24
  isimp only [show (((sp - 32) - 48) + 8) + 24 =
      ((sp - 32) - 48) + 32 by bv_decide] at H32
  iapply Hcont
  iframe

end Project.HexDecodeStdio
