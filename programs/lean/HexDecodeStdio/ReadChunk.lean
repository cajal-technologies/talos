import HexDecodeStdio.MemoryLayout
import HexDecodeStdio.HostIO

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

/-- EOF leg of module function 4.  The universal host returns a successful
zero-byte read; the function consequently neither allocates nor copies. -/
theorem twp_read_chunk_eof
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (out ignored vector sp : UInt32)
    (capacity length : UInt32)
    (old8 old16 old24 old32 oldResult oldOut : UInt64)
    (hinput : host.stdio.input = [])
    (h8no : ((sp - 48) + 8).toNat = (sp - 48).toNat + 8)
    (h16no : ((sp - 48) + 16).toNat = (sp - 48).toNat + 16)
    (h24no : ((sp - 48) + 24).toNat = (sp - 48).toNat + 24)
    (h32no : ((sp - 48) + 32).toNat = (sp - 48).toNat + 32)
    (h40no : ((sp - 48) + 40).toNat = (sp - 48).toNat + 40)
    (h44no : ((sp - 48) + 44).toNat = (sp - 48).toNat + 44)
    (h8 : Address64Facts ((sp - 48) + 8))
    (h16 : Address64Facts ((sp - 48) + 16))
    (h24 : Address64Facts ((sp - 48) + 24))
    (h32 : Address64Facts ((sp - 48) + 32))
    (h44 : Address64Facts ((sp - 48) + 44))
    (hreadCount : Offset32Facts ((sp - 48) + 40) 4)
    (hvecCapacity : Offset32Facts vector 0)
    (hvecLength : Offset32Facts vector 8)
    (houtCount : Offset32Facts out 4)
    (hbufferNowrap : (((sp - 48) + 8).toNat + 32 < UInt32.size))
    (callerParams callerLocalValues : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 ((sp - 48) + 8) old8 ∗
      pointsTo_u64 0 ((sp - 48) + 16) old16 ∗
      pointsTo_u64 0 ((sp - 48) + 24) old24 ∗
      pointsTo_u64 0 ((sp - 48) + 32) old32 ∗
      pointsTo_u64 0 ((sp - 48) + 40) oldResult ∗
      pointsTo_u32 0 vector capacity ∗
      pointsTo_u32 0 (vector + 8) length ∗
      pointsTo_u64 0 out oldOut -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsToBytes 0 ((sp - 48) + 8) (List.replicate 32 0) ∗
      pointsTo_u64 0 ((sp - 48) + 40) (ioWord oldResult 4 0) ∗
      pointsTo_u32 0 vector capacity ∗
      pointsTo_u32 0 (vector + 8) length ∗
      pointsTo_u64 0 out (ioWord oldOut 4 0) -∗
      WP (.running
        ⟨⟨callerParams, callerLocalValues, []⟩, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨callerParams, callerLocalValues,
          [.i32 vector, .i32 ignored, .i32 out]⟩,
        .call 4 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hsp, H8, H16, H24, H32, Hresult,
    Hcapacity, Hlength, Hout⟩ Hcont
  iapply twp_call «module» 4 func1Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams,
    ValueType.zero, func1]
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localTee rfl
  iapply twp_globalSet $$ Hsp
  iintro HframeSp
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old32 h32no h32.one h32.two h32.three h32.four
      h32.five h32.six h32.seven $$ H32
  iintro H32
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old24 h24no h24.one h24.two h24.three h24.four
      h24.five h24.six h24.seven $$ H24
  iintro H24
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old16 h16no h16.one h16.two h16.three h16.four
      h16.five h16.six h16.seven $$ H16
  iintro H16
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old8 h8no h8.one h8.two h8.three h8.four
      h8.five h8.six h8.seven $$ H8
  iintro H8
  ihave H16' : pointsTo_u64 0 (((sp - 48) + 8) + 8) 0 $$ [H16]
  · rw [show ((sp - 48) + 8) + 8 = (sp - 48) + 16 by bv_decide]
    iexact H16
  ihave H24' : pointsTo_u64 0 (((sp - 48) + 8) + 16) 0 $$ [H24]
  · rw [show ((sp - 48) + 8) + 16 = (sp - 48) + 24 by bv_decide]
    iexact H24
  ihave H32' : pointsTo_u64 0 (((sp - 48) + 8) + 24) 0 $$ [H32]
  · rw [show ((sp - 48) + 8) + 24 = (sp - 48) + 32 by bv_decide]
    iexact H32
  ihave HresultParts :=
    (pointsTo_u64_as_ioWord ((sp - 48) + 40) oldResult).mp $$ Hresult
  icases HresultParts with ⟨Htag, Hpad1, Hpad2, Hpad3, Hcount⟩
  ihave HoutParts := (pointsTo_u64_as_ioWord out oldOut).mp $$ Hout
  icases HoutParts with
    ⟨HoutTag, HoutPad1, HoutPad2, HoutPad3, HoutCount⟩
  ihave Hbuffer := (four_u64_zero_as_bytes ((sp - 48) + 8)).mp $$
    [H8 H16' H24' H32']
  · iframe
  ihave HenvPair : hostEnvOwn 0 (Universal.envFor «module») ∗
      hostEnvOwn 0 (Universal.envFor «module») $$ [Henv]
  · isplit <;> iexact Henv
  icases HenvPair with ⟨Henv, HenvKeep⟩
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_const
  rw [show 8 + (sp - 48) = (sp - 48) + 8 by bv_decide,
    show 40 + (sp - 48) = (sp - 48) + 40 by bv_decide]
  iapply twp_read_adapter_no_stack host ((sp - 48) + 40) ignored
      ((sp - 48) + 8) 32 (List.replicate 32 0) []
      (u64Byte oldResult 0) ((oldResult >>> 32).toUInt32)
      (by simp [hinput]) (by simp) (by decide) hbufferNowrap hreadCount $$
      [$Hruntime $Henv $Hhost $Hbuffer $Htag $Hcount]
  iintro ⟨Hruntime, Hhost, Hbuffer, Htag, Hcount⟩
  have hafter : afterUniversalRead host 0 = host := by
    cases host with
    | mk stdio random oom =>
      cases stdio
      simp_all [afterUniversalRead]
  simp only [List.length_nil, Nat.reduceAdd, List.drop_zero,
    List.nil_append, hafter]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load8U (4 : UInt8) h40no $$ Htag
  iintro Htag
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_eq rfl
  iapply twp_brIf (by decide) rfl
  simp
  ihave Hcount44 : pointsTo_u32 0 ((sp - 48) + 44) 0 $$ [Hcount]
  · rw [show (sp - 48) + 44 = ((sp - 48) + 40) + 4 by bv_decide]
    iexact Hcount
  iapply twp_localGet rfl
  iapply twp_load32 0 h44no h44.one h44.two h44.three $$ Hcount44
  iintro Hcount44
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_geU rfl
  simp
  iapply twp_brIfZero
  iapply twp_block
  iapply twp_block
  iapply twp_block
  ihave Hcapacity0 : pointsTo_u32 0 (vector + 0) capacity $$ [Hcapacity]
  · rw [UInt32.add_zero]
    iexact Hcapacity
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 capacity hvecCapacity.noWrap hvecCapacity.one
      hvecCapacity.two hvecCapacity.three $$ Hcapacity0
  iintro Hcapacity0
  iapply twp_localGet rfl
  iapply twp_load32 length hvecLength.noWrap hvecLength.one
      hvecLength.two hvecLength.three $$ Hlength
  iintro Hlength
  iapply twp_localTee rfl
  iapply twp_sub
  iapply twp_leU rfl
  simp
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 (α := Universal.State) ((oldOut >>> 32).toUInt32)
      houtCount.noWrap houtCount.one houtCount.two houtCount.three
      $$ HoutCount
  iintro HoutCount
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_addr (u64Byte oldOut 0) $$ HoutTag
  iintro HoutTag
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_store32 length hvecLength.noWrap hvecLength.one
      hvecLength.two hvecLength.three $$ Hlength
  iintro Hlength
  iapply twp_exitControl rfl
  simp
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  have hrestore : 48 + (sp - 48) = sp := by bv_decide
  rw [hrestore]
  iapply twp_globalSet $$ HframeSp
  iintro Hsp
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  ihave Hresult : pointsTo_u64 0 ((sp - 48) + 40)
      (ioWord oldResult 4 0) $$
      [Htag Hpad1 Hpad2 Hpad3 Hcount44]
  · iapply (pointsTo_ioWord ((sp - 48) + 40) oldResult 4 0).mpr
    rw [show ((sp - 48) + 40) + 4 = (sp - 48) + 44 by bv_decide]
    iframe
  ihave Hout : pointsTo_u64 0 out (ioWord oldOut 4 0) $$
      [HoutTag HoutPad1 HoutPad2 HoutPad3 HoutCount]
  · iapply (pointsTo_ioWord out oldOut 4 0).mpr
    iframe
  iapply Hcont
  iframe

set_option maxHeartbeats 4000000 in
/-- Nonempty successful leg of module function 4 when the destination vector
already has enough spare capacity. -/
theorem twp_read_chunk_nonempty_fits
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (out ignored vector data sp : UInt32)
    (capacity length : UInt32) (chunk oldDst : List UInt8)
    (old8 old16 old24 old32 oldResult oldOut : UInt64)
    (hchunk : chunk = host.stdio.input.take 32)
    (hchunkNe : chunk ≠ [])
    (hfits : UInt32.ofNat chunk.length ≤ capacity - length)
    (h8no : ((sp - 48) + 8).toNat = (sp - 48).toNat + 8)
    (h16no : ((sp - 48) + 16).toNat = (sp - 48).toNat + 16)
    (h24no : ((sp - 48) + 24).toNat = (sp - 48).toNat + 24)
    (h32no : ((sp - 48) + 32).toNat = (sp - 48).toNat + 32)
    (h40no : ((sp - 48) + 40).toNat = (sp - 48).toNat + 40)
    (h44no : ((sp - 48) + 44).toNat = (sp - 48).toNat + 44)
    (h8 : Address64Facts ((sp - 48) + 8))
    (h16 : Address64Facts ((sp - 48) + 16))
    (h24 : Address64Facts ((sp - 48) + 24))
    (h32 : Address64Facts ((sp - 48) + 32))
    (h44 : Address64Facts ((sp - 48) + 44))
    (hreadCount : Offset32Facts ((sp - 48) + 40) 4)
    (hvecCapacity : Offset32Facts vector 0)
    (hvecData : Offset32Facts vector 4)
    (hvecLength : Offset32Facts vector 8)
    (houtCount : Offset32Facts out 4)
    (hbufferNowrap : ((sp - 48) + 8).toNat + 32 < UInt32.size)
    (hdstLen : oldDst.length = chunk.length)
    (hdstNowrap : (data + length).toNat + chunk.length < UInt32.size)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 ((sp - 48) + 8) old8 ∗
      pointsTo_u64 0 ((sp - 48) + 16) old16 ∗
      pointsTo_u64 0 ((sp - 48) + 24) old24 ∗
      pointsTo_u64 0 ((sp - 48) + 32) old32 ∗
      pointsTo_u64 0 ((sp - 48) + 40) oldResult ∗
      pointsTo_u32 0 vector capacity ∗
      pointsTo_u32 0 (vector + 4) data ∗
      pointsTo_u32 0 (vector + 8) length ∗
      pointsToBytes 0 (data + length) oldDst ∗
      pointsTo_u64 0 out oldOut -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn (afterUniversalRead host chunk.length) ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsToBytes 0 ((sp - 48) + 8)
        (chunk ++ (List.replicate 32 0).drop chunk.length) ∗
      pointsTo_u64 0 ((sp - 48) + 40)
        (ioWord oldResult 4 (UInt32.ofNat chunk.length)) ∗
      pointsTo_u32 0 vector capacity ∗
      pointsTo_u32 0 (vector + 4) data ∗
      pointsTo_u32 0 (vector + 8)
        (length + UInt32.ofNat chunk.length) ∗
      pointsToBytes 0 (data + length) chunk ∗
      pointsTo_u64 0 out
        (ioWord oldOut 4 (UInt32.ofNat chunk.length)) -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 vector, .i32 ignored, .i32 out] ++ stack },
        [.call 4] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hsp, H8, H16, H24, H32, Hresult,
    Hcapacity, Hdata, Hlength, Hdst, Hout⟩ Hcont
  have hchunkLen : chunk.length ≤ 32 := by
    rw [hchunk, List.length_take]
    omega
  have hchunkPos : 0 < chunk.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hchunkNe
    exact List.eq_nil_of_length_eq_zero hz
  have hchunkSize : chunk.length < UInt32.size := by
    rw [show UInt32.size = 4294967296 by decide]
    omega
  have hcountNe : UInt32.ofNat chunk.length ≠ 0 := by
    intro hz
    apply hchunkNe
    apply List.eq_nil_of_length_eq_zero
    have hzNat := congrArg UInt32.toNat hz
    rw [UInt32.toNat_ofNat_of_lt' hchunkSize] at hzNat
    simpa using hzNat
  have hcountLt : UInt32.ofNat chunk.length < (33 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' hchunkSize]
    exact Nat.lt_succ_iff.mpr hchunkLen
  simp only [List.singleton_append]
  iapply twp_call «module» 4 func1Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams,
    ValueType.zero, func1]
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localTee rfl
  iapply twp_globalSet $$ Hsp
  iintro HframeSp
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old32 h32no h32.one h32.two h32.three h32.four
      h32.five h32.six h32.seven $$ H32
  iintro H32
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old24 h24no h24.one h24.two h24.three h24.four
      h24.five h24.six h24.seven $$ H24
  iintro H24
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old16 h16no h16.one h16.two h16.three h16.four
      h16.five h16.six h16.seven $$ H16
  iintro H16
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old8 h8no h8.one h8.two h8.three h8.four
      h8.five h8.six h8.seven $$ H8
  iintro H8
  ihave H16' : pointsTo_u64 0 (((sp - 48) + 8) + 8) 0 $$ [H16]
  · rw [show ((sp - 48) + 8) + 8 = (sp - 48) + 16 by bv_decide]
    iexact H16
  ihave H24' : pointsTo_u64 0 (((sp - 48) + 8) + 16) 0 $$ [H24]
  · rw [show ((sp - 48) + 8) + 16 = (sp - 48) + 24 by bv_decide]
    iexact H24
  ihave H32' : pointsTo_u64 0 (((sp - 48) + 8) + 24) 0 $$ [H32]
  · rw [show ((sp - 48) + 8) + 24 = (sp - 48) + 32 by bv_decide]
    iexact H32
  ihave HresultParts :=
    (pointsTo_u64_as_ioWord ((sp - 48) + 40) oldResult).mp $$ Hresult
  icases HresultParts with ⟨Htag, Hpad1, Hpad2, Hpad3, Hcount⟩
  ihave HoutParts := (pointsTo_u64_as_ioWord out oldOut).mp $$ Hout
  icases HoutParts with
    ⟨HoutTag, HoutPad1, HoutPad2, HoutPad3, HoutCount⟩
  ihave Hbuffer := (four_u64_zero_as_bytes ((sp - 48) + 8)).mp $$
    [H8 H16' H24' H32']
  · iframe
  ihave HenvPair : hostEnvOwn 0 (Universal.envFor «module») ∗
      hostEnvOwn 0 (Universal.envFor «module») $$ [Henv]
  · isplit <;> iexact Henv
  icases HenvPair with ⟨Henv, HenvKeep⟩
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_const
  rw [show 8 + (sp - 48) = (sp - 48) + 8 by bv_decide,
    show 40 + (sp - 48) = (sp - 48) + 40 by bv_decide]
  iapply twp_read_adapter_no_stack host ((sp - 48) + 40) ignored
      ((sp - 48) + 8) 32 (List.replicate 32 0) chunk
      (u64Byte oldResult 0) ((oldResult >>> 32).toUInt32)
      hchunk (by simp) (by decide) hbufferNowrap hreadCount $$
      [$Hruntime $Henv $Hhost $Hbuffer $Htag $Hcount]
  iintro ⟨Hruntime, Hhost, Hbuffer, Htag, Hcount⟩
  simp only [afterUniversalRead]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load8U (4 : UInt8) h40no $$ Htag
  iintro Htag
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_eq rfl
  iapply twp_brIf (by decide) rfl
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    tsub_self, List.set_cons_zero, Nat.reduceSub, Nat.reduceLT,
    UInt8.toUInt32_ofNat, List.set_cons_succ, List.take_nil,
    List.drop_nil, List.append_nil]
  ihave Hcount44 : pointsTo_u32 0 ((sp - 48) + 44)
      (UInt32.ofNat chunk.length) $$ [Hcount]
  · rw [show (sp - 48) + 44 = ((sp - 48) + 40) + 4 by bv_decide]
    iexact Hcount
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat chunk.length) h44no h44.one h44.two
      h44.three $$ Hcount44
  iintro Hcount44
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_geU rfl
  have hcountNge :
      ¬ (33 : UInt32) ≤ UInt32.ofNat chunk.length :=
    UInt32.not_le.mpr hcountLt
  simp only [hcountNge, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_block
  iapply twp_block
  iapply twp_block
  ihave Hcapacity0 : pointsTo_u32 0 (vector + 0) capacity $$ [Hcapacity]
  · rw [UInt32.add_zero]
    iexact Hcapacity
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 capacity hvecCapacity.noWrap hvecCapacity.one
      hvecCapacity.two hvecCapacity.three $$ Hcapacity0
  iintro Hcapacity0
  iapply twp_localGet rfl
  iapply twp_load32 length hvecLength.noWrap hvecLength.one
      hvecLength.two hvecLength.three $$ Hlength
  iintro Hlength
  iapply twp_localTee rfl
  iapply twp_sub
  iapply twp_leU rfl
  simp only [hfits, ↓reduceIte]
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  simp only [hcountNe, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_exitControl rfl
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  simp only [hcountNe, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_load32 data hvecData.noWrap hvecData.one hvecData.two
      hvecData.three $$ Hdata
  iintro Hdata
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  ihave HbufferParts :=
    (pointsToBytes_append 0 ((sp - 48) + 8) chunk
      ((List.replicate 32 0).drop chunk.length)).mp $$ Hbuffer
  icases HbufferParts with ⟨Hchunk, HbufferRest⟩
  have hcountToNat : (UInt32.ofNat chunk.length).toNat = chunk.length :=
    UInt32.toNat_ofNat_of_lt' hchunkSize
  have hsrcNowrap : ((sp - 48) + 8).toNat + chunk.length <
      UInt32.size := by omega
  rw [show 8 + (sp - 48) = (sp - 48) + 8 by bv_decide,
    show length + data = data + length by bv_decide]
  iapply twp_memoryCopy32 (len := UInt32.ofNat chunk.length)
      oldDst chunk (by simpa [hcountToNat] using hdstLen)
      (by simpa [hcountToNat]) (by simpa [hcountToNat] using hchunkPos)
      (by simpa [hcountToNat] using hdstNowrap)
      (by simpa [hcountToNat] using hsrcNowrap) $$ Hchunk Hdst
  iintro Hchunk Hdst
  ihave Hbuffer : pointsToBytes 0 ((sp - 48) + 8)
      (chunk ++ (List.replicate 32 0).drop chunk.length) $$
      [Hchunk HbufferRest]
  · iapply (pointsToBytes_append 0 ((sp - 48) + 8) chunk
      ((List.replicate 32 0).drop chunk.length)).mpr
    iframe
  iapply twp_exitControl rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 (α := Universal.State) ((oldOut >>> 32).toUInt32)
      houtCount.noWrap houtCount.one houtCount.two houtCount.three
      $$ HoutCount
  iintro HoutCount
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_addr (u64Byte oldOut 0) $$ HoutTag
  iintro HoutTag
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_store32 length hvecLength.noWrap hvecLength.one
      hvecLength.two hvecLength.three $$ Hlength
  iintro Hlength
  iapply twp_exitControl rfl
  simp
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  have hrestore : 48 + (sp - 48) = sp := by bv_decide
  rw [hrestore]
  iapply twp_globalSet $$ HframeSp
  iintro Hsp
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  ihave Hresult : pointsTo_u64 0 ((sp - 48) + 40)
      (ioWord oldResult 4 (UInt32.ofNat chunk.length)) $$
      [Htag Hpad1 Hpad2 Hpad3 Hcount44]
  · iapply (pointsTo_ioWord ((sp - 48) + 40) oldResult 4
      (UInt32.ofNat chunk.length)).mpr
    rw [show ((sp - 48) + 40) + 4 = (sp - 48) + 44 by bv_decide]
    iframe
  ihave Hout : pointsTo_u64 0 out
      (ioWord oldOut 4 (UInt32.ofNat chunk.length)) $$
      [HoutTag HoutPad1 HoutPad2 HoutPad3 HoutCount]
  · iapply (pointsTo_ioWord out oldOut 4
      (UInt32.ofNat chunk.length)).mpr
    iframe
  ihave Hlength' : pointsTo_u32 0 (vector + 8)
      (length + UInt32.ofNat chunk.length) $$ [Hlength]
  · rw [show length + UInt32.ofNat chunk.length =
        UInt32.ofNat chunk.length + length by bv_decide]
    iexact Hlength
  iapply Hcont
  iframe

end Project.HexDecodeStdio
