import CodeLib
import Project.HexStdio.Program
import HexEncodeStdio.Helpers
import HexEncodeStdio.Hex
import HexEncodeStdio.TotalIterator
import HexEncodeStdio.TotalEncodeLoop

namespace Project.HexEncodeStdio.TotalEncodeFunction

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private abbrev func6Locals (result source length stackPtr slot4 ascii
    dest tmp1 tmp2 : UInt32) (values : List Value := []) : Locals :=
  ⟨[.i32 result, .i32 source, .i32 length],
    [.i32 stackPtr, .i32 slot4, .i32 ascii, .i32 dest, .i32 tmp1, .i32 tmp2],
    values⟩

/-- The straight-line epilogue of the generated encoder. -/
def func6FinishCode : Program := Project.HexStdio.func6.drop 29

private theorem func6_drop16_eq : Project.HexStdio.func6.drop 16 =
    .localGet 3 :: .const 1048576 :: .store32 28 ::
    .localGet 3 :: .localGet 4 :: .store32 24 ::
    .localGet 3 :: .localGet 1 :: .store32 20 ::
    .localGet 3 :: .const 1114112 :: .store32 16 ::
    .block 0 0 Project.HexEncodeStdio.TotalEncodeLoop.encodeOuterBody [] [] ::
    func6FinishCode := by
  rfl

theorem func6_finish {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result source length stackPtr slot4 ascii dest tmp1 tmp2 : UInt32)
    (capacity output : UInt32) (bytes : List UInt8)
    (oldResultPair : UInt64) (oldResultLen : UInt32)
    (hstack : stackPtr.toNat + 32 < UInt32.size)
    (hresult : result.toNat + 12 < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsToAt 0 0 (.i32 stackPtr) ∗
      pointsTo_u32 0 (stackPtr + 4) capacity ∗
      pointsTo_u32 0 (stackPtr + 8) output ∗
      pointsTo_u32 0 (stackPtr + 12) (UInt32.ofNat bytes.length) ∗
      pointsTo_u64 0 (result + 0) oldResultPair ∗
      pointsTo_u32 0 (result + 8) oldResultLen ∗
      (globalPointsToAt 0 0 (.i32 (stackPtr + 32)) -∗
        pointsTo_u32 0 result capacity -∗
        pointsTo_u32 0 (result + 4) output -∗
        pointsTo_u32 0 (result + 8) (UInt32.ofNat bytes.length) -∗
        WP (.running
          ⟨func6Locals result source length stackPtr slot4 ascii dest
              tmp1 tmp2,
            [], arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨func6Locals result source length stackPtr slot4 ascii dest
            tmp1 tmp2,
          func6FinishCode, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] := by
  obtain ⟨s12, s13, s14, s15⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 12 (by omega)
  obtain ⟨s4, s5, s6, s7⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 4 (by omega)
  obtain ⟨s8, s9, s10, s11⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 8 (by omega)
  have s8' : ((stackPtr + 4) + 4).toNat =
      (stackPtr + 4).toNat + 4 := by
    calc
      _ = (stackPtr + 8).toNat := congrArg UInt32.toNat (by bv_decide)
      _ = stackPtr.toNat + 8 := by simpa using s8
      _ = (stackPtr + 4).toNat + 4 := by
        rw [show (stackPtr + 4).toNat = stackPtr.toNat + 4 by
          simpa using s4]
  have s9' : ((stackPtr + 4) + 5).toNat =
      (stackPtr + 4).toNat + 5 := by
    calc
      _ = (stackPtr + 9).toNat := congrArg UInt32.toNat (by bv_decide)
      _ = stackPtr.toNat + 9 := by
        simpa using UInt32.add_ofNat_toNat_noWrap stackPtr 9 (by decide) (by
          norm_num [UInt32.size] at hstack ⊢; omega)
      _ = (stackPtr + 4).toNat + 5 := by
        rw [show (stackPtr + 4).toNat = stackPtr.toNat + 4 by
          simpa using s4]
  have s10' : ((stackPtr + 4) + 6).toNat =
      (stackPtr + 4).toNat + 6 := by
    calc
      _ = (stackPtr + 10).toNat := congrArg UInt32.toNat (by bv_decide)
      _ = stackPtr.toNat + 10 := by
        simpa using UInt32.add_ofNat_toNat_noWrap stackPtr 10 (by decide) (by
          norm_num [UInt32.size] at hstack ⊢; omega)
      _ = (stackPtr + 4).toNat + 6 := by
        rw [show (stackPtr + 4).toNat = stackPtr.toNat + 4 by
          simpa using s4]
  have s11' : ((stackPtr + 4) + 7).toNat =
      (stackPtr + 4).toNat + 7 := by
    calc
      _ = (stackPtr + 11).toNat := congrArg UInt32.toNat (by bv_decide)
      _ = stackPtr.toNat + 11 := by
        simpa using UInt32.add_ofNat_toNat_noWrap stackPtr 11 (by decide) (by
          norm_num [UInt32.size] at hstack ⊢; omega)
      _ = (stackPtr + 4).toNat + 7 := by
        rw [show (stackPtr + 4).toNat = stackPtr.toNat + 4 by
          simpa using s4]
  obtain ⟨r8, r9, r10, r11⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts result 8 (by omega)
  obtain ⟨r0, r1, r2, r3⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts result 0 (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  have r4 : ((result + 0) + 4).toNat = (result + 0).toNat + 4 := by
    rw [UInt32.add_zero]
    simpa using UInt32.add_ofNat_toNat_noWrap result 4 (by decide) (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  have r5 : ((result + 0) + 5).toNat = (result + 0).toNat + 5 := by
    rw [UInt32.add_zero]
    simpa using UInt32.add_ofNat_toNat_noWrap result 5 (by decide) (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  have r6 : ((result + 0) + 6).toNat = (result + 0).toNat + 6 := by
    rw [UInt32.add_zero]
    simpa using UInt32.add_ofNat_toNat_noWrap result 6 (by decide) (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  have r7 : ((result + 0) + 7).toNat = (result + 0).toNat + 7 := by
    rw [UInt32.add_zero]
    simpa using UInt32.add_ofNat_toNat_noWrap result 7 (by decide) (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  iintro ⟨Hglobal, Hcap, Hptr, Hlen, HresultPair, HresultLen, Hfinish⟩
  simp only [func6FinishCode, Project.HexStdio.func6, List.drop_succ_cons,
    List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat bytes.length) s12 s13 s14 s15 $$ Hlen
  iintro Hlen
  iapply twp_store32 oldResultLen r8 r9 r10 r11 $$ HresultLen
  iintro HresultLen
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hptr' : pointsTo_u32 0 ((stackPtr + 4) + 4) output $$ [Hptr]
  · rw [show (stackPtr + 4) + 4 = stackPtr + 8 by bv_decide]
    iexact Hptr
  ihave Hpair := Project.HexEncodeStdio.Helpers.pointsTo_u64_pair_join
    0 (stackPtr + 4) capacity output $$ [$Hcap $Hptr']
  iapply twp_load64
    (capacity.toUInt64 ||| (output.toUInt64 <<< 32))
    s4 s5 s6 s7
    s8' s9' s10' s11' $$ Hpair
  iintro Hpair
  iapply twp_store64 (address := result) oldResultPair r0 r1 r2 r3 r4 r5 r6 r7
    $$ HresultPair
  iintro HresultPair
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  ihave Hglobal' : globalPointsToAt 0 0 (.i32 (stackPtr + 32)) $$ [Hglobal]
  · rw [UInt32.add_comm]
    iexact Hglobal
  ihave HresultPair' : pointsTo_u64 0 (result + 0)
      (capacity.toUInt64 ||| (output.toUInt64 <<< 32)) $$ [HresultPair]
  · iexact HresultPair
  ihave Hpair := Project.HexEncodeStdio.Helpers.pointsTo_u64_pair_split
    0 (result + 0) capacity output $$ HresultPair'
  icases Hpair with ⟨HcapResult, HptrResult⟩
  ihave HcapResult' : pointsTo_u32 0 result capacity $$ [HcapResult]
  · rw [show result + 0 = result by simp]
    iexact HcapResult
  ihave HptrResult' : pointsTo_u32 0 (result + 4) output $$ [HptrResult]
  · rw [show (result + 0) + 4 = result + 4 by simp]
    iexact HptrResult
  iapply Hfinish $$ Hglobal' HcapResult' HptrResult' HresultLen

/-- Once the output allocation has succeeded, the generated encoder
initializes its byte iterator, runs the alternating nibble loop, and publishes
the completed vector in `result`. -/
theorem func6_after_alloc_nonempty {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result source stackPtr output : UInt32) (input : List UInt8)
    (out : List UInt8) (old16 old20 old24 old28 : UInt32)
    (oldResultPair : UInt64) (oldResultLen : UInt32)
    (R : IProp (WasmHeapGF α))
    (hinput : input ≠ [])
    (houtLen : out.length = 2 * input.length)
    (hcapacity : 2 * input.length < UInt32.size)
    (hstack : stackPtr.toNat + 32 < UInt32.size)
    (hsource : source.toNat + input.length + 1 < UInt32.size)
    (hresult : result.toNat + 12 < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    R ∗ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      globalPointsToAt 0 0 (.i32 stackPtr) ∗
      pointsTo_u32 0 (stackPtr + 4)
        (UInt32.ofNat (Project.HexEncodeStdio.TotalEncodeLoop.encodeCapacityNat input)) ∗
      pointsTo_u32 0 (stackPtr + 8) output ∗
      pointsTo_u32 0 (stackPtr + 12) 0 ∗
      pointsTo_u32 0 (stackPtr + 16) old16 ∗
      pointsTo_u32 0 (stackPtr + 20) old20 ∗
      pointsTo_u32 0 (stackPtr + 24) old24 ∗
      pointsTo_u32 0 (stackPtr + 28) old28 ∗
      pointsTo_u64 0 (result + 0) oldResultPair ∗
      pointsTo_u32 0 (result + 8) oldResultLen ∗
      pointsToBytes 0 source input ∗
      pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable ∗
      pointsToBytes 0 output out ∗
      (R -∗ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        globalPointsToAt 0 0 (.i32 (stackPtr + 32)) -∗
        pointsTo_u32 0 result
          (UInt32.ofNat (Project.HexEncodeStdio.TotalEncodeLoop.encodeCapacityNat input)) -∗
        pointsTo_u32 0 (result + 4) output -∗
        pointsTo_u32 0 (result + 8)
          (UInt32.ofNat (Project.HexStdio.Spec.encode input).length) -∗
        pointsTo_u32 0 (stackPtr + 16) Project.HexEncodeStdio.TotalIterator.sentinel -∗
        pointsTo_u32 0 (stackPtr + 20)
          (source + UInt32.ofNat input.length) -∗
        pointsToBytes 0 source input -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        pointsToBytes 0 output (Project.HexStdio.Spec.encode input) -∗
        ∀ finalLocals : Locals,
        WP (.running
          ⟨finalLocals,
            [], arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨func6Locals result source (UInt32.ofNat input.length) stackPtr
            (source + UInt32.ofNat input.length) 0 0 0 0,
          Project.HexStdio.func6.drop 16, arity, remainder, controls, calls⟩ :
          Expr α) @ s; E [{ Φ }] := by
  obtain ⟨p16, p17, p18, p19⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 16 (by omega)
  obtain ⟨p20, p21, p22, p23⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 20 (by omega)
  obtain ⟨p24, p25, p26, p27⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 24 (by omega)
  obtain ⟨p28, p29, p30, p31⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 28 (by omega)
  have hzero : 0 < input.length := by
    simpa only [List.length_pos_iff] using hinput
  iintro ⟨HR, Hruntime, Hglobal, Hcap, HoutputPtr, Hlength, H16, H20, H24, H28,
    HresultPair, HresultLen, Hsource, Htable, Hout, Hpost⟩
  rw [func6_drop16_eq]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old28 p28 p29 p30 p31 $$ H28
  iintro HtablePtr
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old24 p24 p25 p26 p27 $$ H24
  iintro Hend
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old20 p20 p21 p22 p23 $$ H20
  iintro Hcursor
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old16 p16 p17 p18 p19 $$ H16
  iintro Hcurrent
  iapply twp_block
  rw [Project.HexEncodeStdio.TotalEncodeLoop.encodeOuterBody_eq]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  simp only [UInt32.add_comm (16 : UInt32) stackPtr]
  iapply Project.HexEncodeStdio.TotalIterator.twp_call_func18_high_at
    (stackPtr + 16) source input 0 (by omega)
    (by
      have hs16 : (stackPtr + UInt32.ofNat 16).toNat =
          stackPtr.toNat + 16 := by
        simpa using UInt32.add_ofNat_toNat_noWrap stackPtr 16 (by decide) (by
          norm_num [UInt32.size] at hstack ⊢
          omega)
      rw [show (16 : UInt32) = UInt32.ofNat 16 by rfl,
        hs16]
      omega)
    hsource
    (callerLocals := func6Locals result source (UInt32.ofNat input.length)
      stackPtr (source + UInt32.ofNat input.length) 0 0 0 0)
    (stack := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hcursor]
  · rw [show source + UInt32.ofNat 0 = source by simp,
      show stackPtr + 16 + 4 = stackPtr + 20 by bv_decide]
    iexact Hcursor
  isplitl [Hend]
  · rw [show stackPtr + 16 + 8 = stackPtr + 24 by bv_decide]
    iexact Hend
  isplitl [HtablePtr]
  · rw [show stackPtr + 16 + 12 = stackPtr + 28 by bv_decide]
    iexact HtablePtr
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htable]
  · iexact Htable
  iintro Hruntime Hcurrent Hcursor Hend HtablePtr Hsource Htable
  iapply twp_localTee rfl
  iapply twp_const
  iapply Project.HexEncodeStdio.TotalIterator.twp_eq (result := 0)
    (by simp [Project.HexEncodeStdio.Hex.hexDigit_toUInt32_ne_sentinel])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_load32 0
    (show (stackPtr + 12).toNat = stackPtr.toNat + 12 by
      simpa using (Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 12 (by omega)).1)
    (Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 12 (by omega)).2.1
    (Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 12 (by omega)).2.2.1
    (Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 12 (by omega)).2.2.2
    $$ Hlength
  iintro Hlength
  iapply twp_localSet rfl
  let initial : Project.HexEncodeStdio.TotalEncodeLoop.EncodeLoopState input :=
    ⟨0, by omega, false, 0, source + UInt32.ofNat input.length, 0⟩
  simp only [func6Locals, List.set]
  have hlocals :
      (⟨[.i32 result, .i32 0,
          .i32 (Project.HexStdio.Spec.hexDigit
            (input[0].toNat / 16)).toUInt32],
        [.i32 stackPtr, .i32 (source + UInt32.ofNat input.length), .i32 0,
          .i32 0, .i32 0, .i32 0], []⟩ : Locals) =
        Project.HexEncodeStdio.TotalEncodeLoop.loopLocals result stackPtr output initial := by
    rfl
  rw [hlocals]
  iapply Project.HexEncodeStdio.TotalEncodeLoop.func6_encode_loop result stackPtr output source
    input initial
    (iprop% R ∗ globalPointsToAt 0 0 (.i32 stackPtr) ∗
      pointsTo_u64 0 (result + 0) oldResultPair ∗
      pointsTo_u32 0 (result + 8) oldResultLen ∗
      (R -∗ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        globalPointsToAt 0 0 (.i32 (stackPtr + 32)) -∗
        pointsTo_u32 0 result
          (UInt32.ofNat (Project.HexEncodeStdio.TotalEncodeLoop.encodeCapacityNat input)) -∗
        pointsTo_u32 0 (result + 4) output -∗
        pointsTo_u32 0 (result + 8)
          (UInt32.ofNat (Project.HexStdio.Spec.encode input).length) -∗
        pointsTo_u32 0 (stackPtr + 16) Project.HexEncodeStdio.TotalIterator.sentinel -∗
        pointsTo_u32 0 (stackPtr + 20)
          (source + UInt32.ofNat input.length) -∗
        pointsToBytes 0 source input -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        pointsToBytes 0 output (Project.HexStdio.Spec.encode input) -∗
        ∀ finalLocals : Locals,
        WP (.running
          ⟨finalLocals,
            [], arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]))
    hcapacity hstack hsource
    (s := s) (E := E) (Φ := Φ) (arity := arity) (remainder := remainder)
    (afterLoop := []) (controls :=
      { kind := .block, paramArity := 0, resultArity := 0,
        body := [.localGet 3, .const 16, .add, .call 21, .localTee 2,
          .const 1114112, .eq, .br_if 0, .localGet 3, .load32 12,
          .localSet 1,
          .loop 0 0 Project.HexEncodeStdio.TotalEncodeLoop.encodeLoopBody [] []],
        continuation := func6FinishCode,
        belowStack := List.drop 0 [] } :: controls) (calls := calls)
  · intro state finalOut hphase hlast hfinalLen hprefix
    have hposition : Project.HexEncodeStdio.TotalEncodeLoop.loopPosition state + 1 =
        2 * input.length := by
      simp only [Project.HexEncodeStdio.TotalEncodeLoop.loopPosition, hphase]
      omega
    have houtEq : finalOut = Project.HexStdio.Spec.encode input := by
      have hp := hprefix
      rw [hposition] at hp
      calc
        finalOut = finalOut.take (2 * input.length) := by
          rw [← hfinalLen, List.take_length]
        _ = (Project.HexStdio.Spec.encode input).take (2 * input.length) := hp
        _ = Project.HexStdio.Spec.encode input := by
          rw [← Project.HexEncodeStdio.Hex.encode_length, List.take_length]
    have hlenWord : UInt32.ofNat (2 * state.byteIndex + 1) + 1 =
        UInt32.ofNat (Project.HexStdio.Spec.encode input).length := by
      rw [Project.HexEncodeStdio.Hex.encode_length]
      rw [Project.HexEncodeStdio.TotalEncodeLoop.u32_ofNat_succ (by
        have := hcapacity
        omega)]
      congr 1
      simpa only [Project.HexEncodeStdio.TotalEncodeLoop.loopPosition, hphase] using hposition
    subst finalOut
    iintro Hruntime Hcap HoutputPtr Hlength Hcurrent Hcursor Hend HtablePtr
      Hsource Htable Hout Hfinish
    icases Hfinish with ⟨HR, Hglobal, HresultPair, HresultLen, Hpost⟩
    iapply twp_exitControl rfl
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    iapply func6_finish result
      (UInt32.ofNat (2 * state.byteIndex + 1) + 1)
      Project.HexEncodeStdio.TotalIterator.sentinel stackPtr 1 1
      (output + UInt32.ofNat (2 * state.byteIndex + 1)) 0 0
      (UInt32.ofNat (Project.HexEncodeStdio.TotalEncodeLoop.encodeCapacityNat input)) output
      (Project.HexStdio.Spec.encode input) oldResultPair oldResultLen hstack
      hresult
    isplitl [Hglobal]
    · iexact Hglobal
    isplitl [Hcap]
    · iexact Hcap
    isplitl [HoutputPtr]
    · iexact HoutputPtr
    isplitl [Hlength]
    · rw [← hlenWord]
      iexact Hlength
    isplitl [HresultPair]
    · iexact HresultPair
    isplitl [HresultLen]
    · iexact HresultLen
    iintro Hglobal HcapResult HptrResult HlenResult
    simp only [Project.HexEncodeStdio.Hex.encode_length]
    ispecialize Hpost $$ HR Hruntime Hglobal HcapResult HptrResult HlenResult
      Hcurrent
    ispecialize Hpost $$ Hcursor Hsource Htable Hout
    ispecialize Hpost $$ %(func6Locals result
      (UInt32.ofNat (2 * state.byteIndex + 1) + 1)
      Project.HexEncodeStdio.TotalIterator.sentinel stackPtr 1 1
      (output + UInt32.ofNat (2 * state.byteIndex + 1)) 0 0)
    iexact Hpost
  simp only [Project.HexEncodeStdio.TotalEncodeLoop.encodeLoopInvariant,
    Project.HexEncodeStdio.TotalEncodeLoop.loopLocals, Project.HexEncodeStdio.TotalEncodeLoop.loopPosition,
    Project.HexEncodeStdio.TotalEncodeLoop.loopDigit, Project.HexEncodeStdio.TotalEncodeLoop.loopSaved, initial,
    func6Locals]
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hcap]
  · iexact Hcap
  isplitl [HoutputPtr]
  · iexact HoutputPtr
  isplitl [Hlength]
  · iexact Hlength
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hcursor]
  · rw [show stackPtr + 16 + 4 = stackPtr + 20 by bv_decide]
    iexact Hcursor
  isplitl [Hend]
  · rw [show stackPtr + 16 + 8 = stackPtr + 24 by bv_decide]
    iexact Hend
  isplitl [HtablePtr]
  · rw [show stackPtr + 16 + 12 = stackPtr + 28 by bv_decide]
    iexact HtablePtr
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htable]
  · iexact Htable
  iexists out
  isplitl [Hout]
  · iexact Hout
  isplitr
  · ipureintro
    exact houtLen
  isplitr
  · ipureintro
    rfl
  isplitl [HR]
  · iexact HR
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [HresultPair]
  · iexact HresultPair
  isplitl [HresultLen]
  · iexact HresultLen
  · iexact Hpost

/-- The zero-length encoder path performs no allocation.  Its iterator starts
at its end pointer, so the first iterator call returns the sentinel and the
outer block immediately publishes Rust's empty-vector representation. -/
theorem func6_after_empty {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result source stackPtr : UInt32)
    (old16 old20 old24 old28 : UInt32)
    (oldResultPair : UInt64) (oldResultLen : UInt32)
    (hstack : stackPtr.toNat + 32 < UInt32.size)
    (hresult : result.toNat + 12 < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      globalPointsToAt 0 0 (.i32 stackPtr) ∗
      pointsTo_u32 0 (stackPtr + 4) 0 ∗
      pointsTo_u32 0 (stackPtr + 8) 1 ∗
      pointsTo_u32 0 (stackPtr + 12) 0 ∗
      pointsTo_u32 0 (stackPtr + 16) old16 ∗
      pointsTo_u32 0 (stackPtr + 20) old20 ∗
      pointsTo_u32 0 (stackPtr + 24) old24 ∗
      pointsTo_u32 0 (stackPtr + 28) old28 ∗
      pointsTo_u64 0 (result + 0) oldResultPair ∗
      pointsTo_u32 0 (result + 8) oldResultLen ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        globalPointsToAt 0 0 (.i32 (stackPtr + 32)) -∗
        pointsTo_u32 0 result 0 -∗
        pointsTo_u32 0 (result + 4) 1 -∗
        pointsTo_u32 0 (result + 8) 0 -∗
        ∀ finalLocals : Locals,
        WP (.running
          ⟨finalLocals, [], arity, remainder, controls, calls⟩ : Expr α)
            @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨func6Locals result source 0 stackPtr source 0 0 0 0,
          Project.HexStdio.func6.drop 16, arity, remainder, controls, calls⟩ :
          Expr α) @ s; E [{ Φ }] := by
  obtain ⟨p16, p17, p18, p19⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 16 (by omega)
  obtain ⟨p20, p21, p22, p23⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 20 (by omega)
  obtain ⟨p24, p25, p26, p27⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 24 (by omega)
  obtain ⟨p28, p29, p30, p31⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 28 (by omega)
  have hiter : (stackPtr + 16).toNat + 12 < UInt32.size := by
    have hs16 : (stackPtr + UInt32.ofNat 16).toNat =
        stackPtr.toNat + 16 := by
      simpa using UInt32.add_ofNat_toNat_noWrap stackPtr 16 (by decide) (by
        norm_num [UInt32.size] at hstack ⊢
        omega)
    rw [show (16 : UInt32) = UInt32.ofNat 16 by rfl, hs16]
    omega
  iintro ⟨Hruntime, Hglobal, Hcap, HoutputPtr, Hlength, H16, H20, H24, H28,
    HresultPair, HresultLen, Hpost⟩
  rw [func6_drop16_eq]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old28 p28 p29 p30 p31 $$ H28
  iintro HtablePtr
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old24 p24 p25 p26 p27 $$ H24
  iintro Hend
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old20 p20 p21 p22 p23 $$ H20
  iintro Hcursor
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old16 p16 p17 p18 p19 $$ H16
  iintro Hcurrent
  iapply twp_block
  rw [Project.HexEncodeStdio.TotalEncodeLoop.encodeOuterBody_eq]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  simp only [UInt32.add_comm (16 : UInt32) stackPtr]
  iapply Project.HexEncodeStdio.TotalIterator.twp_call_func18_end (stackPtr + 16) source hiter
    (callerLocals := func6Locals result source 0 stackPtr source 0 0 0 0)
    (stack := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hcursor]
  · rw [show stackPtr + 16 + 4 = stackPtr + 20 by bv_decide]
    iexact Hcursor
  isplitl [Hend]
  · rw [show stackPtr + 16 + 8 = stackPtr + 24 by bv_decide]
    iexact Hend
  iintro Hruntime Hcurrent Hcursor Hend
  iapply twp_localTee rfl
  iapply twp_const
  iapply Project.HexEncodeStdio.TotalIterator.twp_eq (result := 1)
    (by simp [Project.HexEncodeStdio.TotalIterator.sentinel])
  iapply twp_brIf (by decide) rfl
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  simp only [func6Locals, List.set]
  iapply func6_finish result source Project.HexEncodeStdio.TotalIterator.sentinel stackPtr
    source 0 0 0 0 0 1 [] oldResultPair oldResultLen hstack hresult
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hcap]
  · iexact Hcap
  isplitl [HoutputPtr]
  · iexact HoutputPtr
  isplitl [Hlength]
  · iexact Hlength
  isplitl [HresultPair]
  · iexact HresultPair
  isplitl [HresultLen]
  · iexact HresultLen
  iintro Hglobal HcapResult HptrResult HlenResult
  ispecialize Hpost $$ Hruntime Hglobal HcapResult HptrResult HlenResult
  ispecialize Hpost $$ %(func6Locals result source
    Project.HexEncodeStdio.TotalIterator.sentinel stackPtr source 0 0 0 0)
  iexact Hpost

end Project.HexEncodeStdio.TotalEncodeFunction
