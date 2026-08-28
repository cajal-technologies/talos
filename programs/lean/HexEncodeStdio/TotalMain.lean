import HexEncodeStdio.TotalWrite
import HexEncodeStdio.HDAllocator
import HexEncodeStdio.Helpers

namespace Project.HexEncodeStdio.TotalMain

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private abbrev mainLocals (sp inputPtr outputPtr outputCap : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[], [.i32 sp, .i32 inputPtr, .i32 outputPtr, .i32 outputCap], values⟩

/-- Frame-preserving presentation of the already-proved writer contract. -/
private theorem twp_call_func8_nonempty_frame {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (ptr length stackPtr : UInt32) (bytes : List UInt8)
    (host : Universal.State) (oldTag : UInt8) (oldLength : UInt32)
    (hlen : length.toNat = bytes.length) (hpos : 0 < bytes.length)
    (hptr : ptr.toNat + bytes.length < UInt32.size)
    (hstack : stackPtr.toNat + 16 < UInt32.size)
    (R : IProp (WasmHeapGF Universal.State))
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    R ∗ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗ globalPointsToAt 0 0 (.i32 (stackPtr + 16)) ∗
      pointsToBytes 0 ptr bytes ∗ (⟨0, stackPtr⟩ ↦w oldTag) ∗
      pointsTo_u32 0 (stackPtr + 4) oldLength ∗
      (R ∗ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (Project.HexEncodeStdio.TotalWrite.afterWrite host bytes) -∗
        globalPointsToAt 0 0 (.i32 (stackPtr + 16)) -∗
        pointsToBytes 0 ptr bytes -∗ (⟨0, stackPtr⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (stackPtr + 4) length -∗
        WP (.running ⟨{ callerLocals with values := stack }, code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨{ callerLocals with values := .i32 length :: .i32 ptr :: stack },
          .call 11 :: code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro Hpre
  icases Hpre with ⟨HR, Hpre⟩
  icases Hpre with ⟨Hruntime, Hpre⟩
  icases Hpre with ⟨Henv, Hpre⟩
  icases Hpre with ⟨Hhost, Hpre⟩
  icases Hpre with ⟨Hglobal, Hpre⟩
  icases Hpre with ⟨Hbytes, Hpre⟩
  icases Hpre with ⟨Htag, Hpre⟩
  icases Hpre with ⟨Hlength, Hnext⟩
  ihave Hcont :
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (Project.HexEncodeStdio.TotalWrite.afterWrite host bytes) -∗
        globalPointsToAt 0 0 (.i32 (stackPtr + 16)) -∗
        pointsToBytes 0 ptr bytes -∗ (⟨0, stackPtr⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (stackPtr + 4) length -∗
        WP (.running ⟨{ callerLocals with values := stack }, code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) $$ [HR Hnext]
  · iintro Hruntime Henv Hhost Hglobal Hbytes Htag Hlength
    iapply Hnext $$ [$HR $Hruntime] Henv Hhost Hglobal Hbytes Htag Hlength
  iapply Project.HexEncodeStdio.TotalWrite.twp_call_func8_nonempty ptr length stackPtr
      bytes host oldTag oldLength hlen hpos hptr hstack $$
    [$Hruntime $Henv $Hhost $Hglobal $Hbytes $Htag $Hlength $Hcont]

/-- Successful suffix of the exported encoder, beginning immediately after
`func6` has published the encoded vector.  It writes the full output, runs
both no-op deallocations, restores the stack pointer, and returns. -/
theorem func10_after_encode_nonempty {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (sp inputPtr inputCapacity outputPtr outputCapacity : UInt32)
    (input encoded : List UInt8) (host : Universal.State)
    (oldWriteTag : UInt8) (oldWriteLength : UInt32)
    (hencoded : encoded = Project.HexStdio.Spec.encode input)
    (hinputPos : 0 < input.length)
    (houtputLen : (UInt32.ofNat encoded.length).toNat = encoded.length)
    (houtputPos : 0 < encoded.length)
    (houtputPtr : outputPtr.toNat + encoded.length < UInt32.size)
    (hmainStack : sp.toNat + 32 < UInt32.size)
    (hwriteStack : (sp - 16).toNat + 16 < UInt32.size)
    (houtputCapacity : outputCapacity ≠ 0)
    (hinputCapacity : inputCapacity ≠ 0) :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u32 0 (sp + 8) outputCapacity ∗
      pointsTo_u32 0 (sp + 12) outputPtr ∗
      pointsTo_u32 0 (sp + 16) (UInt32.ofNat encoded.length) ∗
      pointsTo_u32 0 (sp + 20) inputCapacity ∗
      pointsTo_u32 0 (sp + 24) inputPtr ∗
      pointsTo_u32 0 (sp + 28) (UInt32.ofNat input.length) ∗
      pointsToBytes 0 inputPtr input ∗
      pointsToBytes 0 outputPtr encoded ∗
      (⟨0, sp - 16⟩ ↦w oldWriteTag) ∗
      pointsTo_u32 0 ((sp - 16) + 4) oldWriteLength -∗
    (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
      hostStateOwn (Project.HexEncodeStdio.TotalWrite.afterWrite host encoded) -∗
      globalPointsToAt 0 0 (.i32 (sp + 32)) -∗
      WP (.running ⟨mainLocals sp inputPtr inputCapacity outputCapacity,
          [], 0, [], [], []⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨mainLocals sp inputPtr 0 0,
        Project.HexStdio.func10.drop 18, 0, [], [], []⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hglobal, HoutputCapacityMem, HoutPtr, HoutLen,
    HinputCap, HinputPtr, HinputLen, Hinput, Hencoded, HwriteTag,
    HwriteLength⟩ Hnext
  simp only [Project.HexStdio.func10, List.drop_succ_cons, List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_load32 outputPtr
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 12 (by omega)).1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 12 (by omega)).2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 12 (by omega)).2.2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 12 (by omega)).2.2.2 $$ HoutPtr
  iintro HoutPtr
  iapply twp_localTee rfl
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat encoded.length)
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 16 (by omega)).1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 16 (by omega)).2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 16 (by omega)).2.2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 16 (by omega)).2.2.2 $$ HoutLen
  iintro HoutLen
  simp [mainLocals, List.set]
  ihave HglobalWrite : globalPointsToAt 0 0 (.i32 ((sp - 16) + 16)) $$ [Hglobal]
  · rw [show sp - 16 + 16 = sp by bv_decide]
    iexact Hglobal
  let R : IProp (WasmHeapGF Universal.State) := iprop(
      pointsTo_u32 0 (sp + 8) outputCapacity ∗
      pointsTo_u32 0 (sp + 12) outputPtr ∗
      pointsTo_u32 0 (sp + 16) (UInt32.ofNat encoded.length) ∗
      pointsTo_u32 0 (sp + 20) inputCapacity ∗
      pointsTo_u32 0 (sp + 24) inputPtr ∗
      pointsTo_u32 0 (sp + 28) (UInt32.ofNat input.length) ∗
      pointsToBytes 0 inputPtr input ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (Project.HexEncodeStdio.TotalWrite.afterWrite host encoded) -∗
        globalPointsToAt 0 0 (.i32 (sp + 32)) -∗
        WP (.running ⟨mainLocals sp inputPtr inputCapacity outputCapacity,
          [], 0, [], [], []⟩ : Expr Universal.State) @ s; E [{ Φ }]))
  ihave HR : R $$ [HoutputCapacityMem HoutPtr HoutLen HinputCap HinputPtr
      HinputLen Hinput Hnext]
  · unfold R
    iframe
  iapply twp_call_func8_nonempty_frame outputPtr
      (UInt32.ofNat encoded.length) (sp - 16) encoded host oldWriteTag
      oldWriteLength houtputLen houtputPos houtputPtr hwriteStack
      R
      (callerLocals := ⟨[], [.i32 sp, .i32 inputPtr, .i32 outputPtr, .i32 0], []⟩)
      (stack := []) $$
      [$HR $Hruntime $Henv $Hhost $HglobalWrite $Hencoded $HwriteTag
        $HwriteLength]
  iintro ⟨HRret, HruntimeAfterWrite⟩ Henv Hhost Hglobal Hencoded HwriteTag
    HwriteLength
  isimp only [R] at HRret
  icases HRret with ⟨HoutputCapacityMem, HoutPtr, HoutLen, HinputCap,
    HinputPtr, HinputLen, Hinput, Hnext⟩
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 outputCapacity
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 8 (by omega)).1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 8 (by omega)).2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 8 (by omega)).2.2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 8 (by omega)).2.2.2 $$
      HoutputCapacityMem
  iintro HoutCapLoaded
  iapply twp_localTee rfl
  iapply twp_eqz rfl
  simp [houtputCapacity, mainLocals, List.set]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  let outFrame : ControlFrame :=
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := [.localGet 0, .load32 8, .localTee 3, .eqz, .br_if 0,
        .localGet 2, .localGet 3, .const 1, .call 17]
      continuation := Project.HexStdio.func10.drop 25
      belowStack := [] }
  have hdealloc := Project.HexEncodeStdio.twp_dealloc_noop
      (s := s) (E := E) (Φ := Φ) outputPtr outputCapacity 1
      (⟨[], [.i32 sp, .i32 inputPtr, .i32 outputPtr, .i32 outputCapacity], []⟩)
      [] [] 0 []
      ({ kind := .block
         paramArity := 0
         resultArity := 0
         body := [.localGet 0, .load32 8, .localTee 3, .eqz, .br_if 0,
           .localGet 2, .localGet 3, .const 1, .call 17]
         continuation := Project.HexStdio.func10.drop 25
         belowStack := [] } :: []) []
  simp only [List.append_nil, Project.HexStdio.func10, List.drop_succ_cons,
    List.drop_zero] at hdealloc
  iapply hdealloc $$ HruntimeAfterWrite
  iintro HruntimeAfterDealloc
  iapply twp_exitControl rfl
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 inputCapacity
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 20 (by omega)).1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 20 (by omega)).2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 20 (by omega)).2.2.1
      (Project.HexEncodeStdio.Helpers.wordAccessFacts sp 20 (by omega)).2.2.2 $$
      HinputCap
  iintro HinputCapLoaded
  iapply twp_localTee rfl
  iapply twp_eqz rfl
  simp [hinputCapacity, List.set]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  have hdeallocInput := Project.HexEncodeStdio.twp_dealloc_noop
      (s := s) (E := E) (Φ := Φ) inputPtr inputCapacity 1
      (⟨[], [.i32 sp, .i32 inputPtr, .i32 inputCapacity, .i32 outputCapacity], []⟩)
      [] [] 0 []
      ({ kind := .block
         paramArity := 0
         resultArity := 0
         body := [.localGet 0, .load32 20, .localTee 2, .eqz, .br_if 0,
           .localGet 1, .localGet 2, .const 1, .call 17]
         continuation := Project.HexStdio.func10.drop 26
         belowStack := [] } :: []) []
  simp only [List.append_nil, Project.HexStdio.func10, List.drop_succ_cons,
    List.drop_zero] at hdeallocInput
  iapply hdeallocInput $$ HruntimeAfterDealloc
  iintro HruntimeAfterInputDealloc
  iapply twp_exitControl rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  ihave Hglobal' : globalPointsToAt 0 0 (.i32 (sp + 32)) $$ [Hglobal]
  · rw [UInt32.add_comm]
    iexact Hglobal
  simp [mainLocals]
  iapply Hnext $$ HruntimeAfterInputDealloc Henv Hhost Hglobal'

end Project.HexEncodeStdio.TotalMain
