import Project.Mergesort.FormatProof

/-!
# Generated buffered-format writer

The output loop reaches generated local `func33` at absolute index 35.  This
file verifies that large formatter bottom-up.  The first contract covers the
exact 32-byte shadow-frame prologue and stops at its first nested call
(absolute index 36), keeping that formatter dependency explicit.
-/

namespace Project.Mergesort.WriteFmtProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.RangeProof
open Project.Mergesort.FormatProof

def writeFmtAtPrepare : Program := func33.drop 18
def writeFmtAfterPrepare : Program := func33.drop 19

def writeFmtParams
    (resultPtr writerPtr formatPtr argumentsPtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 writerPtr, .i32 formatPtr, .i32 argumentsPtr]

def writeFmtLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0]

theorem writeFmtAtPrepare_eq :
    writeFmtAtPrepare = .call 36 :: writeFmtAfterPrepare := by
  rfl

/-! Exact generated prologue of local `func33`, through both saved argument
stores and both operands for absolute call 36. -/
theorem writeFmt_to_prepare_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writerPtr formatPtr argumentsPtr stackTop : UInt32)
    (oldFormat oldArguments : UInt32)
    (hframeRoom : (stackTop - 32).toNat + 24 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 16) oldFormat ∗
      pointsTo_u32 ((stackTop - 32) + 20) oldArguments ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        pointsTo_u32 ((stackTop - 32) + 16) formatPtr -∗
        pointsTo_u32 ((stackTop - 32) + 20) argumentsPtr -∗
        WP (.running
          ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
              writeFmtLocals (stackTop - 32),
              [.i32 ((stackTop - 32) + 16),
               .i32 ((stackTop - 32) + 8)]⟩,
            writeFmtAtPrepare, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
          [.i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func33, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let frame := stackTop - 32
  obtain ⟨h160, h161, h162, h163⟩ :=
    descriptorSlot32Facts frame 16 24 hframeRoom (by decide)
  obtain ⟨h200, h201, h202, h203⟩ :=
    descriptorSlot32Facts frame 20 24 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hformat, Harguments, Hdone⟩
  simp only [func33]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [writeFmtParams, List.length, Nat.sub_self, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFormat h160 h161 h162 h163 $$ Hformat
  iintro Hformat
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldArguments h200 h201 h202 h203 $$ Harguments
  iintro Harguments
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 8 frame]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 16 frame]
  isimp only [writeFmtParams, writeFmtLocals, writeFmtAtPrepare, func33,
    List.drop] at Hdone
  iapply Hdone $$ Hruntime Hglobal Hformat Harguments

/-! Absolute-index-35 entry rule, composable from the generated driver.  It
enters `func33`, runs the proved prologue, and exposes the exact callee state
at absolute call 36. -/
theorem writeFmt_call_to_prepare_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writerPtr formatPtr argumentsPtr stackTop : UInt32)
    (oldFormat oldArguments : UInt32)
    (hframeRoom : (stackTop - 32).toNat + 24 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 16) oldFormat ∗
      pointsTo_u32 ((stackTop - 32) + 20) oldArguments ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        pointsTo_u32 ((stackTop - 32) + 16) formatPtr -∗
        pointsTo_u32 ((stackTop - 32) + 20) argumentsPtr -∗
        WP (.running
          ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
              writeFmtLocals (stackTop - 32),
              [.i32 ((stackTop - 32) + 16),
               .i32 ((stackTop - 32) + 8)]⟩,
            writeFmtAtPrepare, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 argumentsPtr, .i32 formatPtr, .i32 writerPtr,
           .i32 resultPtr] ++ stack },
        .call 35 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hformat, Harguments, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 35 func33Def
      (by decide) writeFmt_index $$ Hruntime
  iintro Hruntime
  simp [func33Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := writeFmt_to_prepare_call_twp (α := α)
    resultPtr writerPtr formatPtr argumentsPtr stackTop
    oldFormat oldArguments hframeRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [writeFmtParams] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hformat]
  · iexact Hformat
  isplitl [Harguments]
  · iexact Harguments
  iintro Hruntime Hglobal Hformat Harguments
  isimp only [writeFmtParams] at Hdone
  iapply Hdone $$ Hruntime Hglobal Hformat Harguments

end Project.Mergesort.WriteFmtProof
