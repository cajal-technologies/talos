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
open Project.Mergesort.Machine

private theorem twp_eq
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .eq :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.eq hresult)

def writeFmtAtPrepare : Program := func33.drop 18
def writeFmtAfterPrepare : Program := func33.drop 19

def writeFmtParams
    (resultPtr writerPtr formatPtr argumentsPtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 writerPtr, .i32 formatPtr, .i32 argumentsPtr]

def writeFmtLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0]

def formatPrepareOuterBody : Program :=
  match func34.drop 7 with
  | .block _ _ body :: _ => body
  | _ => []

def formatPrepareAfterOuter : Program := func34.drop 8

def formatPrepareLocals (frame second : UInt32) : List Value :=
  [.i32 frame, .i32 second, .i32 0, .i32 0, .i32 0,
   .i32 0, .i32 0, .i32 0, .i32 0]

def formatPrepareOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := formatPrepareOuterBody
    continuation := formatPrepareAfterOuter
    belowStack := [] }

def formatPrepareMiddleBody : Program :=
  match formatPrepareOuterBody with
  | .block _ _ body :: _ => body
  | _ => []

def formatPrepareAfterMiddle : Program := formatPrepareOuterBody.drop 1

def formatPrepareInnerBody : Program :=
  match formatPrepareMiddleBody with
  | .block _ _ body :: _ => body
  | _ => []

def formatPrepareStaticPath : Program := formatPrepareMiddleBody.drop 1

def formatPrepareMiddleFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := formatPrepareMiddleBody
    continuation := formatPrepareAfterMiddle
    belowStack := [] }

theorem writeFmtAtPrepare_eq :
    writeFmtAtPrepare = .call 36 :: writeFmtAfterPrepare := by
  rfl

theorem formatPrepare_at_outer_eq :
    func34.drop 7 =
      .block 0 0 formatPrepareOuterBody :: formatPrepareAfterOuter := by
  rfl

theorem formatPrepare_outer_shape :
    formatPrepareOuterBody =
      .block 0 0 formatPrepareMiddleBody :: formatPrepareAfterMiddle := by
  rfl

theorem formatPrepare_middle_shape :
    formatPrepareMiddleBody =
      .block 0 0 formatPrepareInnerBody :: formatPrepareStaticPath := by
  rfl

theorem formatPrepare_inner_shape :
    formatPrepareInnerBody =
      [.localGet 3, .const 1, .and, .const 1, .eq, .const 1, .and,
       .eqz, .br_if 0, .localGet 1, .load32 0, .localSet 4,
       .localGet 3, .const 1, .shrU, .localSet 5, .br 1] := by
  rfl

/-! Exact prefix of local `func34` (absolute 36).  It computes the 16-byte
scratch address, reads the second input word, and enters the generated outer
control block without interpreting either representation branch yet. -/
theorem formatPrepare_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr stackTop second : UInt32)
    (hinputRoom : inputPtr.toNat + 8 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (inputPtr + 4) second ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (inputPtr + 4) second -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 inputPtr],
              formatPrepareLocals (stackTop - 16) second, []⟩,
            formatPrepareOuterBody, 0, [],
            formatPrepareOuterFrame :: controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 inputPtr],
          List.replicate 9 (.i32 0), []⟩,
        func34, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts inputPtr 4 8 hinputRoom (by decide)
  iintro ⟨Hglobal, Hsecond, Hdone⟩
  simp only [func34]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.replicate_succ, List.replicate_zero, List.set,
    List.length, Nat.sub_self]
  iapply twp_localGet rfl
  iapply twp_load32 second h40 h41 h42 h43 $$ Hsecond
  iintro Hsecond
  iapply twp_localSet rfl
  simp only [List.length, List.set]
  iapply twp_block
  simp only [List.drop_zero]
  isimp only [formatPrepareLocals, formatPrepareOuterBody,
    formatPrepareOuterFrame, formatPrepareAfterOuter, func34, List.drop] at Hdone
  iapply Hdone $$ Hglobal Hsecond

/-! The driver passes an aligned argument pointer as the second word.  This
exact pure-control rule follows the generated low-bit test through its two
nested blocks and lands at the static fallback loads. -/
theorem formatPrepare_aligned_dispatch_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr frame second : UInt32)
    (heven : second &&& 1 = 0)
    {R : IProp WasmHeapGF}
    {controls : List ControlFrame} {calls : List CallFrame} :
    R ∗
      (R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 inputPtr],
              formatPrepareLocals frame second, []⟩,
            formatPrepareStaticPath, 0, [],
            formatPrepareMiddleFrame :: formatPrepareOuterFrame :: controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 inputPtr],
          formatPrepareLocals frame second, []⟩,
        formatPrepareOuterBody, 0, [],
        formatPrepareOuterFrame :: controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [formatPrepareLocals, formatPrepareMiddleFrame,
    formatPrepareOuterFrame, formatPrepareMiddleBody,
    formatPrepareStaticPath, formatPrepareAfterMiddle,
    formatPrepareAfterOuter, formatPrepareOuterBody, func34, List.drop]
  iintro ⟨HR, Hdone⟩
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [heven]
  iapply twp_const
  iapply twp_eq (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (value := 0) (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ HR

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
