import Project.Mergesort.FormatProof
import Project.Mergesort.VectorProof

/-!
# Generated empty `String` constructor

The exported driver calls local `func110` to construct an empty String.  The
generated three-word layout is `(capacity = 0, data = 1, length = 0)`.
-/

namespace Project.Mergesort.StringProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.SplitAtProof
open Project.Mergesort.FormatProof
open Project.Mergesort.VectorProof

private def stringNewParams (resultPtr : UInt32) : List Value :=
  [.i32 resultPtr]

/-- Exact total body rule for generated local `func110`. -/
theorem stringNew_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr stackTop : UInt32)
    (oldFrame4 oldFrame8 oldFrame12 : UInt32)
    (oldResult0 oldResult4 oldResult8 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 4) oldFrame4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo_u32 (resultPtr + 8) oldResult8 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        sliceDescriptorAt ((stackTop - 16) + 4) 0 1 -∗
        pointsTo_u32 ((stackTop - 16) + 12) 0 -∗
        vecDescriptorAt resultPtr 0 1 0 -∗
        WP (.running
          ⟨⟨stringNewParams resultPtr, [.i32 (stackTop - 16)], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨stringNewParams resultPtr, [.i32 0], []⟩,
        func110, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts frame 4 16 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 16 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 16 hframeRoom (by decide)
  obtain ⟨hfw0, hfw1, hfw2, hfw3, hfw4, hfw5, hfw6, hfw7⟩ :=
    descriptorSlot64Facts frame 4 16 hframeRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    descriptorSlot32Facts resultPtr 8 12 hresultRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
    descriptorSlot64Facts resultPtr 0 12 hresultRoom (by decide)
  iintro ⟨Hglobal, Hframe4, Hframe8, Hframe12,
    Hresult0, Hresult4, Hresult8, Hdone⟩
  simp only [func110]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame4 hf40 hf41 hf42 hf43 $$ Hframe4
  iintro Hframe4
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame8 hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame12 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 0 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_store32 oldResult8 hr80 hr81 hr82 hr83 $$ Hresult8
  iintro Hresult8
  ihave HframeWord : pointsTo_u64 (frame + 4) (packU32 0 1) $$
      [Hframe4 Hframe8]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 4) 0 1).mp
    simp only [sliceDescriptorAt]
    isplitl [Hframe4]
    · iexact Hframe4
    · rw [show (frame + 4) + 4 = frame + 8 by bv_decide]
      iexact Hframe8
  ihave HresultWord : pointsTo_u64 (resultPtr + 0)
      (packU32 oldResult0 oldResult4) $$ [Hresult0 Hresult4]
  · iapply (sliceDescriptorAt_eq_u64 (resultPtr + 0)
      oldResult0 oldResult4).mp
    simp only [sliceDescriptorAt]
    rw [UInt32.add_zero]
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 0 1)
    hfw0 hfw1 hfw2 hfw3 hfw4 hfw5 hfw6 hfw7 $$ HframeWord
  iintro HframeWord
  iapply twp_store64 (packU32 oldResult0 oldResult4)
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 $$ HresultWord
  iintro HresultWord
  simp [stringNewParams, frame]
  ihave HframeDesc : sliceDescriptorAt (frame + 4) 0 1 $$ [HframeWord]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 4) 0 1).mpr
    iexact HframeWord
  ihave HresultDesc : sliceDescriptorAt resultPtr 0 1 $$ [HresultWord]
  · iapply (sliceDescriptorAt_eq_u64 resultPtr 0 1).mpr
    rw [show resultPtr = resultPtr + 0 by bv_decide]
    iexact HresultWord
  ihave Hvec : vecDescriptorAt resultPtr 0 1 0 $$
      [HresultDesc Hresult8]
  · simp only [vecDescriptorAt, sliceDescriptorAt] at *
    iframe
  iapply Hdone $$ Hglobal HframeDesc Hframe12 Hvec

/-- Composable absolute-index-112 call rule for generated `func110`. -/
theorem stringNew_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr stackTop : UInt32)
    (oldFrame4 oldFrame8 oldFrame12 : UInt32)
    (oldResult0 oldResult4 oldResult8 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 4) oldFrame4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo_u32 (resultPtr + 8) oldResult8 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        sliceDescriptorAt ((stackTop - 16) + 4) 0 1 -∗
        pointsTo_u32 ((stackTop - 16) + 12) 0 -∗
        vecDescriptorAt resultPtr 0 1 0 -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 resultPtr :: stack },
        .call 112 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe4, Hframe8, Hframe12,
    Hresult0, Hresult4, Hresult8, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 112 func110Def
      (by decide) stringNew_index $$ Hruntime
  iintro Hruntime
  simp [func110Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := stringNew_body_twp (α := α)
    resultPtr stackTop oldFrame4 oldFrame8 oldFrame12
    oldResult0 oldResult4 oldResult8 hframeRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [stringNewParams] at Hbody
  ihave Hresult0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hresult0]
  · rw [UInt32.add_zero]
    iexact Hresult0
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [Hresult0At]
  · iexact Hresult0At
  isplitl [Hresult4]
  · iexact Hresult4
  isplitl [Hresult8]
  · iexact Hresult8
  iintro Hglobal HframeDesc Hframe12 Hvec
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal HframeDesc Hframe12 Hvec

end Project.Mergesort.StringProof
