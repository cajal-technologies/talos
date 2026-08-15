import Project.Mergesort.SplitAtProof

/-!
# Generated formatting argument helper

`func43` constructs the two-word formatting argument descriptor used by the
exported output loop.  Its generated body has no callees, so it is verified as
an independent leaf before the larger writer/formatter chain.
-/

namespace Project.Mergesort.FormatProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.SplitAtProof

private def argumentParams (resultPtr valuePtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 valuePtr]

theorem descriptorSlot32Facts (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 4 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega)⟩

theorem descriptorSlot64Facts (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 8 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 ∧
    ((base + UInt32.ofNat offset) + 4).toNat =
      (base + UInt32.ofNat offset).toNat + 4 ∧
    ((base + UInt32.ofNat offset) + 5).toNat =
      (base + UInt32.ofNat offset).toNat + 5 ∧
    ((base + UInt32.ofNat offset) + 6).toNat =
      (base + UInt32.ofNat offset).toNat + 6 ∧
    ((base + UInt32.ofNat offset) + 7).toNat =
      (base + UInt32.ofNat offset).toNat + 7 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 7) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega),
    by simpa using hstep 4 (by omega), by simpa using hstep 5 (by omega),
    by simpa using hstep 6 (by omega), by simpa using hstep 7 (by omega)⟩

/-- Exact total body rule for generated local `func43`. -/
theorem displayArgument_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr valuePtr stackTop : UInt32)
    (oldFrame8 oldFrame12 oldResult0 oldResult4 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        sliceDescriptorAt ((stackTop - 16) + 8) valuePtr 1 -∗
        sliceDescriptorAt resultPtr valuePtr 1 -∗
        WP (.running
          ⟨⟨argumentParams resultPtr valuePtr, [.i32 (stackTop - 16)], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨argumentParams resultPtr valuePtr, [.i32 0], []⟩,
        func43, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 16 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 16 hframeRoom (by decide)
  obtain ⟨hfw0, hfw1, hfw2, hfw3, hfw4, hfw5, hfw6, hfw7⟩ :=
    descriptorSlot64Facts frame 8 16 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
    descriptorSlot64Facts resultPtr 0 8 hresultRoom (by decide)
  iintro ⟨Hglobal, Hframe8, Hframe12, Hresult0, Hresult4, Hdone⟩
  simp only [func43]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFrame8 hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame12 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  ihave HframeWord : pointsTo_u64 (frame + 8) (packU32 valuePtr 1) $$
      [Hframe8 Hframe12]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 8) valuePtr 1).mp
    simp only [sliceDescriptorAt]
    isplitl [Hframe8]
    · iexact Hframe8
    · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
      iexact Hframe12
  ihave HresultWord : pointsTo_u64 (resultPtr + 0)
      (packU32 oldResult0 oldResult4) $$ [Hresult0 Hresult4]
  · iapply (sliceDescriptorAt_eq_u64 (resultPtr + 0)
      oldResult0 oldResult4).mp
    simp only [sliceDescriptorAt]
    rw [UInt32.add_zero]
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 valuePtr 1)
    hfw0 hfw1 hfw2 hfw3 hfw4 hfw5 hfw6 hfw7 $$ HframeWord
  iintro HframeWord
  iapply twp_store64 (packU32 oldResult0 oldResult4)
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 $$ HresultWord
  iintro HresultWord
  simp [argumentParams, frame]
  ihave HframeDesc : sliceDescriptorAt (frame + 8) valuePtr 1 $$ [HframeWord]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 8) valuePtr 1).mpr
    iexact HframeWord
  ihave HresultDesc : sliceDescriptorAt resultPtr valuePtr 1 $$ [HresultWord]
  · iapply (sliceDescriptorAt_eq_u64 resultPtr valuePtr 1).mpr
    rw [show resultPtr = resultPtr + 0 by bv_decide]
    iexact HresultWord
  iapply Hdone $$ Hglobal HframeDesc HresultDesc

/-- Composable absolute-index-45 call rule for generated `func43`. -/
theorem displayArgument_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr valuePtr stackTop : UInt32)
    (oldFrame8 oldFrame12 oldResult0 oldResult4 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        sliceDescriptorAt ((stackTop - 16) + 8) valuePtr 1 -∗
        sliceDescriptorAt resultPtr valuePtr 1 -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 valuePtr, .i32 resultPtr] ++ stack },
        .call 45 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe8, Hframe12, Hresult0, Hresult4,
    Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 45 func43Def
      (by decide) displayArgument_index $$ Hruntime
  iintro Hruntime
  simp [func43Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := displayArgument_body_twp (α := α)
    resultPtr valuePtr stackTop oldFrame8 oldFrame12 oldResult0 oldResult4
    hframeRoom hresultRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [argumentParams] at Hbody
  ihave Hresult0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hresult0]
  · rw [UInt32.add_zero]
    iexact Hresult0
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [Hresult0At]
  · iexact Hresult0At
  isplitl [Hresult4]
  · iexact Hresult4
  iintro Hglobal HframeDesc HresultDesc
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal HframeDesc HresultDesc

end Project.Mergesort.FormatProof
