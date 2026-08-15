import Project.Mergesort.RangeProof

/-!
# Generated `IntoIter<u64>` helpers

`func6` computes the exact remaining length of the generated iterator from
its current and end pointers.  It is a leaf used by collection/formatting and
is proved here independently of allocation and element traversal.
-/

namespace Project.Mergesort.IteratorProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof

def iteratorRemaining (current finish : UInt32) : UInt32 :=
  (finish - current) >>> (3 % 32)

private def intoIterLenParams (resultPtr iterPtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 iterPtr]

private def intoIterLenZeroLocals : List Value :=
  [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

private def intoIterLenFinalLocals
    (frame current finish : UInt32) : List Value :=
  [.i32 frame, .i32 finish, .i32 current,
    .i32 (iteratorRemaining current finish),
    .i32 (iteratorRemaining current finish)]

private theorem slot32Facts (base : UInt32) (offset total : Nat)
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

private theorem pointsTo_u32_add_zero
    [WasmHeapGS] (address value : UInt32) :
    pointsTo_u32 (address + 0) value ⊢ pointsTo_u32 address value := by
  rw [UInt32.add_zero]

/-- Exact total body rule for local `func6`. -/
theorem intoIterLen_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iterPtr current finish stackTop : UInt32)
    (oldFrame oldResult0 oldResult4 oldResult8 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hiterRoom : iterPtr.toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame ∗
      pointsTo_u32 (iterPtr + 4) current ∗
      pointsTo_u32 (iterPtr + 12) finish ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo_u32 (resultPtr + 8) oldResult8 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 12)
          (iteratorRemaining current finish) -∗
        pointsTo_u32 (iterPtr + 4) current -∗
        pointsTo_u32 (iterPtr + 12) finish -∗
        pointsTo_u32 (resultPtr + 0)
          (iteratorRemaining current finish) -∗
        pointsTo_u32 (resultPtr + 4) 1 -∗
        pointsTo_u32 (resultPtr + 8)
          (iteratorRemaining current finish) -∗
        WP (.running
          ⟨⟨intoIterLenParams resultPtr iterPtr,
              intoIterLenFinalLocals (stackTop - 16) current finish, []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨intoIterLenParams resultPtr iterPtr, intoIterLenZeroLocals, []⟩,
        func6, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf0, hf1, hf2, hf3⟩ :=
    slot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  obtain ⟨hi40, hi41, hi42, hi43⟩ :=
    slot32Facts iterPtr 4 16 hiterRoom (by decide)
  obtain ⟨hi120, hi121, hi122, hi123⟩ :=
    slot32Facts iterPtr 12 16 hiterRoom (by decide)
  obtain ⟨hr00, hr01, hr02, hr03⟩ :=
    slot32Facts resultPtr 0 12 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    slot32Facts resultPtr 4 12 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    slot32Facts resultPtr 8 12 hresultRoom (by decide)
  iintro ⟨Hglobal, Hframe, Hcurrent, Hfinish, Hr0, Hr4, Hr8, Hdone⟩
  simp only [func6]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 finish hi120 hi121 hi122 hi123 $$ Hfinish
  iintro Hfinish
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 current hi40 hi41 hi42 hi43 $$ Hcurrent
  iintro Hcurrent
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_const
  iapply twp_shrU
  iapply twp_store32 oldFrame hf0 hf1 hf2 hf3 $$ Hframe
  iintro Hframe
  iapply twp_localGet rfl
  iapply twp_load32 ((finish - current) >>> (3 % 32))
    hf0 hf1 hf2 hf3 $$ Hframe
  iintro Hframe
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 ((finish - current) >>> (3 % 32))
    hf0 hf1 hf2 hf3 $$ Hframe
  iintro Hframe
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResult0 hr00 hr01 hr02 hr03 $$ Hr0
  iintro Hr0
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldResult4 hr40 hr41 hr42 hr43 $$ Hr4
  iintro Hr4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResult8 hr80 hr81 hr82 hr83 $$ Hr8
  iintro Hr8
  simp [intoIterLenParams, intoIterLenZeroLocals, intoIterLenFinalLocals,
    iteratorRemaining]
  iapply Hdone $$ Hglobal Hframe Hcurrent Hfinish Hr0 Hr4 Hr8

/-- Composable absolute-index-8 call rule for generated `func6`. -/
theorem intoIterLen_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iterPtr current finish stackTop : UInt32)
    (oldFrame oldResult0 oldResult4 oldResult8 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hiterRoom : iterPtr.toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame ∗
      pointsTo_u32 (iterPtr + 4) current ∗
      pointsTo_u32 (iterPtr + 12) finish ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo_u32 (resultPtr + 8) oldResult8 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 12)
          (iteratorRemaining current finish) -∗
        pointsTo_u32 (iterPtr + 4) current -∗
        pointsTo_u32 (iterPtr + 12) finish -∗
        pointsTo_u32 (resultPtr + 0)
          (iteratorRemaining current finish) -∗
        pointsTo_u32 (resultPtr + 4) 1 -∗
        pointsTo_u32 (resultPtr + 8)
          (iteratorRemaining current finish) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 iterPtr, .i32 resultPtr] ++ stack },
        .call 8 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe, Hcurrent, Hfinish, Hr0, Hr4, Hr8,
    Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 8 func6Def
      (by decide) intoIterLen_index $$ Hruntime
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := intoIterLen_body_twp (α := α)
    resultPtr iterPtr current finish stackTop
    oldFrame oldResult0 oldResult4 oldResult8
    hframeRoom hiterRoom hresultRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [intoIterLenParams, intoIterLenZeroLocals] at Hbody
  ihave Hr0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hr0]
  · rw [UInt32.add_zero]
    iexact Hr0
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe]
  · iexact Hframe
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hfinish]
  · iexact Hfinish
  isplitl [Hr0At]
  · iexact Hr0At
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  iintro Hglobal Hframe Hcurrent Hfinish Hr0 Hr4 Hr8
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave Hr0Plain : pointsTo_u32 resultPtr
      (iteratorRemaining current finish) $$ [Hr0]
  · iapply pointsTo_u32_add_zero
    iexact Hr0
  iapply Hdone $$ Hruntime Hglobal Hframe Hcurrent Hfinish Hr0Plain Hr4 Hr8

end Project.Mergesort.IteratorProof
