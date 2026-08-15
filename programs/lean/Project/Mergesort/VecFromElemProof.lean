import Project.Mergesort.VectorProof
import Project.Mergesort.FormatProof
import Project.Mergesort.AllocatorProof

/-!
# Generated `Vec<u64>::from_elem` call chain

The unchanged generated `func105` is a forwarding shim at absolute index 107.
Its `call 108` targets local `func106`, the actual constructor implementation;
local `func108` is a different routine at absolute index 110.

This module gives exact forwarding rules, proves the u64 zero-test leaf used by
the implementation, and isolates the implementation's exact stack-frame
prefix and zero-value dispatch segment.
-/

namespace Project.Mergesort.VecFromElemProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.VectorProof
open Project.Mergesort.RangeProof
open Project.Mergesort.FormatProof
open Project.Mergesort.AllocatorProof
open Project.Mergesort.SplitAtProof

private theorem twp_eqI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .eqI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.eqI64 hresult)

private theorem twp_constI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .constI64 value :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.constI64)

/- Exact body rule for local `func98`, the zero test selected by the
`Vec<u64>::from_elem` specialization. -/
theorem u64IsZero_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (valuePtr : UInt32) (value : UInt64) (result : UInt32)
    (hresult : result = if value = 0 then 1 else 0)
    (hroom : valuePtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u64 valuePtr value ∗
      (pointsTo_u64 valuePtr value -∗
        WP (.running
          ⟨⟨[.i32 valuePtr], [], [.i32 result]⟩,
            [.ret], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 valuePtr], [], []⟩,
        func98, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    descriptorSlot64Facts valuePtr 0 8 hroom (by decide)
  iintro ⟨Hvalue, Hdone⟩
  simp only [func98]
  iapply twp_localGet rfl
  ihave HvalueAt : pointsTo_u64 (valuePtr + 0) value $$ [Hvalue]
  · rw [UInt32.add_zero]
    iexact Hvalue
  iapply twp_load64 value h0 h1 h2 h3 h4 h5 h6 h7 $$ HvalueAt
  iintro HvalueAt
  iapply twp_constI64
  iapply twp_eqI64 hresult
  iapply twp_const
  iapply twp_and
  rw [show result &&& 1 = result by
    subst result
    split <;> decide]
  ihave Hvalue : pointsTo_u64 valuePtr value $$ [HvalueAt]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact HvalueAt
  iapply Hdone $$ Hvalue

/- Composable call rule for local `func98` at absolute index 100. -/
theorem u64IsZero_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (valuePtr : UInt32) (value : UInt64) (result : UInt32)
    (hresult : result = if value = 0 then 1 else 0)
    (hroom : valuePtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗ pointsTo_u64 valuePtr value ∗
      (runtimeModuleOwn «module» -∗ pointsTo_u64 valuePtr value -∗
        WP (.running
          ⟨{ callerLocals with values := .i32 result :: stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 valuePtr :: stack },
        .call 100 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hvalue, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 100 func98Def
      (by decide) u64IsZero_index $$ Hruntime
  iintro Hruntime
  simp [func98Def, Function.toLocals, Function.numParams]
  have Hbody := u64IsZero_body_twp (α := α) valuePtr value result
    hresult hroom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hvalue]
  · iexact Hvalue
  iintro Hvalue
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.singleton_append]
  iapply Hdone $$ Hruntime Hvalue

/- Exact stack/global prefix of local `func106`.  This checkpoint is shared by
both generated allocation/fill branches. -/
theorem vecFromElemImpl_frame_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count stackTop : UInt32) (value oldFrame16 : UInt64)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u64 ((stackTop - 48) + 16) oldFrame16 ∗
      (globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        pointsTo_u64 ((stackTop - 48) + 16) value -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 value, .i32 count],
              [.i32 (stackTop - 48), .i32 0, .i32 0, .i64 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            func106.drop 9, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i64 value, .i32 count],
          [.i32 0, .i32 0, .i32 0, .i64 0,
            .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func106, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 48
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    descriptorSlot64Facts frame 16 48 hframeRoom (by decide)
  iintro ⟨Hglobal, Hframe16, Hdone⟩
  simp only [func106]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store64 oldFrame16 h0 h1 h2 h3 h4 h5 h6 h7 $$ Hframe16
  iintro Hframe16
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.drop]
  iapply Hdone $$ Hglobal Hframe16

private def vecFromElemImplLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i64 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

private def vecFromElemImplInnerBody : Program :=
  [.localGet 3, .const 16, .add, .call 100,
    .const 1, .and, .br_if 0,
    .const 8, .localSet 4,
    .localGet 3, .const 8, .add,
    .localGet 2, .localGet 4, .localGet 4, .call 142,
    .localGet 3, .load32 12, .localSet 5,
    .localGet 3, .localGet 3, .load32 8, .store32 24,
    .localGet 3, .localGet 5, .store32 28,
    .localGet 3, .const 0, .store32 32,
    .localGet 3, .load64 16, .localSet 6,
    .localGet 3, .const 24, .add,
    .localGet 2, .localGet 6, .call 101,
    .localGet 0, .localGet 3, .load32 32, .store32 8,
    .localGet 0, .localGet 3, .load64 24, .store64 0,
    .br 1]

private def vecFromElemImplZeroAlternative : Program :=
  [.localGet 3, .const 36, .add, .localSet 7,
    .const 1, .localSet 8,
    .const 8, .localSet 9,
    .localGet 7, .localGet 2,
    .localGet 8, .const 1, .and,
    .localGet 9, .localGet 9, .call 146,
    .block 0 0
      [.localGet 3, .load32 36, .const 1, .and, .eqz, .br_if 0,
        .localGet 3, .load32 40,
        .localGet 3, .load32 44,
        .call 203, .unreachable],
    .localGet 3, .load32 40, .localSet 10,
    .localGet 3, .load32 44, .localSet 11,
    .localGet 0, .localGet 10, .store32 0,
    .localGet 0, .localGet 11, .store32 4,
    .localGet 0, .localGet 2, .store32 8]

private def vecFromElemImplOuterBody : Program :=
  [.block 0 0 vecFromElemImplInnerBody] ++
    vecFromElemImplZeroAlternative

private def vecFromElemImplEpilogue : Program :=
  [.localGet 3, .const 48, .add, .globalSet 0, .ret]

private def vecFromElemImplOuterFrame
    (params : List Value) (frame : UInt32) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := vecFromElemImplOuterBody
    continuation := vecFromElemImplEpilogue
    belowStack :=
      (⟨params, vecFromElemImplLocals frame, []⟩ : Locals).values.drop 0 }

private def vecFromElemImplInnerFrame
    (params : List Value) (frame : UInt32) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := vecFromElemImplInnerBody
    continuation := vecFromElemImplZeroAlternative
    belowStack :=
      (⟨params, vecFromElemImplLocals frame, []⟩ : Locals).values.drop 0 }

/- Exact zero-value dispatch used by the scratch-vector construction.  It
enters the two generated blocks, calls local `func98` at absolute index 100,
and takes the optimized allocation/fill alternative. -/
set_option maxHeartbeats 3000000 in
theorem vecFromElemImpl_zero_dispatch_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count frame : UInt32)
    (hframeRoom : frame.toNat + 48 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u64 (frame + 16) 0 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        pointsTo_u64 (frame + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
              vecFromElemImplLocals frame, []⟩,
            vecFromElemImplZeroAlternative, 0, [],
            [vecFromElemImplOuterFrame
              [.i32 resultPtr, .i64 0, .i32 count] frame], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
          vecFromElemImplLocals frame, []⟩,
        func106.drop 9, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let params : List Value := [.i32 resultPtr, .i64 0, .i32 count]
  obtain ⟨hf160, hf161, hf162, hf163, hf164, hf165, hf166, hf167⟩ :=
    descriptorSlot64Facts frame 16 48 hframeRoom (by decide)
  have hvalueRoom : (frame + 16).toNat + 8 ≤ UInt32.size := by
    change (frame + UInt32.ofNat 16).toNat + 8 ≤ UInt32.size
    rw [hf160]
    simp only [UInt32.size] at hframeRoom ⊢
    omega
  iintro ⟨Hruntime, Hglobal, Hvalue, Hdone⟩
  simp only [func106, List.drop]
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (16 : UInt32) frame]
  iapply u64IsZero_call_twp (α := α)
    (frame + 16) 0 1 (by simp) hvalueRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨params, vecFromElemImplLocals frame, []⟩)
    (stack := [])
    (calls := calls)
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hvalue]
  · iexact Hvalue
  iintro Hruntime Hvalue
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  isimp only [vecFromElemImplZeroAlternative,
    vecFromElemImplOuterBody, vecFromElemImplOuterFrame,
    vecFromElemImplEpilogue, func106, List.drop,
    vecFromElemImplInnerBody, List.singleton_append] at Hdone
  iapply Hdone $$ Hruntime Hglobal Hvalue

private def vecFromElemImplZeroAfterAlloc : Program :=
  vecFromElemImplZeroAlternative.drop 16

private theorem pointsTo_u32_add_zero
    [WasmHeapGS] (base value : UInt32) :
    pointsTo_u32 base value ⊢ pointsTo_u32 (base + 0) value := by
  rw [UInt32.add_zero]

/- Exact successful suffix after the zeroed allocator call returns.  The
allocator supplies the zero-filled array and the three success words in the
generated frame; this rule turns them into the final `Vec<u64>` descriptor,
restores the stack global, and reaches `ret`. -/
set_option maxHeartbeats 3000000 in
theorem vecFromElemImpl_zero_success_suffix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count frame capacity data : UInt32)
    (oldResultCapacity oldResultData oldResultLength : UInt32)
    (hframeRoom : frame.toNat + 48 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 (frame + 36) 0 ∗
      pointsTo_u32 (frame + 40) capacity ∗
      pointsTo_u32 (frame + 44) data ∗
      vecDescriptorAt resultPtr oldResultCapacity oldResultData
        oldResultLength ∗
      array64At data (List.replicate count.toNat 0) ∗
      (globalPointsTo 0 (.i32 (frame + 48)) -∗
        pointsTo_u32 (frame + 36) 0 -∗
        pointsTo_u32 (frame + 40) capacity -∗
        pointsTo_u32 (frame + 44) data -∗
        vecDescriptorAt resultPtr capacity data count -∗
        array64At data (List.replicate count.toNat 0) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
              [.i32 frame, .i32 0, .i32 0, .i64 0,
                .i32 (frame + 36), .i32 1, .i32 8,
                .i32 capacity, .i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
          [.i32 frame, .i32 0, .i32 0, .i64 0,
            .i32 (frame + 36), .i32 1, .i32 8,
            .i32 0, .i32 0], []⟩,
        vecFromElemImplZeroAfterAlloc, 0, [],
        [vecFromElemImplOuterFrame
          [.i32 resultPtr, .i64 0, .i32 count] frame], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf360, hf361, hf362, hf363⟩ :=
    descriptorSlot32Facts frame 36 48 hframeRoom (by decide)
  obtain ⟨hf400, hf401, hf402, hf403⟩ :=
    descriptorSlot32Facts frame 40 48 hframeRoom (by decide)
  obtain ⟨hf440, hf441, hf442, hf443⟩ :=
    descriptorSlot32Facts frame 44 48 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    descriptorSlot32Facts resultPtr 0 12 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 12 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    descriptorSlot32Facts resultPtr 8 12 hresultRoom (by decide)
  iintro ⟨Hglobal, Hf36, Hf40, Hf44, Hresult, Harray, Hdone⟩
  isimp only [vecDescriptorAt] at Hresult
  icases Hresult with ⟨Hr0, Hr4, Hr8⟩
  simp only [vecFromElemImplZeroAfterAlloc,
    vecFromElemImplZeroAlternative, List.drop]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 0 hf360 hf361 hf362 hf363 $$ Hf36
  iintro Hf36
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 capacity hf400 hf401 hf402 hf403 $$ Hf40
  iintro Hf40
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_load32 data hf440 hf441 hf442 hf443 $$ Hf44
  iintro Hf44
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hr0At : pointsTo_u32 (resultPtr + 0) oldResultCapacity $$ [Hr0]
  · iapply pointsTo_u32_add_zero
    iexact Hr0
  iapply twp_store32 oldResultCapacity hr0 hr1 hr2 hr3 $$ Hr0At
  iintro Hr0At
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResultData hr40 hr41 hr42 hr43 $$ Hr4
  iintro Hr4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResultLength hr80 hr81 hr82 hr83 $$ Hr8
  iintro Hr8
  iapply twp_exitControl (by rfl)
  simp only [vecFromElemImplOuterFrame, vecFromElemImplEpilogue,
    List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (48 : UInt32) frame]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave Hr0 : pointsTo_u32 resultPtr capacity $$ [Hr0At]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact Hr0At
  ihave Hresult : vecDescriptorAt resultPtr capacity data count $$
      [Hr0 Hr4 Hr8]
  · isimp only [vecDescriptorAt]
    iframe
  iapply Hdone $$ Hglobal Hf36 Hf40 Hf44 Hresult Harray

/- Pure generated setup immediately before the zeroed allocator invocation
(`call 146`, local `func144`).  `R` packages the caller's frame and result
ownership without baking allocator internals into this constructor layer. -/
theorem vecFromElemImpl_zero_allocation_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (resultPtr count frame : UInt32)
    {calls : List CallFrame} :
    R ∗
      (R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
              [.i32 frame, .i32 0, .i32 0, .i64 0,
                .i32 (frame + 36), .i32 1, .i32 8,
                .i32 0, .i32 0],
              [.i32 8, .i32 8, .i32 1, .i32 count,
                .i32 (frame + 36)]⟩,
            .call 146 :: vecFromElemImplZeroAfterAlloc,
            0, [],
            [vecFromElemImplOuterFrame
              [.i32 resultPtr, .i64 0, .i32 count] frame], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
          vecFromElemImplLocals frame, []⟩,
        vecFromElemImplZeroAlternative, 0, [],
        [vecFromElemImplOuterFrame
          [.i32 resultPtr, .i64 0, .i32 count] frame], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨HR, Hdone⟩
  simp only [vecFromElemImplZeroAlternative]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (36 : UInt32) frame]
  iapply twp_localSet rfl
  simp only [vecFromElemImplLocals, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  isimp only [vecFromElemImplZeroAfterAlloc,
    vecFromElemImplZeroAlternative, List.drop] at Hdone
  iapply Hdone $$ HR

/- Composition of the exact `func106` frame setup, u64-zero dispatch, and
allocator-argument setup.  The only remaining boundary is the allocator call
itself; its continuation is the verified success suffix above. -/
set_option maxHeartbeats 3000000 in
theorem vecFromElemImpl_zero_to_allocator_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count stackTop : UInt32) (oldFrame16 : UInt64)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u64 ((stackTop - 48) + 16) oldFrame16 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        pointsTo_u64 ((stackTop - 48) + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
              [.i32 (stackTop - 48), .i32 0, .i32 0, .i64 0,
                .i32 ((stackTop - 48) + 36), .i32 1, .i32 8,
                .i32 0, .i32 0],
              [.i32 8, .i32 8, .i32 1, .i32 count,
                .i32 ((stackTop - 48) + 36)]⟩,
            .call 146 :: vecFromElemImplZeroAfterAlloc,
            0, [],
            [vecFromElemImplOuterFrame
              [.i32 resultPtr, .i64 0, .i32 count] (stackTop - 48)],
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
          [.i32 0, .i32 0, .i32 0, .i64 0,
            .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func106, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 48
  iintro ⟨Hruntime, Hglobal, Hframe16, Hdone⟩
  have Hprefix := vecFromElemImpl_frame_prefix_twp (α := α)
    resultPtr count stackTop 0 oldFrame16 hframeRoom
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hprefix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe16]
  · iexact Hframe16
  iintro Hglobal Hframe16
  have Hdispatch := vecFromElemImpl_zero_dispatch_twp (α := α)
    resultPtr count frame hframeRoom
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  simp only [vecFromElemImplLocals, frame] at Hdispatch
  iapply Hdispatch
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe16]
  · iexact Hframe16
  iintro Hruntime Hglobal Hframe16
  let R : IProp WasmHeapGF := iprop%
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u64 (frame + 16) 0
  have Halloc := vecFromElemImpl_zero_allocation_prefix_twp (α := α)
    R resultPtr count frame (s := s) (E := E) (Φ := Φ) (calls := calls)
  simp only [vecFromElemImplLocals, frame] at Halloc
  iapply Halloc
  isplitl [Hruntime Hglobal Hframe16]
  · isimp only [R]
    iframe
  iintro HR
  isimp only [R] at HR
  icases HR with ⟨Hruntime, Hglobal, Hframe16⟩
  iapply Hdone $$ Hruntime Hglobal Hframe16

/- Absolute-index-108 call boundary for the zero-specialized implementation,
composed up to its allocator dependency. -/
set_option maxHeartbeats 3000000 in
theorem vecFromElemImpl_zero_to_allocator_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count stackTop : UInt32) (oldFrame16 : UInt64)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u64 ((stackTop - 48) + 16) oldFrame16 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        pointsTo_u64 ((stackTop - 48) + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
              [.i32 (stackTop - 48), .i32 0, .i32 0, .i64 0,
                .i32 ((stackTop - 48) + 36), .i32 1, .i32 8,
                .i32 0, .i32 0],
              [.i32 8, .i32 8, .i32 1, .i32 count,
                .i32 ((stackTop - 48) + 36)]⟩,
            .call 146 :: vecFromElemImplZeroAfterAlloc,
            0, [],
            [vecFromElemImplOuterFrame
              [.i32 resultPtr, .i64 0, .i32 count] (stackTop - 48)],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 count, .i64 0, .i32 resultPtr] ++ stack },
        .call 108 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe16, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 108 func106Def
      (by decide) vecFromElemImpl_index $$ Hruntime
  iintro Hruntime
  simp [func106Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := vecFromElemImpl_zero_to_allocator_twp (α := α)
    resultPtr count stackTop oldFrame16 hframeRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe16]
  · iexact Hframe16
  iintro Hruntime Hglobal Hframe16
  iapply Hdone $$ Hruntime Hglobal Hframe16

/- The generated `func105` body is exactly a typed forwarding call to local
`func106` (absolute index 108). -/
theorem vecFromElem_forward_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count : UInt32) (value : UInt64)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 value, .i32 count],
              [.i32 0, .i32 0, .i32 0, .i64 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            func106, 0, [], [],
            { locals := ⟨[.i32 resultPtr, .i64 value, .i32 count], [], []⟩
              continuation := [.ret]
              resultArity := 0
              callerRemainder := []
              control := [] } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i64 value, .i32 count], [], []⟩,
        func105, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Himpl⟩
  simp only [func105]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_call (α := α) «module» 108 func106Def
      (by decide) vecFromElemImpl_index $$ Hruntime
  iintro Hruntime
  simp [func106Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply Himpl $$ Hruntime

/- Absolute-index-107 forwarding rule, preserving an arbitrary caller frame. -/
theorem vecFromElem_forward_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count : UInt32) (value : UInt64)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 value, .i32 count],
              [.i32 0, .i32 0, .i32 0, .i64 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            func106, 0, [], [],
            { locals := ⟨[.i32 resultPtr, .i64 value, .i32 count], [], []⟩
              continuation := [.ret]
              resultArity := 0
              callerRemainder := []
              control := [] } ::
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 count, .i64 value, .i32 resultPtr] ++ stack },
        .call 107 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Himpl⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 107 func105Def
      (by decide) vecFromElem_index $$ Hruntime
  iintro Hruntime
  simp [func105Def, Function.toLocals, Function.numParams]
  have Hbody := vecFromElem_forward_body_twp (α := α)
    resultPtr count value (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  iapply Himpl $$ Hruntime

/- Driver-facing absolute-index-107 rule, composed through the forwarding shim
and the zero-specialized implementation up to the allocator call. -/
set_option maxHeartbeats 3000000 in
theorem vecFromElem_zero_to_allocator_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count stackTop : UInt32) (oldFrame16 : UInt64)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u64 ((stackTop - 48) + 16) oldFrame16 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        pointsTo_u64 ((stackTop - 48) + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i64 0, .i32 count],
              [.i32 (stackTop - 48), .i32 0, .i32 0, .i64 0,
                .i32 ((stackTop - 48) + 36), .i32 1, .i32 8,
                .i32 0, .i32 0],
              [.i32 8, .i32 8, .i32 1, .i32 count,
                .i32 ((stackTop - 48) + 36)]⟩,
            .call 146 :: vecFromElemImplZeroAfterAlloc,
            0, [],
            [vecFromElemImplOuterFrame
              [.i32 resultPtr, .i64 0, .i32 count] (stackTop - 48)],
            { locals := ⟨[.i32 resultPtr, .i64 0, .i32 count], [], []⟩
              continuation := [.ret]
              resultArity := 0
              callerRemainder := []
              control := [] } ::
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 count, .i64 0, .i32 resultPtr] ++ stack },
        .call 107 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe16, Hdone⟩
  have Hforward := vecFromElem_forward_call_twp (α := α)
    resultPtr count 0 (s := s) (E := E) (Φ := Φ)
    (callerLocals := callerLocals) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
  iapply Hforward
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  have Himpl := vecFromElemImpl_zero_to_allocator_twp (α := α)
    resultPtr count stackTop oldFrame16 hframeRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := ⟨[.i32 resultPtr, .i64 0, .i32 count], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Himpl
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe16]
  · iexact Hframe16
  iintro Hruntime Hglobal Hframe16
  iapply Hdone $$ Hruntime Hglobal Hframe16

/-! ## Closed scratch-vector construction on the singleton allocator path -/

private theorem size8_low_fact (count size : UInt32)
    (hsizeNat : size.toNat = 8 * count.toNat) :
    UInt32.ofNat
      ((UInt64.ofNat count.toNat * UInt64.ofNat (8 : UInt32).toNat).toNat
        % 2 ^ 32) = size := by
  have hc : count.toNat < 4294967296 := count.toNat_lt
  have hs : size.toNat < 4294967296 := size.toNat_lt
  rw [UInt64.toNat_mul,
    UInt64.toNat_ofNat_of_lt' (by omega : count.toNat < 2 ^ 64),
    UInt64.toNat_ofNat_of_lt' (by decide : (8 : UInt32).toNat < 2 ^ 64),
    show (8 : UInt32).toNat = 8 from rfl,
    Nat.mod_eq_of_lt (by omega : count.toNat * 8 < 2 ^ 64),
    show count.toNat * 8 % 2 ^ 32 = size.toNat by omega]
  exact UInt32.ofNat_toNat

private theorem size8_high_fact (count size : UInt32)
    (hsizeNat : size.toNat = 8 * count.toNat) :
    UInt32.ofNat
      (((UInt64.ofNat count.toNat * UInt64.ofNat (8 : UInt32).toNat) >>>
        ((32 : UInt64) % 64)).toNat % 2 ^ 32) = 0 := by
  have hc : count.toNat < 4294967296 := count.toNat_lt
  have hs : size.toNat < 4294967296 := size.toNat_lt
  rw [show (32 : UInt64) % 64 = 32 by decide,
    UInt64.toNat_shiftRight,
    UInt64.toNat_mul,
    UInt64.toNat_ofNat_of_lt' (by omega : count.toNat < 2 ^ 64),
    UInt64.toNat_ofNat_of_lt' (by decide : (8 : UInt32).toNat < 2 ^ 64),
    show (8 : UInt32).toNat = 8 from rfl,
    Nat.mod_eq_of_lt (by omega : count.toNat * 8 < 2 ^ 64),
    show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt (by omega : count.toNat * 8 < 2 ^ 32)]
  rfl

private theorem pointsTo_u32_at_eq
    [WasmSmallStepGS hlc] {left right value : UInt32}
    (h : left = right) :
    pointsTo_u32 left value ⊢ pointsTo_u32 right value := by
  rw [h]

/- Closed absolute-index-107 rule for the zero-valued `Vec<u64>::from_elem`
constructor: the forwarding shim, the implementation, and the complete
singleton-path zeroed allocator chain, ending with the caller's fresh
scratch-vector descriptor and its zero-filled payload.  All shadow-stack
scratch below the caller's frame comes back with known contents, and the
allocator-internal residue is returned opaquely. -/
set_option maxHeartbeats 4000000 in
theorem vecFromElem_zero_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count stackTop : UInt32) (oldFrame16 : UInt64)
    (size smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (oldResultCapacity oldResultData oldResultLength : UInt32)
    (old36 old40 old44 : UInt32)
    (old28' old32' old36' old40' old44' : UInt32)
    (oldPair8 oldPair12 oldWrap8 oldWrap12 : UInt32)
    (oldCore8 oldCore12 oldCore16 oldCore20 oldCore24 oldCore28 : UInt32)
    (hsizeNat : size.toNat = 8 * count.toNat)
    (hsizeNonzero : size ≠ 0)
    (hsmall : size < 245)
    (havailable : smallAllocatorShiftedMap size smallMap &&& 3 ≠ 0)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8) (hdataNonzero : data ≠ 0)
    (hlength : size.toNat =
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length)
    (hpayloadRoom : data.toNat +
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length ≤
      UInt32.size)
    (hheadRoom : (smallAllocatorBinHeadAddress size smallMap).toNat + 4 ≤
      UInt32.size)
    (hchunkLinksRoom : chunk.toNat + 12 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hnextRoom : (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤
      UInt32.size)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    (hallocFrameRoom : (stackTop - 96).toNat + 48 ≤ UInt32.size)
    (hwrapRoom : (stackTop - 112).toNat + 16 ≤ UInt32.size)
    (hcoreRoom : (stackTop - 144).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u64 ((stackTop - 48) + 16) oldFrame16 ∗
      pointsTo_u32 ((stackTop - 48) + 36) old36 ∗
      pointsTo_u32 ((stackTop - 48) + 40) old40 ∗
      pointsTo_u32 ((stackTop - 48) + 44) old44 ∗
      vecDescriptorAt resultPtr oldResultCapacity oldResultData
        oldResultLength ∗
      pointsTo_u32 ((stackTop - 96) + 28) old28' ∗
      pointsTo_u32 ((stackTop - 96) + 32) old32' ∗
      pointsTo_u32 ((stackTop - 96) + 36) old36' ∗
      pointsTo_u32 ((stackTop - 96) + 40) old40' ∗
      pointsTo_u32 ((stackTop - 96) + 44) old44' ∗
      allocationPairAt ((stackTop - 96) + 8) oldPair8 oldPair12 ∗
      allocationPairAt ((stackTop - 112) + 8) oldWrap8 oldWrap12 ∗
      pointsTo_u32 ((stackTop - 144) + 8) oldCore8 ∗
      pointsTo_u32 ((stackTop - 144) + 12) oldCore12 ∗
      pointsTo_u32 ((stackTop - 144) + 16) oldCore16 ∗
      pointsTo_u32 ((stackTop - 144) + 20) oldCore20 ∗
      pointsTo_u32 ((stackTop - 144) + 24) oldCore24 ∗
      pointsTo_u32 ((stackTop - 144) + 28) oldCore28 ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u64 ((stackTop - 48) + 16) 0 -∗
        pointsTo_u32 ((stackTop - 48) + 36) 0 -∗
        pointsTo_u32 ((stackTop - 48) + 40) count -∗
        pointsTo_u32 ((stackTop - 48) + 44) data -∗
        vecDescriptorAt resultPtr count data count -∗
        array64At data (List.replicate count.toNat 0) -∗
        pointsTo_u32 ((stackTop - 96) + 28) 0 -∗
        pointsTo_u32 ((stackTop - 96) + 32) 8 -∗
        pointsTo_u32 ((stackTop - 96) + 36) size -∗
        pointsTo_u32 ((stackTop - 96) + 40) data -∗
        pointsTo_u32 ((stackTop - 96) + 44) size -∗
        allocationPairAt ((stackTop - 96) + 8) data size -∗
        allocationPairAt ((stackTop - 112) + 8) data size -∗
        pointsTo_u32 ((stackTop - 144) + 8) data -∗
        pointsTo_u32 ((stackTop - 144) + 12) size -∗
        pointsTo_u32 ((stackTop - 144) + 16) data -∗
        pointsTo_u32 ((stackTop - 144) + 20) data -∗
        pointsTo_u32 ((stackTop - 144) + 24) data -∗
        pointsTo_u32 ((stackTop - 144) + 28) data -∗
        allocatorCoreResidueAt size smallMap chunk data nextHeader -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 count, .i64 0, .i32 resultPtr] ++ stack },
        .call 107 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h360, h361, h362, h363⟩ :=
    descriptorSlot32Facts (stackTop - 48) 36 48 hframeRoom (by decide)
  have hwords :
      (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
        tail).length = count.toNat := by
    have h1 := hlength.symm.trans hsizeNat
    omega
  iintro ⟨Hruntime, Hglobal, Hframe16, H36, H40, H44, Hresult,
    H28', H32', H36', H40', H44', Hpair, Hwrap,
    Hc8, Hc12, Hc16, Hc20, Hc24, Hc28,
    Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  have Hopen := vecFromElem_zero_to_allocator_call_twp (α := α)
    resultPtr count stackTop oldFrame16 hframeRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := callerLocals) (stack := stack) (code := code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls)
  iapply Hopen
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe16]
  · iexact Hframe16
  iintro Hruntime Hglobal Hframe16
  have Halloc := zeroedAllocator_singleton_call_twp (α := α)
    ((stackTop - 48) + 36) count 1 8 8 (stackTop - 48)
    (UInt64.ofNat count.toNat * UInt64.ofNat (8 : UInt32).toNat)
    size smallMap chunk previous data oldHeader nextHeader headerByte tail
    old28' old32' old36' old40' old44' oldPair8 oldPair12 oldWrap8
    oldWrap12 oldCore8 oldCore12 oldCore16 oldCore20 oldCore24 oldCore28
    old36 old40 old44
    rfl (size8_low_fact count size hsizeNat)
    (size8_high_fact count size hsizeNat)
    (by have hlt := UInt32.lt_iff_toNat_lt.mp hsmall
        rw [show (245 : UInt32).toNat = 245 from rfl] at hlt
        rw [UInt32.le_iff_toNat_le,
          show ((2147483648 : UInt32) - 8).toNat = 2147483640 from rfl]
        omega)
    (by decide) (by decide) hsmall havailable hnonzero hheaderByte hdata
    hdataNonzero hsizeNonzero hlength hpayloadRoom hheadRoom
    hchunkLinksRoom hchunkRoom hnextRoom
    (by rw [show (stackTop - 48) - 48 = stackTop - 96 by bv_decide]
        exact hallocFrameRoom)
    (by rw [show (stackTop - 48) - 64 = stackTop - 112 by bv_decide]
        exact hwrapRoom)
    (by rw [show (stackTop - 48) - 96 = stackTop - 144 by bv_decide]
        exact hcoreRoom)
    (by have h := h360
        rw [show UInt32.ofNat 36 = (36 : UInt32) from rfl] at h
        rw [h]
        simp only [UInt32.size] at hframeRoom ⊢
        omega)
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 resultPtr, .i64 0, .i32 count],
        [.i32 (stackTop - 48), .i32 0, .i32 0, .i64 0,
          .i32 ((stackTop - 48) + 36), .i32 1, .i32 8,
          .i32 0, .i32 0], []⟩)
    (stack := [])
    (code := vecFromElemImplZeroAfterAlloc) (arity := 0)
    (remainder := [])
    (controls :=
      [vecFromElemImplOuterFrame
        [.i32 resultPtr, .i64 0, .i32 count] (stackTop - 48)])
    (calls :=
      { locals := ⟨[.i32 resultPtr, .i64 0, .i32 count], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  rw [show (stackTop - 48) - 48 = stackTop - 96 by bv_decide,
    show (stackTop - 48) - 64 = stackTop - 112 by bv_decide,
    show (stackTop - 48) - 96 = stackTop - 144 by bv_decide] at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  iapply Halloc
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H28']
  · iexact H28'
  isplitl [H32']
  · iexact H32'
  isplitl [H36']
  · iexact H36'
  isplitl [H40']
  · iexact H40'
  isplitl [H44']
  · iexact H44'
  isplitl [Hpair]
  · iexact Hpair
  isplitl [Hwrap]
  · iexact Hwrap
  isplitl [Hc8]
  · iexact Hc8
  isplitl [Hc12]
  · iexact Hc12
  isplitl [Hc16]
  · iexact Hc16
  isplitl [Hc20]
  · iexact Hc20
  isplitl [Hc24]
  · iexact Hc24
  isplitl [Hc28]
  · iexact Hc28
  isplitl [H36]
  · iexact H36
  isplitl [H40]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 48) + 40 = ((stackTop - 48) + 36) + 4 by bv_decide)
    iexact H40
  isplitl [H44]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 48) + 44 = ((stackTop - 48) + 36) + 8 by bv_decide)
    iexact H44
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hhead]
  · iexact Hhead
  isplitl [HheaderTail]
  · iexact HheaderTail
  isplitl [Howned]
  · iexact Howned
  isplitl [HnextHeader]
  · iexact HnextHeader
  iintro Hruntime Hglobal H28' H32' H36' H40' H44' Hpair Hwrap Hc8 Hc12
    Hc16 Hc20 Hc24 Hc28 H36 H40 H44 Hresidue Harray
  ihave H40At : pointsTo_u32 ((stackTop - 48) + 40) count $$ [H40]
  · iapply pointsTo_u32_at_eq
      (show ((stackTop - 48) + 36) + 4 = (stackTop - 48) + 40 by bv_decide)
    iexact H40
  ihave H44At : pointsTo_u32 ((stackTop - 48) + 44) data $$ [H44]
  · iapply pointsTo_u32_at_eq
      (show ((stackTop - 48) + 36) + 8 = (stackTop - 48) + 44 by bv_decide)
    iexact H44
  ihave Harray' : array64At data (List.replicate count.toNat 0) $$ [Harray]
  · rw [← hwords]
    iexact Harray
  have Hsuffix := vecFromElemImpl_zero_success_suffix_twp (α := α)
    resultPtr count (stackTop - 48) count data
    oldResultCapacity oldResultData oldResultLength
    hframeRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := ⟨[.i32 resultPtr, .i64 0, .i32 count], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hsuffix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H36]
  · iexact H36
  isplitl [H40At]
  · iexact H40At
  isplitl [H44At]
  · iexact H44At
  isplitl [Hresult]
  · iexact Hresult
  isplitl [Harray']
  · iexact Harray'
  iintro Hglobal H36 H40 H44 Hresult Harray
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (stackTop - 48) + 48 = stackTop by bv_decide]
    iexact Hglobal
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime HglobalTop Hframe16 H36 H40 H44 Hresult
    Harray H28' H32' H36' H40' H44' Hpair Hwrap Hc8 Hc12 Hc16 Hc20 Hc24
    Hc28 Hresidue

end Project.Mergesort.VecFromElemProof
