import Project.Mergesort.DriverOutputProof
import Project.Mergesort.MemoryFillProof
import Project.Mergesort.ArgumentsProof

/-!
# Generated driver output-loop leaves

The output loop is verified in instruction-shaped pieces.  This first leaf
executes the exact nonempty `IntoIter<u64>::next` call at the head of the
generated loop and reconnects its 16-byte callee frame to the reusable sort
workspace below the exported function's frame.
-/

namespace Project.Mergesort.DriverOutputLoopProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.DriverProof
open Project.Mergesort.DriverSortProof
open Project.Mergesort.DriverOutputProof
open Project.Mergesort.OutputIteratorProof
open Project.Mergesort.SortFunctionProof
open Project.Mergesort.FormatProof
open Project.Mergesort.MemoryFillProof
open Project.Mergesort.ArgumentsProof
open Project.Mergesort.SplitAtProof

def driverOutputLoopBody : Program :=
  match driverAtOutputLoop with
  | [.loop _ _ body] => body
  | _ => []

def driverOutputAfterNext : Program := driverOutputLoopBody.drop 7

def driverOutputInnerBody : Program :=
  match driverOutputAfterNext with
  | .block _ _ outer :: _ =>
      match outer with
      | .block _ _ second :: _ =>
          match second with
          | .block _ _ third :: _ =>
              match third with
              | .block _ _ inner :: _ => inner
              | _ => []
          | _ => []
      | _ => []
  | _ => []

def driverOutputInnerAfterPayload : Program := driverOutputInnerBody.drop 11

def driverOutputCommonCode : Program :=
  match driverOutputAfterNext with
  | .block _ _ _ :: common => common
  | _ => []

def driverOutputAfterDisplayArgument : Program :=
  driverOutputCommonCode.drop 7

def driverOutputAtWriteFmt : Program :=
  driverOutputCommonCode.drop 37

def driverOutputAfterWriteFmt : Program :=
  driverOutputCommonCode.drop 38

theorem driverAtOutputLoop_exact :
    driverAtOutputLoop = [.loop 0 0 driverOutputLoopBody] := by
  rfl

theorem driverOutputLoopBody_next_eq :
    driverOutputLoopBody =
      [.localGet 0, .const 304, .add,
       .localGet 0, .const 288, .add, .call 7] ++
        driverOutputAfterNext := by
  rfl

theorem driverOutputInnerBody_payload_eq :
    driverOutputInnerBody =
      [.localGet 0, .load64 304, .wrapI64, .const 1, .and, .eqz,
       .br_if 0, .localGet 0, .localGet 0, .load64 312, .store64 320] ++
        driverOutputInnerAfterPayload := by
  rfl

theorem driverOutputInnerAfterPayload_eq :
    driverOutputInnerAfterPayload =
      [.localGet 0, .load8U 255, .const 1, .and, .br_if 2, .br 1] := by
  rfl

theorem driverOutputCommonCode_display_eq :
    driverOutputCommonCode =
      [.localGet 0, .const 352, .add,
       .localGet 0, .const 320, .add, .call 45] ++
        driverOutputAfterDisplayArgument := by
  rfl

theorem driverOutputAfterDisplayArgument_eq :
    driverOutputAfterDisplayArgument =
      [.localGet 0, .const 344, .add,
       .localGet 0, .load64 352, .store64 0,
       .const 1050388, .localSet 18,
       .localGet 0, .const 8, .add, .localGet 18,
       .localGet 0, .const 344, .add, .call 51,
       .localGet 0, .load32 12, .localSet 19,
       .localGet 0, .load32 8, .localSet 20,
       .localGet 0, .const 336, .add,
       .localGet 0, .const 72, .add,
       .localGet 20, .localGet 19] ++ driverOutputAtWriteFmt := by
  rfl

theorem driverOutputAtWriteFmt_eq :
    driverOutputAtWriteFmt = .call 35 :: driverOutputAfterWriteFmt := by
  rfl

private theorem twp_wrapI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (value.toNat % 2 ^ 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        .wrapI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.wrapI64)

/-! Once `next` returns `Some value`, this exact innermost generated block
checks the discriminant and copies the payload into the formatting slot. -/
theorem driver_output_extract_payload_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32) (value oldDestination : UInt64)
    (localValues : List Value)
    (hframeLocal : (⟨[], localValues, []⟩ : Locals).get 0 =
      some (.i32 frame))
    (hframeRoom : frame.toNat + 328 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    optionU64At (304 + frame) 1 value ∗
      pointsTo_u64 (320 + frame) oldDestination ∗
      (optionU64At (304 + frame) 1 value -∗
        pointsTo_u64 (320 + frame) value -∗
        WP (.running
          ⟨⟨[], localValues, []⟩,
            driverOutputInnerAfterPayload, 0, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], localValues, []⟩,
        driverOutputInnerBody, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h3040, h3041, h3042, h3043, h3044, h3045, h3046, h3047⟩ :=
    descriptorSlot64Facts frame 304 328 hframeRoom (by decide)
  obtain ⟨h3120, h3121, h3122, h3123, h3124, h3125, h3126, h3127⟩ :=
    descriptorSlot64Facts frame 312 328 hframeRoom (by decide)
  obtain ⟨h3200, h3201, h3202, h3203, h3204, h3205, h3206, h3207⟩ :=
    descriptorSlot64Facts frame 320 328 hframeRoom (by decide)
  have h304 : frame + 304 = 304 + frame := UInt32.add_comm frame 304
  have h312 : frame + 312 = (304 + frame) + 8 := by bv_decide
  have h320 : frame + 320 = 320 + frame := UInt32.add_comm frame 320
  have hframeLocalStack :
      (⟨[], localValues, [.i32 frame]⟩ : Locals).get 0 =
        some (.i32 frame) := by
    simpa only [Locals.get] using hframeLocal
  iintro ⟨Hresult, Hdestination, Hdone⟩
  isimp only [optionU64At] at Hresult
  icases Hresult with ⟨Htag, Hpayload⟩
  rw [driverOutputInnerBody_payload_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet hframeLocal
  ihave HtagAt : pointsTo_u64 (frame + 304) 1 $$ [Htag]
  · rw [h304]
    iexact Htag
  iapply twp_load64 1 h3040 h3041 h3042 h3043 h3044 h3045 h3046 h3047 $$
    HtagAt
  iintro HtagAt
  iapply twp_wrapI64
  rw [show UInt32.ofNat ((1 : UInt64).toNat % 2 ^ 32) = 1 by decide]
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet hframeLocal
  iapply twp_localGet hframeLocalStack
  ihave HpayloadAt : pointsTo_u64 (frame + 312) value $$ [Hpayload]
  · rw [h312]
    iexact Hpayload
  iapply twp_load64 value h3120 h3121 h3122 h3123 h3124 h3125 h3126 h3127 $$
    HpayloadAt
  iintro HpayloadAt
  ihave HdestinationAt : pointsTo_u64 (frame + 320) oldDestination $$
      [Hdestination]
  · rw [h320]
    iexact Hdestination
  iapply twp_store64 oldDestination
    h3200 h3201 h3202 h3203 h3204 h3205 h3206 h3207 $$ HdestinationAt
  iintro HdestinationAt
  ihave Hresult : optionU64At (304 + frame) 1 value $$ [HtagAt HpayloadAt]
  · isimp only [optionU64At]
    isplitl [HtagAt]
    · rw [← h304]
      iexact HtagAt
    rw [← h312]
    iexact HpayloadAt
  ihave Hdestination : pointsTo_u64 (320 + frame) value $$ [HdestinationAt]
  · rw [← h320]
    iexact HdestinationAt
  iapply Hdone $$ Hresult Hdestination

/-! On the first element, the generated byte flag is one and the innermost
block takes its exact depth-two branch, skipping delimiter emission. -/
theorem driver_output_first_flag_branch_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32) (localValues : List Value)
    (hframeLocal : (⟨[], localValues, []⟩ : Locals).get 0 =
      some (.i32 frame))
    (hflag : (frame + 255).toNat = frame.toNat + 255)
    {targetCode : Program} {targetValues : List Value}
    {targetControls controls : List ControlFrame} {calls : List CallFrame}
    (htarget : branchTarget? 0 2 controls [] =
      some (targetCode, targetControls, targetValues)) :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (frame + 255) (DFrac.own 1) (some (1 : UInt8)) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (frame + 255) (DFrac.own 1) (some (1 : UInt8)) -∗
        WP (.running
          ⟨⟨[], localValues, targetValues⟩,
            targetCode, 0, [], targetControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], localValues, []⟩,
        driverOutputInnerAfterPayload, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hflag, Hdone⟩
  rw [driverOutputInnerAfterPayload_eq]
  iapply twp_localGet hframeLocal
  iapply twp_load8U_owned 1 hflag $$ Hflag
  iintro Hflag
  rw [show (1 : UInt8).toUInt32 = (1 : UInt32) by decide]
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) htarget
  iapply Hdone $$ Hflag

/-! After the first element, the byte flag is zero.  The generated depth-two
conditional falls through and the following depth-one branch selects the
delimiter-emission continuation. -/
theorem driver_output_later_flag_branch_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32) (localValues : List Value)
    (hframeLocal : (⟨[], localValues, []⟩ : Locals).get 0 =
      some (.i32 frame))
    (hflag : (frame + 255).toNat = frame.toNat + 255)
    {targetCode : Program} {targetValues : List Value}
    {targetControls controls : List ControlFrame} {calls : List CallFrame}
    (htarget : branchTarget? 0 1 controls [] =
      some (targetCode, targetControls, targetValues)) :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (frame + 255) (DFrac.own 1) (some (0 : UInt8)) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (frame + 255) (DFrac.own 1) (some (0 : UInt8)) -∗
        WP (.running
          ⟨⟨[], localValues, targetValues⟩,
            targetCode, 0, [], targetControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], localValues, []⟩,
        driverOutputInnerAfterPayload, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hflag, Hdone⟩
  rw [driverOutputInnerAfterPayload_eq]
  iapply twp_localGet hframeLocal
  iapply twp_load8U_owned 0 hflag $$ Hflag
  iintro Hflag
  rw [show (0 : UInt8).toUInt32 = (0 : UInt32) by decide]
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_br htarget
  iapply Hdone $$ Hflag

/-! Common value-formatting prefix.  It invokes the exact generated
`Display::fmt` argument constructor and stops immediately after absolute call
45, retaining both descriptors written by that callee. -/
theorem driver_output_display_argument_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32) (localValues : List Value)
    (oldHelper8 oldHelper12 oldResult0 oldResult4 : UInt32)
    (hframeLocal : (⟨[], localValues, []⟩ : Locals).get 0 =
      some (.i32 frame))
    (hhelperRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : (frame + 352).toNat + 8 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 ((frame - 16) + 8) oldHelper8 ∗
      pointsTo_u32 ((frame - 16) + 12) oldHelper12 ∗
      pointsTo_u32 ((frame + 352) + 0) oldResult0 ∗
      pointsTo_u32 ((frame + 352) + 4) oldResult4 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        sliceDescriptorAt ((frame - 16) + 8) (frame + 320) 1 -∗
        sliceDescriptorAt (frame + 352) (frame + 320) 1 -∗
        WP (.running
          ⟨⟨[], localValues, []⟩,
            driverOutputAfterDisplayArgument, 0, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], localValues, []⟩,
        driverOutputCommonCode, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hframeLocalStack :
      (⟨[], localValues, [.i32 (frame + 352)]⟩ : Locals).get 0 =
        some (.i32 frame) := by
    simpa only [Locals.get] using hframeLocal
  iintro ⟨Hruntime, Hglobal, Hhelper8, Hhelper12, Hresult0, Hresult4,
    Hdone⟩
  rw [driverOutputCommonCode_display_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet hframeLocal
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 352 frame]
  iapply twp_localGet hframeLocalStack
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 320 frame]
  have Hcall := displayArgument_call_twp (α := α)
    (frame + 352) (frame + 320) frame
    oldHelper8 oldHelper12 oldResult0 oldResult4
    hhelperRoom hresultRoom
    (callerLocals := ⟨[], localValues, []⟩) (stack := [])
    (code := driverOutputAfterDisplayArgument) (arity := 0)
    (remainder := []) (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil] at Hcall
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hhelper8]
  · iexact Hhelper8
  isplitl [Hhelper12]
  · iexact Hhelper12
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  iintro Hruntime Hglobal Hhelper Hresult
  iapply Hdone $$ Hruntime Hglobal Hhelper Hresult

/-! The exact nonempty iterator-next prefix of one generated output-loop
iteration.  Formatting and delimiter emission begin at
`driverOutputAfterNext` and are proved separately. -/
set_option maxHeartbeats 4000000 in
theorem driver_output_next_nonempty_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame allocation current capacity finish : UInt32)
    (sortLength inputLength dataPtr scratchLength : UInt32)
    (value oldTag oldPayload : UInt64)
    (depth : Nat)
    (hne : finish ≠ current)
    (hnextFrameRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hiterRoom : (288 + frame).toNat + 16 ≤ UInt32.size)
    (hcurrentRoom : current.toNat + 8 ≤ UInt32.size)
    (hresultRoom : (304 + frame).toNat + 16 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      intoIterDescriptorAt (288 + frame) allocation current capacity finish ∗
      pointsTo_u64 current value ∗
      optionU64At (304 + frame) oldTag oldPayload ∗
      SortWorkspace frame (depth + 1) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        intoIterDescriptorAt (288 + frame) allocation (current + 8)
          capacity finish -∗
        pointsTo_u64 current value -∗
        optionU64At (304 + frame) 1 value -∗
        SortWorkspace frame (depth + 1) -∗
        WP (.running
          ⟨⟨[], driverSortCallLocals frame sortLength inputLength dataPtr
              scratchLength, []⟩,
            driverOutputAfterNext, 0, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], driverSortCallLocals frame sortLength inputLength dataPtr
          scratchLength, []⟩,
        driverOutputLoopBody, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hframeSlot : (frame - 48) + 44 = (frame - 16) + 12 := by
    bv_decide
  iintro ⟨Hruntime, Hglobal, Hiter, Hvalue, Hresult, Hworkspace, Hdone⟩
  isimp only [SortWorkspace] at Hworkspace
  icases Hworkspace with ⟨Hframe, Hworkspace⟩
  isimp only [SortFrameOwn] at Hframe
  icases Hframe with
    ⟨%v0, %v1, %v2, %v3, %v4, %v5, %v6, %v7, %v8, %v9, %v10, %v11,
      Hv0, Hv1, Hv2, Hv3, Hv4, Hv5, Hv6, Hv7, Hv8, Hv9, Hv10, Hv11⟩
  rw [driverOutputLoopBody_next_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  ihave Hframe12 : pointsTo_u32 ((frame - 16) + 12) v11 $$ [Hv11]
  · rw [← hframeSlot]
    iexact Hv11
  have Hnext := intoIterNext_nonempty_call_twp (α := α)
    (304 + frame) (288 + frame) allocation current capacity finish frame
    value oldTag oldPayload v11 hne hnextFrameRoom hiterRoom
    hcurrentRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[], driverSortCallLocals frame sortLength inputLength dataPtr
        scratchLength, []⟩)
    (stack := []) (code := driverOutputAfterNext) (arity := 0)
    (remainder := []) (controls := controls) (calls := calls)
  simp only [List.append_nil] at Hnext
  iapply Hnext
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hiter]
  · iexact Hiter
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [Hvalue]
  · iexact Hvalue
  isplitl [Hresult]
  · iexact Hresult
  iintro Hruntime Hglobal Hiter Hframe12 Hvalue Hresult
  ihave Hv11 : pointsTo_u32 ((frame - 48) + 44) current $$ [Hframe12]
  · rw [hframeSlot]
    iexact Hframe12
  ihave Hframe : SortFrameOwn (frame - 48) $$
      [Hv0 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11]
  · isimp only [SortFrameOwn]
    iexists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, current
    iframe
  ihave Hworkspace : SortWorkspace frame (depth + 1) $$ [Hframe Hworkspace]
  · isimp only [SortWorkspace]
    iframe
  iapply Hdone $$ Hruntime Hglobal Hiter Hvalue Hresult Hworkspace

/-! Symmetric empty iterator-next prefix.  It reaches the same generated tag
dispatch with discriminant zero and no array-cell premise. -/
set_option maxHeartbeats 4000000 in
theorem driver_output_next_empty_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame allocation current capacity : UInt32)
    (sortLength inputLength dataPtr scratchLength : UInt32)
    (oldTag oldPayload : UInt64)
    (depth : Nat)
    (hiterRoom : (288 + frame).toNat + 16 ≤ UInt32.size)
    (hresultRoom : (304 + frame).toNat + 16 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      intoIterDescriptorAt (288 + frame) allocation current capacity current ∗
      optionU64At (304 + frame) oldTag oldPayload ∗
      SortWorkspace frame (depth + 1) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        intoIterDescriptorAt (288 + frame) allocation current capacity current -∗
        optionU64At (304 + frame) 0 oldPayload -∗
        SortWorkspace frame (depth + 1) -∗
        WP (.running
          ⟨⟨[], driverSortCallLocals frame sortLength inputLength dataPtr
              scratchLength, []⟩,
            driverOutputAfterNext, 0, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], driverSortCallLocals frame sortLength inputLength dataPtr
          scratchLength, []⟩,
        driverOutputLoopBody, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hframeSlot : (frame - 48) + 44 = (frame - 16) + 12 := by
    bv_decide
  iintro ⟨Hruntime, Hglobal, Hiter, Hresult, Hworkspace, Hdone⟩
  isimp only [SortWorkspace] at Hworkspace
  icases Hworkspace with ⟨Hframe, Hworkspace⟩
  isimp only [SortFrameOwn] at Hframe
  icases Hframe with
    ⟨%v0, %v1, %v2, %v3, %v4, %v5, %v6, %v7, %v8, %v9, %v10, %v11,
      Hv0, Hv1, Hv2, Hv3, Hv4, Hv5, Hv6, Hv7, Hv8, Hv9, Hv10, Hv11⟩
  rw [driverOutputLoopBody_next_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  ihave Hframe12 : pointsTo_u32 ((frame - 16) + 12) v11 $$ [Hv11]
  · rw [← hframeSlot]
    iexact Hv11
  have Hnext := intoIterNext_empty_call_twp (α := α)
    (304 + frame) (288 + frame) allocation current capacity frame
    v11 oldTag oldPayload hiterRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[], driverSortCallLocals frame sortLength inputLength dataPtr
        scratchLength, []⟩)
    (stack := []) (code := driverOutputAfterNext) (arity := 0)
    (remainder := []) (controls := controls) (calls := calls)
  simp only [List.append_nil] at Hnext
  iapply Hnext
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hiter]
  · iexact Hiter
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [Hresult]
  · iexact Hresult
  iintro Hruntime Hglobal Hiter Hframe12 Hresult
  ihave Hv11 : pointsTo_u32 ((frame - 48) + 44) v11 $$ [Hframe12]
  · rw [hframeSlot]
    iexact Hframe12
  ihave Hframe : SortFrameOwn (frame - 48) $$
      [Hv0 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11]
  · isimp only [SortFrameOwn]
    iexists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11
    iframe
  ihave Hworkspace : SortWorkspace frame (depth + 1) $$ [Hframe Hworkspace]
  · isimp only [SortWorkspace]
    iframe
  iapply Hdone $$ Hruntime Hglobal Hiter Hresult Hworkspace

end Project.Mergesort.DriverOutputLoopProof
