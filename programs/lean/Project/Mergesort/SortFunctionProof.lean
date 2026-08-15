import Project.Mergesort.CoreProof
import Project.Mergesort.RangeProof
import Project.Mergesort.SplitAtProof
import Project.Mergesort.CopySliceProof
import Project.Mergesort.MergeFunctionProof

/-!
# Generated `mergesort::<u64>` function proof

The unchanged Rust binary contains its recursive sort as local `func126`.
This file verifies that generated body bottom-up.  The first executable layer
is the complete `length ≤ 1` path: it installs the forty-eight-byte shadow
frame, takes the generated early branch, restores the stack pointer, and
arrives at the function return without touching either array.
-/

namespace Project.Mergesort.SortFunctionProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Pure
open Project.Mergesort.CoreProof
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.SplitAtProof
open Project.Mergesort.CopySliceProof
open Project.Mergesort.MergeFunctionProof

def sortParams
    (dataPtr length scratchPtr scratchLength : UInt32) : List Value :=
  [.i32 dataPtr, .i32 length, .i32 scratchPtr, .i32 scratchLength]

/-- The typed zero-initialized locals of `func126Def`. -/
def sortZeroLocals : List Value :=
  [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

/-- Ownership of one 48-byte generated sort frame, represented as its twelve
`u32` words.  Contents are existential because every helper overwrites its
temporary region before reading it semantically. -/
def SortFrameOwn [WasmHeapGS] (frame : UInt32) : IProp WasmHeapGF :=
  iprop% ∃ v0 : UInt32, ∃ v1 : UInt32, ∃ v2 : UInt32, ∃ v3 : UInt32,
    ∃ v4 : UInt32, ∃ v5 : UInt32, ∃ v6 : UInt32, ∃ v7 : UInt32,
    ∃ v8 : UInt32, ∃ v9 : UInt32, ∃ v10 : UInt32, ∃ v11 : UInt32,
      pointsTo_u32 (frame + 0) v0 ∗
      pointsTo_u32 (frame + 4) v1 ∗
      pointsTo_u32 (frame + 8) v2 ∗
      pointsTo_u32 (frame + 12) v3 ∗
      pointsTo_u32 (frame + 16) v4 ∗
      pointsTo_u32 (frame + 20) v5 ∗
      pointsTo_u32 (frame + 24) v6 ∗
      pointsTo_u32 (frame + 28) v7 ∗
      pointsTo_u32 (frame + 32) v8 ∗
      pointsTo_u32 (frame + 36) v9 ∗
      pointsTo_u32 (frame + 40) v10 ∗
      pointsTo_u32 (frame + 44) v11

/-- Reusable shadow-stack ownership for recursive sort.  The successor layer
owns the current 48-byte frame and recurses below it; helper frames occupy the
upper portion of the next layer and are returned before recursive calls. -/
def SortWorkspace [WasmHeapGS] : UInt32 → Nat → IProp WasmHeapGF
  | _, 0 => iprop% emp
  | stackTop, depth + 1 => iprop%
      SortFrameOwn (stackTop - 48) ∗ SortWorkspace (stackTop - 48) depth

theorem sortWorkspace_succ [WasmSmallStepGS hlc]
    (stackTop : UInt32) (depth : Nat) :
    SortWorkspace stackTop (depth + 1) ⊣⊢
      SortFrameOwn (stackTop - 48) ∗
        SortWorkspace (stackTop - 48) depth :=
  .rfl

theorem sortWorkspace_two [WasmSmallStepGS hlc]
    (stackTop : UInt32) (depth : Nat) :
    SortWorkspace stackTop (depth + 2) ⊣⊢
      SortFrameOwn (stackTop - 48) ∗
        SortFrameOwn ((stackTop - 48) - 48) ∗
        SortWorkspace ((stackTop - 48) - 48) depth := by
  simp only [SortWorkspace]
  exact .rfl

theorem sortWorkspace_stack_step (stackTop : UInt32) (depth : Nat)
    (hsafe : 48 * (depth + 1) ≤ stackTop.toNat) :
    (stackTop - 48).toNat = stackTop.toNat - 48 ∧
      48 * depth ≤ (stackTop - 48).toNat ∧
      (stackTop - 48).toNat + 48 ≤ UInt32.size := by
  have h48 : (48 : UInt32) ≤ stackTop := by
    rw [UInt32.le_iff_toNat_le]
    simpa using (show 48 ≤ stackTop.toNat by omega)
  have hsub := UInt32.toNat_sub_of_le stackTop 48 h48
  rw [show (48 : UInt32).toNat = 48 by decide] at hsub
  refine ⟨hsub, ?_, ?_⟩
  · rw [hsub]
    omega
  · rw [hsub]
    have htop48 : 48 ≤ stackTop.toNat := by omega
    rw [Nat.sub_add_cancel htop48]
    exact Nat.le_of_lt stackTop.toNat_lt

theorem sort_helper_rooms (frame : UInt32) (hlow : 48 ≤ frame.toNat) :
    (frame - 16).toNat + 16 ≤ UInt32.size ∧
      ((frame - 16) - 16).toNat + 16 ≤ UInt32.size ∧
      (frame - 32).toNat + 32 ≤ UInt32.size := by
  have h16 : (16 : UInt32) ≤ frame := by
    rw [UInt32.le_iff_toNat_le]
    change 16 ≤ frame.toNat
    omega
  have h32 : (32 : UInt32) ≤ frame := by
    rw [UInt32.le_iff_toNat_le]
    change 32 ≤ frame.toNat
    omega
  have hframe16 := UInt32.toNat_sub_of_le frame 16 h16
  have hframe32 := UInt32.toNat_sub_of_le frame 32 h32
  rw [show (16 : UInt32).toNat = 16 by decide] at hframe16
  rw [show (32 : UInt32).toNat = 32 by decide] at hframe32
  have hinner16 : (16 : UInt32) ≤ frame - 16 := by
    rw [UInt32.le_iff_toNat_le]
    change 16 ≤ (frame - 16).toNat
    rw [hframe16]
    omega
  have hinner := UInt32.toNat_sub_of_le (frame - 16) 16 hinner16
  rw [show (16 : UInt32).toNat = 16 by decide] at hinner
  have htop := frame.toNat_lt
  refine ⟨?_, ?_, ?_⟩
  · rw [hframe16, Nat.sub_add_cancel (by omega : 16 ≤ frame.toNat)]
    exact Nat.le_of_lt htop
  · rw [hinner, hframe16]
    calc
      (frame.toNat - 16 - 16) + 16 ≤ frame.toNat := by omega
      _ ≤ UInt32.size := Nat.le_of_lt htop
  · rw [hframe32, Nat.sub_add_cancel (by omega : 32 ≤ frame.toNat)]
    exact Nat.le_of_lt htop

/-- Locals after `func126` installs its forty-eight-byte frame. -/
def sortFramedLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

/-- The generated body after its six-instruction shadow-stack prologue. -/
def sortAfterFrame : Program := func126.drop 6

/-- Instructions nested in `func126`'s generated outer block. -/
def sortRecursiveBody : Program :=
  match sortAfterFrame with
  | .block 0 0 body :: _ => body
  | _ => []

/-- The recursive path after the guard and `local 5 := length >> 1`. -/
def sortAfterMid : Program := sortRecursiveBody.drop 10

/-- Generated restoration/return suffix after the recursive outer block. -/
def sortAfterOuterBlock : Program := sortAfterFrame.drop 1

def sortOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := sortRecursiveBody
    continuation := sortAfterOuterBlock
    belowStack := [] }

/-- Locals at the first slice-range call on the recursive path. -/
def sortMidLocals (frame mid : UInt32) : List Value :=
  [.i32 frame, .i32 mid, .i32 0, .i32 0, .i32 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

/-- Continuation after the first `RangeTo` call and the two generated loads
of its `(pointer, length)` result descriptor. -/
def sortAfterFirstRange : Program := sortAfterMid.drop 12

/-- Locals after the first range descriptor has been loaded from `frame`. -/
def sortFirstRangeLocals
    (frame mid firstPtr firstLength : UInt32) : List Value :=
  [.i32 frame, .i32 mid, .i32 firstLength, .i32 firstPtr,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

def sortFirstRangeSourceLocals
    (frame mid firstPtr firstLength sourceLoc : UInt32) : List Value :=
  [.i32 frame, .i32 mid, .i32 firstLength, .i32 firstPtr,
    .i32 sourceLoc, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

/-- Generated state immediately before the first recursive call at absolute
index 128. -/
def sortFirstCallLocals
    (frame mid firstPtr firstLength secondLength : UInt32) : List Value :=
  [.i32 frame, .i32 mid, .i32 firstLength, .i32 firstPtr,
    .i32 1050272, .i32 secondLength,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

def sortAtFirstRecursiveCall : Program := sortAfterFirstRange.drop 18

/-- Continuation supplied to the first recursive call. -/
def sortAfterFirstRecursiveCall : Program := sortAtFirstRecursiveCall.drop 1

/-- Continuation after constructing and loading the data suffix descriptor. -/
def sortAfterDataSuffix : Program := sortAfterFirstRecursiveCall.drop 16

def sortAfterDataSuffixLocals
    (frame mid firstPtr firstLength secondLength suffixPtr suffixLength :
      UInt32) : List Value :=
  [.i32 frame, .i32 mid, .i32 firstLength, .i32 firstPtr,
    .i32 1050272, .i32 secondLength, .i32 1050288,
    .i32 suffixLength, .i32 suffixPtr, .i32 0, .i32 0]

def sortSecondCallLocals
    (frame mid firstPtr firstLength secondLength
      dataSuffixPtr dataSuffixLength scratchSuffixLength : UInt32) :
    List Value :=
  [.i32 frame, .i32 mid, .i32 firstLength, .i32 firstPtr,
    .i32 1050272, .i32 secondLength, .i32 1050288,
    .i32 dataSuffixLength, .i32 dataSuffixPtr, .i32 1050304,
    .i32 scratchSuffixLength]

def sortAtSecondRecursiveCall : Program := sortAfterDataSuffix.drop 18

def sortAfterSecondRecursiveCall : Program := sortAtSecondRecursiveCall.drop 1

def sortAtMergeCall : Program := sortAfterSecondRecursiveCall.drop 18

def sortAfterMerge : Program := sortAtMergeCall.drop 1

private def sortRangeFromParams
    (resultPtr start dataPtr length sourceLoc : UInt32) : List Value :=
  [.i32 resultPtr, .i32 start, .i32 dataPtr, .i32 length, .i32 sourceLoc]

private def sortRangeFromLocals
    (resultLength resultData : UInt32) : List Value :=
  [.i32 resultLength, .i32 resultData]

private theorem sortDescriptorSlotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 8 ≤ UInt32.size)
    (hoffset : offset ≤ 4) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
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
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private theorem sortFrameSlotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 16 ≤ UInt32.size)
    (hoffset : offset ≤ 12) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
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
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private theorem sortWideFrameSlotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 32 ≤ UInt32.size)
    (hoffset : offset ≤ 28) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
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
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private theorem sortFullFrameSlotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 48 ≤ UInt32.size)
    (hoffset : offset ≤ 44) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
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
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private theorem sort_pointsTo_u32_at_eq
    [WasmSmallStepGS hlc] {left right value : UInt32}
    (h : left = right) :
    pointsTo_u32 left value ⊢ pointsTo_u32 right value := by
  rw [h]

private theorem sort_sliceDescriptorAt_elim
    [WasmSmallStepGS hlc] (base data length : UInt32) :
    sliceDescriptorAt base data length ⊢
      pointsTo_u32 base data ∗ pointsTo_u32 (base + 4) length := by
  simp only [sliceDescriptorAt]
  iintro H
  iexact H

/-- Total non-panicking body rule for generated `func9` (`RangeFrom`). -/
theorem sort_rangeFrom_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr start dataPtr length sourceLoc : UInt32)
    (oldResultPtr oldResultLength : UInt32)
    (hstart : start ≤ length)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 resultPtr oldResultPtr ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (pointsTo_u32 resultPtr (dataPtr + (start <<< (3 % 32))) -∗
        pointsTo_u32 (resultPtr + 4) (length - start) -∗
        ∀ controls : List ControlFrame,
          WP (.running
            ⟨⟨sortRangeFromParams resultPtr start dataPtr length sourceLoc,
                sortRangeFromLocals (length - start)
                  ((start <<< (3 % 32)) + dataPtr), []⟩,
              [.ret], 0, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortRangeFromParams resultPtr start dataPtr length sourceLoc,
          sortRangeFromLocals 0 0, []⟩,
        func9, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    sortDescriptorSlotFacts resultPtr 0 hresultRoom (by decide)
  obtain ⟨hl0, hl1, hl2, hl3⟩ :=
    sortDescriptorSlotFacts resultPtr 4 hresultRoom (by decide)
  have hnot : ¬length < start := not_lt_of_ge hstart
  iintro ⟨HresultPtr, HresultLength, Hcont⟩
  simp only [func9]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_gtU (result := 0) (by simp [hnot])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [sortRangeFromParams, sortRangeFromLocals, List.set,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResultLength hl0 hl1 hl2 hl3 $$ HresultLength
  iintro HresultLength
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HresultPtr0 : pointsTo_u32 (resultPtr + 0) oldResultPtr
      $$ [HresultPtr]
  · rw [UInt32.add_zero]
    iexact HresultPtr
  iapply twp_store32 oldResultPtr hr0 hr1 hr2 hr3 $$ HresultPtr0
  iintro HresultPtr0
  ihave HresultPtrPlain :
      pointsTo_u32 resultPtr (dataPtr + (start <<< (3 % 32)))
      $$ [HresultPtr0]
  · iapply pointsTo_u32_add_zero
    rw [UInt32.add_comm dataPtr]
    iexact HresultPtr0
  iapply Hcont $$ HresultPtrPlain HresultLength

/-- Total direct-call rule for generated `RangeFrom` at absolute index 11. -/
theorem sort_rangeFrom_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr start dataPtr length sourceLoc : UInt32)
    (oldResultPtr oldResultLength : UInt32)
    (hstart : start ≤ length)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 resultPtr oldResultPtr ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 resultPtr (dataPtr + (start <<< (3 % 32))) -∗
        pointsTo_u32 (resultPtr + 4) (length - start) -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 sourceLoc, .i32 length, .i32 dataPtr, .i32 start,
            .i32 resultPtr] ++ stack },
        .call 11 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, HresultPtr, HresultLength, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 11 rangeFromFunction
      (by decide) rangeFrom_index $$ Hruntime
  iintro Hruntime
  simp [rangeFromFunction, func9Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  have Hbody := sort_rangeFrom_body_twp (α := α)
    resultPtr start dataPtr length sourceLoc oldResultPtr oldResultLength
    hstart hresultRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [sortRangeFromParams, sortRangeFromLocals] at Hbody
  iapply Hbody
  isplitl [HresultPtr]
  · iexact HresultPtr
  isplitl [HresultLength]
  · iexact HresultLength
  iintro HresultPtr HresultLength
  iintro %calleeControls
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append,
    List.drop_eq_nil_of_le (by decide : 5 ≤
      [.i32 resultPtr, .i32 start, .i32 dataPtr, .i32 length,
        .i32 sourceLoc].length)]
  ihave HresultPtrExpected :
      pointsTo_u32 resultPtr (dataPtr + (start <<< 3)) $$ [HresultPtr]
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iexact HresultPtr
  iapply Hcont $$ Hruntime HresultPtrExpected HresultLength

@[simp] theorem midpoint_toNat (length : UInt32) :
    (length >>> (1 % 32)).toNat = length.toNat / 2 := by
  rw [UInt32.toNat_shiftRight]
  rw [show (1 % 32 : UInt32).toNat % 32 = 1 by decide]
  simp [Nat.shiftRight_eq_div_pow]

theorem midpoint_input_length {input : List UInt64} {length : UInt32}
    (hlength : input.length = length.toNat) :
    (length >>> (1 % 32)).toNat = input.length / 2 := by
  rw [midpoint_toNat, hlength]

theorem midpoint_pos {length : UInt32} (hlarge : 1 < length) :
    0 < (length >>> (1 % 32)).toNat := by
  rw [midpoint_toNat]
  rw [UInt32.lt_iff_toNat_lt] at hlarge
  rw [show (1 : UInt32).toNat = 1 by decide] at hlarge
  omega

theorem midpoint_lt_length {length : UInt32} (hlarge : 1 < length) :
    (length >>> (1 % 32)).toNat < length.toNat := by
  rw [midpoint_toNat]
  rw [UInt32.lt_iff_toNat_lt] at hlarge
  rw [show (1 : UInt32).toNat = 1 by decide] at hlarge
  omega

theorem midpoint_le {length : UInt32} :
    length >>> (1 % 32) ≤ length := by
  rw [UInt32.le_iff_toNat_le, midpoint_toNat]
  omega

theorem midpoint_lt_nat {input : List UInt64} {length : UInt32}
    (hlarge : 1 < length) (hlength : input.length = length.toNat) :
    input.length / 2 < input.length := by
  have h := midpoint_lt_length hlarge
  rw [midpoint_toNat, ← hlength] at h
  exact h

theorem suffix_ptr_toNat (base length : UInt32)
    (hlarge : 1 < length)
    (hfit : base.toNat + 8 * length.toNat ≤ UInt32.size) :
    (base + ((length >>> (1 % 32)) <<< 3)).toNat =
      base.toNat + 8 * (length.toNat / 2) := by
  rw [UInt32.add_comm base]
  rw [← (UInt32.ofNat_toNat (x := length >>> (1 % 32)))]
  have hshift :
      (UInt32.ofNat (length >>> (1 % 32)).toNat <<< 3) + base =
        base + (8 : UInt32) * UInt32.ofNat (length >>> (1 % 32)).toNat := by
    simpa using shiftAddress64_eq base (length >>> (1 % 32)).toNat
  rw [hshift]
  apply Mem.words64_slotAddr_toNat
  rw [midpoint_toNat]
  have hmid := midpoint_lt_length hlarge
  rw [midpoint_toNat] at hmid
  simp only [UInt32.size] at hfit ⊢
  omega

theorem suffix_length_lt {length : UInt32} (hlarge : 1 < length) :
    length.toNat - (length >>> (1 % 32)).toNat < length.toNat := by
  rw [midpoint_toNat]
  rw [UInt32.lt_iff_toNat_lt] at hlarge
  rw [show (1 : UInt32).toNat = 1 by decide] at hlarge
  omega

theorem sortRel_base {input : List UInt64} (hlength : input.length ≤ 1) :
    SortRel input input :=
  .small hlength

theorem sortPost_base {input : List UInt64} (hlength : input.length ≤ 1) :
    SortPost input input := by
  exact sortedPermutation_of_sortRel (.small hlength)

/-- Exact recursive-branch prefix inside the generated outer block.  When
`length > 1`, the early branch is not taken and local 5 receives the unsigned
half length used by both recursive calls. -/
theorem sort_recursive_guard_mid_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame : UInt32)
    (hlarge : 1 < length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortMidLocals frame (length >>> (1 % 32)), []⟩,
        sortAfterMid, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortFramedLocals frame, []⟩,
        sortRecursiveBody, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hnot : ¬length ≤ 1 := by
    rw [UInt32.lt_iff_toNat_lt] at hlarge
    rw [UInt32.le_iff_toNat_le]
    omega
  simp [sortAfterMid, sortRecursiveBody, sortAfterFrame, func126]
  iintro Hcont
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_leU (result := 0) (by simp [hnot])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shrU
  iapply twp_localSet rfl
  simp [sortParams, sortFramedLocals, sortMidLocals]
  iapply Hcont

/-- Exact full-function prefix for the recursive branch, including the
forty-eight-byte shadow-frame installation and entry into the generated outer
block.  The continuation begins at the first `RangeTo` call preparation. -/
theorem sort_recursive_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength stackTop : UInt32)
    (hlarge : 1 < length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortMidLocals (stackTop - 48) (length >>> (1 % 32)), []⟩,
            sortAfterMid, arity, remainder, sortOuterFrame :: controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortZeroLocals, []⟩,
        func126, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [sortParams, sortZeroLocals, sortMidLocals, sortAfterMid,
    sortOuterFrame, sortRecursiveBody, sortAfterFrame, sortAfterOuterBlock,
    func126]
  iintro ⟨Hglobal, Hcont⟩
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
  iapply twp_block
  simp
  have Hguard := sort_recursive_guard_mid_twp (α := α)
    dataPtr length scratchPtr scratchLength (stackTop - 48) hlarge
    (s := s) (E := E) (Φ := Φ) (arity := arity) (remainder := remainder)
    (controls := sortOuterFrame :: controls) (calls := calls)
  simp [sortParams, sortFramedLocals, sortMidLocals,
    sortRecursiveBody, sortAfterFrame, sortAfterMid, sortAfterOuterBlock,
    sortOuterFrame, func126] at Hguard
  iapply Hguard
  ispecialize Hcont $$ Hglobal
  iapply Hcont

/-- Exact first helper segment on the recursive path.  It prepares and calls
generated `RangeTo` at absolute index 10 for `data[..mid]`, then performs the
two descriptor loads into locals 6 and 7. -/
theorem sort_first_range_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame mid : UInt32)
    (oldResultPtr oldResultLength oldOuter8 oldOuter12
      oldInner8 oldInner12 : UInt32)
    (hmid : mid ≤ length)
    (houterRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hinnerRoom : ((frame - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : frame.toNat + 8 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 ((frame - 16) + 8) oldOuter8 ∗
      pointsTo_u32 ((frame - 16) + 12) oldOuter12 ∗
      pointsTo_u32 (((frame - 16) - 16) + 8) oldInner8 ∗
      pointsTo_u32 (((frame - 16) - 16) + 12) oldInner12 ∗
      pointsTo_u32 frame oldResultPtr ∗
      pointsTo_u32 (frame + 4) oldResultLength ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        pointsTo_u32 ((frame - 16) + 8) dataPtr -∗
        pointsTo_u32 ((frame - 16) + 12) mid -∗
        pointsTo_u32 (((frame - 16) - 16) + 8) 1 -∗
        pointsTo_u32 (((frame - 16) - 16) + 12) mid -∗
        pointsTo_u32 frame dataPtr -∗
        pointsTo_u32 (frame + 4) mid -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortFirstRangeLocals frame mid dataPtr mid, []⟩,
            sortAfterFirstRange, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortMidLocals frame mid, []⟩,
        sortAfterMid, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    sortDescriptorSlotFacts frame 0 hresultRoom (by decide)
  obtain ⟨hl0, hl1, hl2, hl3⟩ :=
    sortDescriptorSlotFacts frame 4 hresultRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Houter8, Houter12, Hinner8, Hinner12,
    HresultPtr, HresultLength, Hcont⟩
  simp only [sortAfterMid, sortRecursiveBody, sortAfterFrame, func126,
    List.drop]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  have Hrange := rangeTo_call_twp (α := α)
    frame dataPtr mid length 1050256 frame
    oldResultPtr oldResultLength oldOuter8 oldOuter12 oldInner8 oldInner12
    hmid houterRoom hinnerRoom hresultRoom
    (callerLocals :=
      ⟨sortParams dataPtr length scratchPtr scratchLength,
        sortMidLocals frame mid, []⟩)
    (stack := []) (code := sortAfterMid.drop 6)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [sortAfterMid, sortRecursiveBody, sortAfterFrame, func126,
    List.drop, List.append_nil] at Hrange
  iapply Hrange
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Houter8]
  · iexact Houter8
  isplitl [Houter12]
  · iexact Houter12
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [HresultPtr]
  · iexact HresultPtr
  isplitl [HresultLength]
  · iexact HresultLength
  iintro Hruntime Hglobal Houter8 Houter12 Hinner8 Hinner12
    HresultPtr HresultLength
  iapply twp_localGet rfl
  iapply twp_load32 mid hl0 hl1 hl2 hl3 $$ HresultLength
  iintro HresultLength
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  ihave HresultPtr0 : pointsTo_u32 (frame + 0) dataPtr $$ [HresultPtr]
  · rw [UInt32.add_zero]
    iexact HresultPtr
  iapply twp_load32 dataPtr hr0 hr1 hr2 hr3 $$ HresultPtr0
  iintro HresultPtr0
  iapply twp_localSet rfl
  simp only [sortParams, sortMidLocals, sortFirstRangeLocals,
    sortAfterFirstRange, sortAfterMid, sortRecursiveBody, sortAfterFrame,
    func126, List.drop, List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave HresultPtrPlain : pointsTo_u32 frame dataPtr $$ [HresultPtr0]
  · iapply pointsTo_u32_add_zero
    iexact HresultPtr0
  iapply Hcont $$ Hruntime Hglobal Houter8 Houter12 Hinner8 Hinner12
    HresultPtrPlain HresultLength

/-- Exact second helper segment.  It builds `scratch[..mid]` with the second
generated `RangeTo` call, loads its length, prepares the four recursive-sort
arguments, and stops with `.call 128` as the next instruction. -/
theorem sort_second_range_to_first_recursive_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame mid : UInt32)
    (oldSecondPtr oldSecondLength outer8 outer12 inner8 inner12 : UInt32)
    (hmidScratch : mid ≤ scratchLength)
    (houterRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hinnerRoom : ((frame - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    (hsecondResultRoom : (frame + 8).toNat + 8 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 ((frame - 16) + 8) outer8 ∗
      pointsTo_u32 ((frame - 16) + 12) outer12 ∗
      pointsTo_u32 (((frame - 16) - 16) + 8) inner8 ∗
      pointsTo_u32 (((frame - 16) - 16) + 12) inner12 ∗
      pointsTo_u32 frame dataPtr ∗
      pointsTo_u32 (frame + 4) mid ∗
      pointsTo_u32 (frame + 8) oldSecondPtr ∗
      pointsTo_u32 (frame + 12) oldSecondLength ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        pointsTo_u32 ((frame - 16) + 8) scratchPtr -∗
        pointsTo_u32 ((frame - 16) + 12) mid -∗
        pointsTo_u32 (((frame - 16) - 16) + 8) 1 -∗
        pointsTo_u32 (((frame - 16) - 16) + 12) mid -∗
        pointsTo_u32 frame dataPtr -∗
        pointsTo_u32 (frame + 4) mid -∗
        pointsTo_u32 (frame + 8) scratchPtr -∗
        pointsTo_u32 (frame + 12) mid -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortFirstCallLocals frame mid dataPtr mid mid,
              [.i32 mid, .i32 scratchPtr, .i32 mid, .i32 dataPtr]⟩,
            sortAtFirstRecursiveCall, arity, remainder, controls, calls⟩ :
            Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortFirstRangeLocals frame mid dataPtr mid, []⟩,
        sortAfterFirstRange, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hs80, hs81, hs82, hs83⟩ :=
    sortFrameSlotFacts frame 8 hframeRoom (by decide)
  obtain ⟨hs120, hs121, hs122, hs123⟩ :=
    sortFrameSlotFacts frame 12 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Houter8, Houter12, Hinner8, Hinner12,
    HfirstPtr, HfirstLength, HsecondPtr, HsecondLength, Hcont⟩
  simp only [sortAfterFirstRange, sortAfterMid, sortRecursiveBody,
    sortAfterFrame, func126, List.drop]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [sortParams, sortFirstRangeLocals,
    List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (8 : UInt32) frame]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  have Hrange := rangeTo_call_twp (α := α)
    (frame + 8) scratchPtr mid scratchLength 1050272 frame
    oldSecondPtr oldSecondLength outer8 outer12 inner8 inner12
    hmidScratch houterRoom hinnerRoom hsecondResultRoom
    (callerLocals :=
      ⟨sortParams dataPtr length scratchPtr scratchLength,
        sortFirstRangeSourceLocals frame mid dataPtr mid 1050272, []⟩)
    (stack := []) (code := sortAfterFirstRange.drop 10)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [sortAfterFirstRange, sortAfterMid, sortRecursiveBody,
    sortAfterFrame, func126, sortParams, sortFirstRangeSourceLocals,
    List.drop, List.append_nil] at Hrange
  ihave HsecondLengthAt : pointsTo_u32 ((frame + 8) + 4) oldSecondLength
      $$ [HsecondLength]
  · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
    iexact HsecondLength
  iapply Hrange
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Houter8]
  · iexact Houter8
  isplitl [Houter12]
  · iexact Houter12
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [HsecondPtr]
  · iexact HsecondPtr
  isplitl [HsecondLengthAt]
  · iexact HsecondLengthAt
  iintro Hruntime Hglobal Houter8 Houter12 Hinner8 Hinner12
    HsecondPtr HsecondLength
  ihave HsecondLength12 : pointsTo_u32 (frame + 12) mid $$ [HsecondLength]
  · iapply sort_pointsTo_u32_at_eq (show (frame + 8) + 4 = frame + 12 by
      bv_decide)
    iexact HsecondLength
  iapply twp_localGet rfl
  iapply twp_load32 mid hs120 hs121 hs122 hs123 $$ HsecondLength12
  iintro HsecondLength12
  iapply twp_localSet rfl
  simp only [sortFirstCallLocals,
    List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 scratchPtr hs80 hs81 hs82 hs83 $$ HsecondPtr
  iintro HsecondPtr
  iapply twp_localGet rfl
  simp only [sortAtFirstRecursiveCall, sortAfterFirstRange, sortAfterMid,
    sortRecursiveBody, sortAfterFrame, func126, List.drop]
  iapply Hcont $$ Hruntime Hglobal Houter8 Houter12 Hinner8 Hinner12
    HfirstPtr HfirstLength HsecondPtr HsecondLength12

/-- Workspace-packaged prefix of the recursive branch.  It owns and returns
the overlapping parent/helper/child stack region while exposing the first
recursive call as the next instruction. -/
theorem sort_to_first_recursive_call_workspace_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength stackTop : UInt32)
    (depth : Nat) (hlarge : 1 < length)
    (hmidScratch : length >>> (1 % 32) ≤ scratchLength)
    (hsafe : 48 * (depth + 2) ≤ stackTop.toNat)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      SortWorkspace stackTop (depth + 2) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        SortFrameOwn (stackTop - 48) -∗
        SortWorkspace (stackTop - 48) (depth + 1) -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortFirstCallLocals (stackTop - 48)
                (length >>> (1 % 32)) dataPtr (length >>> (1 % 32))
                (length >>> (1 % 32)),
              [.i32 (length >>> (1 % 32)), .i32 scratchPtr,
                .i32 (length >>> (1 % 32)), .i32 dataPtr]⟩,
            sortAtFirstRecursiveCall, arity, remainder,
            sortOuterFrame :: controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortZeroLocals, []⟩,
        func126, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let frame := stackTop - 48
  let childFrame := frame - 48
  have hstep := sortWorkspace_stack_step stackTop (depth + 1) hsafe
  have hframeRoom : frame.toNat + 48 ≤ UInt32.size := by
    simpa only [frame] using hstep.2.2
  have hframeLow : 48 ≤ frame.toNat := by
    have htailSafe : 48 * (depth + 1) ≤ frame.toNat := by
      simpa only [frame] using hstep.2.1
    omega
  have hframe16 : frame.toNat + 16 ≤ UInt32.size := by omega
  obtain ⟨houterRoom, hinnerRoom, _hsplitRoom⟩ :=
    sort_helper_rooms frame hframeLow
  have hresult8 : frame.toNat + 8 ≤ UInt32.size := by omega
  have hresult16 : (frame + 8).toNat + 8 ≤ UInt32.size := by
    have h8 : (frame + 8).toNat = frame.toNat + 8 := by
      apply UInt32.add_ofNat_toNat_noWrap
      · decide
      · simpa only [UInt32.size] using (show frame.toNat + 8 < UInt32.size by
          omega)
    rw [h8]
    omega
  iintro ⟨Hruntime, Hglobal, Hworkspace, Hcont⟩
  icases (sortWorkspace_two stackTop depth).mp $$ Hworkspace with
    ⟨Hframe, Hchild, Hrest⟩
  isimp only [SortFrameOwn] at Hframe
  icases Hframe with
    ⟨%c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8, %c9, %c10, %c11,
      Hc0, Hc1, Hc2, Hc3, Hc4, Hc5, Hc6, Hc7, Hc8, Hc9, Hc10, Hc11⟩
  isimp only [SortFrameOwn] at Hchild
  icases Hchild with
    ⟨%n0, %n1, %n2, %n3, %n4, %n5, %n6, %n7, %n8, %n9, %n10, %n11,
      Hn0, Hn1, Hn2, Hn3, Hn4, Hn5, Hn6, Hn7, Hn8, Hn9, Hn10, Hn11⟩
  iapply sort_recursive_prefix_twp dataPtr length scratchPtr scratchLength
    stackTop hlarge
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave Hc0Plain : pointsTo_u32 frame c0 $$ [Hc0]
  · iapply pointsTo_u32_add_zero
    iexact Hc0
  ihave Houter8 : pointsTo_u32 ((frame - 16) + 8) n10 $$ [Hn10]
  · iapply sort_pointsTo_u32_at_eq
      (show childFrame + 40 = (frame - 16) + 8 by
        dsimp only [childFrame]; bv_decide)
    iexact Hn10
  ihave Houter12 : pointsTo_u32 ((frame - 16) + 12) n11 $$ [Hn11]
  · iapply sort_pointsTo_u32_at_eq
      (show childFrame + 44 = (frame - 16) + 12 by
        dsimp only [childFrame]; bv_decide)
    iexact Hn11
  ihave Hinner8 : pointsTo_u32 (((frame - 16) - 16) + 8) n6 $$ [Hn6]
  · iapply sort_pointsTo_u32_at_eq
      (show childFrame + 24 = ((frame - 16) - 16) + 8 by
        dsimp only [childFrame]; bv_decide)
    iexact Hn6
  ihave Hinner12 : pointsTo_u32 (((frame - 16) - 16) + 12) n7 $$ [Hn7]
  · iapply sort_pointsTo_u32_at_eq
      (show childFrame + 28 = ((frame - 16) - 16) + 12 by
        dsimp only [childFrame]; bv_decide)
    iexact Hn7
  iapply sort_first_range_twp dataPtr length scratchPtr scratchLength frame
    (length >>> (1 % 32)) c0 c1 n10 n11 n6 n7
    (midpoint_le (length := length)) houterRoom hinnerRoom hresult8
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Houter8]
  · iexact Houter8
  isplitl [Houter12]
  · iexact Houter12
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hc0Plain]
  · iexact Hc0Plain
  isplitl [Hc1]
  · iexact Hc1
  iintro Hruntime Hglobal Houter8 Houter12 Hinner8 Hinner12 Hc0 Hc1
  iapply sort_second_range_to_first_recursive_call_twp
    dataPtr length scratchPtr scratchLength frame (length >>> (1 % 32))
    c2 c3 dataPtr (length >>> (1 % 32)) 1 (length >>> (1 % 32))
    hmidScratch houterRoom hinnerRoom hframe16 hresult16
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Houter8]
  · iexact Houter8
  isplitl [Houter12]
  · iexact Houter12
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hc0]
  · iexact Hc0
  isplitl [Hc1]
  · iexact Hc1
  isplitl [Hc2]
  · iexact Hc2
  isplitl [Hc3]
  · iexact Hc3
  iintro Hruntime Hglobal Houter8 Houter12 Hinner8 Hinner12
    Hc0 Hc1 Hc2 Hc3
  ihave Hc0At : pointsTo_u32 (frame + 0) dataPtr $$ [Hc0]
  · rw [UInt32.add_zero]
    iexact Hc0
  ihave Hn10At : pointsTo_u32 (childFrame + 40) scratchPtr $$ [Houter8]
  · iapply sort_pointsTo_u32_at_eq
      (show (frame - 16) + 8 = childFrame + 40 by
        dsimp only [childFrame]; bv_decide)
    iexact Houter8
  ihave Hn11At : pointsTo_u32 (childFrame + 44)
      (length >>> (1 % 32)) $$ [Houter12]
  · iapply sort_pointsTo_u32_at_eq
      (show (frame - 16) + 12 = childFrame + 44 by
        dsimp only [childFrame]; bv_decide)
    iexact Houter12
  ihave Hn6At : pointsTo_u32 (childFrame + 24) 1 $$ [Hinner8]
  · iapply sort_pointsTo_u32_at_eq
      (show ((frame - 16) - 16) + 8 = childFrame + 24 by
        dsimp only [childFrame]; bv_decide)
    iexact Hinner8
  ihave Hn7At : pointsTo_u32 (childFrame + 28)
      (length >>> (1 % 32)) $$ [Hinner12]
  · iapply sort_pointsTo_u32_at_eq
      (show ((frame - 16) - 16) + 12 = childFrame + 28 by
        dsimp only [childFrame]; bv_decide)
    iexact Hinner12
  ihave HframeOwn : SortFrameOwn frame $$
      [Hc0At Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hc9 Hc10 Hc11]
  · isimp only [SortFrameOwn]
    iexists dataPtr
    iexists (length >>> (1 % 32))
    iexists scratchPtr
    iexists (length >>> (1 % 32))
    iexists c4
    iexists c5
    iexists c6
    iexists c7
    iexists c8
    iexists c9
    iexists c10
    iexists c11
    iframe
  ihave HchildOwn : SortFrameOwn childFrame $$
      [Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6At Hn7At Hn8 Hn9 Hn10At Hn11At]
  · isimp only [SortFrameOwn]
    iexists n0
    iexists n1
    iexists n2
    iexists n3
    iexists n4
    iexists n5
    iexists 1
    iexists (length >>> (1 % 32))
    iexists n8
    iexists n9
    iexists scratchPtr
    iexists (length >>> (1 % 32))
    iframe
  ihave Htail : SortWorkspace frame (depth + 1) $$ [HchildOwn Hrest]
  · iapply (sortWorkspace_succ frame depth).mpr
    iframe
  iapply Hcont $$ Hruntime Hglobal HframeOwn Htail

/-- After the first recursive call returns, construct `data[mid..]` with the
generated `RangeFrom` helper and load its descriptor into locals 11 and 12. -/
theorem sort_data_suffix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame mid : UInt32)
    (oldSuffixPtr oldSuffixLength : UInt32)
    (hmid : mid ≤ length)
    (hframeRoom : frame.toNat + 32 ≤ UInt32.size)
    (hresultRoom : (frame + 16).toNat + 8 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (frame + 16) oldSuffixPtr ∗
      pointsTo_u32 (frame + 20) oldSuffixLength ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 (frame + 16) (dataPtr + (mid <<< 3)) -∗
        pointsTo_u32 (frame + 20) (length - mid) -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortAfterDataSuffixLocals frame mid dataPtr mid mid
                (dataPtr + (mid <<< 3)) (length - mid), []⟩,
            sortAfterDataSuffix, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortFirstCallLocals frame mid dataPtr mid mid, []⟩,
        sortAfterFirstRecursiveCall, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hp160, hp161, hp162, hp163⟩ :=
    sortWideFrameSlotFacts frame 16 hframeRoom (by decide)
  obtain ⟨hl200, hl201, hl202, hl203⟩ :=
    sortWideFrameSlotFacts frame 20 hframeRoom (by decide)
  iintro ⟨Hruntime, HsuffixPtr, HsuffixLength, Hcont⟩
  simp only [sortAfterFirstRecursiveCall, sortAtFirstRecursiveCall,
    sortAfterFirstRange, sortAfterMid, sortRecursiveBody, sortAfterFrame,
    func126, List.drop]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [sortParams, sortFirstCallLocals, sortAfterDataSuffixLocals,
    List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (16 : UInt32) frame]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  have Hrange := sort_rangeFrom_call_twp (α := α)
    (frame + 16) mid dataPtr length 1050288
    oldSuffixPtr oldSuffixLength hmid hresultRoom
    (callerLocals :=
      ⟨sortParams dataPtr length scratchPtr scratchLength,
        sortAfterDataSuffixLocals frame mid dataPtr mid mid 0 0, []⟩)
    (stack := []) (code := sortAfterFirstRecursiveCall.drop 10)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [sortAfterFirstRecursiveCall, sortAtFirstRecursiveCall,
    sortAfterFirstRange, sortAfterMid, sortRecursiveBody, sortAfterFrame,
    func126, sortParams, sortAfterDataSuffixLocals, List.drop,
    List.append_nil] at Hrange
  ihave HsuffixLengthAt :
      pointsTo_u32 ((frame + 16) + 4) oldSuffixLength $$ [HsuffixLength]
  · rw [show (frame + 16) + 4 = frame + 20 by bv_decide]
    iexact HsuffixLength
  iapply Hrange
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [HsuffixPtr]
  · iexact HsuffixPtr
  isplitl [HsuffixLengthAt]
  · iexact HsuffixLengthAt
  iintro Hruntime HsuffixPtr HsuffixLength
  ihave HsuffixLength20 : pointsTo_u32 (frame + 20) (length - mid)
      $$ [HsuffixLength]
  · iapply sort_pointsTo_u32_at_eq
      (show (frame + 16) + 4 = frame + 20 by bv_decide)
    iexact HsuffixLength
  iapply twp_localGet rfl
  iapply twp_load32 (length - mid) hl200 hl201 hl202 hl203 $$ HsuffixLength20
  iintro HsuffixLength20
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  ihave HsuffixPtr3 :
      pointsTo_u32 (frame + 16) (dataPtr + (mid <<< 3)) $$ [HsuffixPtr]
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iexact HsuffixPtr
  iapply twp_load32 (dataPtr + (mid <<< 3)) hp160 hp161 hp162 hp163
      $$ HsuffixPtr3
  iintro HsuffixPtr
  iapply twp_localSet rfl
  simp only [sortAfterDataSuffix, sortAfterFirstRecursiveCall,
    sortAtFirstRecursiveCall, sortAfterFirstRange, sortAfterMid,
    sortRecursiveBody, sortAfterFrame, func126, List.drop, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply Hcont $$ Hruntime HsuffixPtr HsuffixLength20

/-- Construct `scratch[mid..]`, load its length, and prepare the exact operand
stack consumed by the second generated recursive call. -/
theorem sort_scratch_suffix_to_second_recursive_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame mid : UInt32)
    (dataSuffixPtr dataSuffixLength oldScratchSuffixPtr
      oldScratchSuffixLength : UInt32)
    (hmid : mid ≤ scratchLength)
    (hframeRoom : frame.toNat + 32 ≤ UInt32.size)
    (hresultRoom : (frame + 24).toNat + 8 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (frame + 24) oldScratchSuffixPtr ∗
      pointsTo_u32 (frame + 28) oldScratchSuffixLength ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 (frame + 24) (scratchPtr + (mid <<< 3)) -∗
        pointsTo_u32 (frame + 28) (scratchLength - mid) -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortSecondCallLocals frame mid dataPtr mid mid
                dataSuffixPtr dataSuffixLength (scratchLength - mid),
              [.i32 (scratchLength - mid),
                .i32 (scratchPtr + (mid <<< 3)),
                .i32 dataSuffixLength, .i32 dataSuffixPtr]⟩,
            sortAtSecondRecursiveCall, arity, remainder, controls, calls⟩ :
            Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortAfterDataSuffixLocals frame mid dataPtr mid mid
            dataSuffixPtr dataSuffixLength, []⟩,
        sortAfterDataSuffix, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hp240, hp241, hp242, hp243⟩ :=
    sortWideFrameSlotFacts frame 24 hframeRoom (by decide)
  obtain ⟨hl280, hl281, hl282, hl283⟩ :=
    sortWideFrameSlotFacts frame 28 hframeRoom (by decide)
  iintro ⟨Hruntime, HscratchSuffixPtr, HscratchSuffixLength, Hcont⟩
  simp only [sortAfterDataSuffix, sortAfterFirstRecursiveCall,
    sortAtFirstRecursiveCall, sortAfterFirstRange, sortAfterMid,
    sortRecursiveBody, sortAfterFrame, func126, List.drop]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [sortParams, sortAfterDataSuffixLocals, sortSecondCallLocals,
    List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (24 : UInt32) frame]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  have Hrange := sort_rangeFrom_call_twp (α := α)
    (frame + 24) mid scratchPtr scratchLength 1050304
    oldScratchSuffixPtr oldScratchSuffixLength hmid hresultRoom
    (callerLocals :=
      ⟨sortParams dataPtr length scratchPtr scratchLength,
        sortSecondCallLocals frame mid dataPtr mid mid dataSuffixPtr
          dataSuffixLength 0, []⟩)
    (stack := []) (code := sortAfterDataSuffix.drop 10)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [sortAfterDataSuffix, sortAfterFirstRecursiveCall,
    sortAtFirstRecursiveCall, sortAfterFirstRange, sortAfterMid,
    sortRecursiveBody, sortAfterFrame, func126, sortParams,
    sortSecondCallLocals, List.drop, List.append_nil] at Hrange
  ihave HscratchSuffixLengthAt :
      pointsTo_u32 ((frame + 24) + 4) oldScratchSuffixLength
      $$ [HscratchSuffixLength]
  · rw [show (frame + 24) + 4 = frame + 28 by bv_decide]
    iexact HscratchSuffixLength
  iapply Hrange
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [HscratchSuffixPtr]
  · iexact HscratchSuffixPtr
  isplitl [HscratchSuffixLengthAt]
  · iexact HscratchSuffixLengthAt
  iintro Hruntime HscratchSuffixPtr HscratchSuffixLength
  ihave HscratchSuffixLength28 :
      pointsTo_u32 (frame + 28) (scratchLength - mid)
      $$ [HscratchSuffixLength]
  · iapply sort_pointsTo_u32_at_eq
      (show (frame + 24) + 4 = frame + 28 by bv_decide)
    iexact HscratchSuffixLength
  iapply twp_localGet rfl
  iapply twp_load32 (scratchLength - mid) hl280 hl281 hl282 hl283
      $$ HscratchSuffixLength28
  iintro HscratchSuffixLength28
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HscratchSuffixPtr3 :
      pointsTo_u32 (frame + 24) (scratchPtr + (mid <<< 3))
      $$ [HscratchSuffixPtr]
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iexact HscratchSuffixPtr
  iapply twp_load32 (scratchPtr + (mid <<< 3)) hp240 hp241 hp242 hp243
      $$ HscratchSuffixPtr3
  iintro HscratchSuffixPtr
  iapply twp_localGet rfl
  simp only [sortAtSecondRecursiveCall, sortAfterDataSuffix,
    sortAfterFirstRecursiveCall, sortAtFirstRecursiveCall,
    sortAfterFirstRange, sortAfterMid, sortRecursiveBody, sortAfterFrame,
    func126, List.drop]
  iapply Hcont $$ Hruntime HscratchSuffixPtr HscratchSuffixLength28

/-- Workspace-packaged bridge between the two recursive calls.  It executes
both generated `RangeFrom` descriptor constructions, preserves the lower
recursive workspace, and returns the current frame at the exact second-call
boundary. -/
theorem sort_between_recursive_calls_workspace_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame mid : UInt32)
    (depth : Nat)
    (hmidData : mid ≤ length) (hmidScratch : mid ≤ scratchLength)
    (hframeRoom : frame.toNat + 48 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      SortFrameOwn frame ∗
      SortWorkspace frame (depth + 1) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        SortFrameOwn frame -∗
        SortWorkspace frame (depth + 1) -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortSecondCallLocals frame mid dataPtr mid mid
                (dataPtr + (mid <<< 3)) (length - mid)
                (scratchLength - mid),
              [.i32 (scratchLength - mid),
                .i32 (scratchPtr + (mid <<< 3)),
                .i32 (length - mid), .i32 (dataPtr + (mid <<< 3))]⟩,
            sortAtSecondRecursiveCall, arity, remainder,
            sortOuterFrame :: controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortFirstCallLocals frame mid dataPtr mid mid, []⟩,
        sortAfterFirstRecursiveCall, arity, remainder,
        sortOuterFrame :: controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have hframe32 : frame.toNat + 32 ≤ UInt32.size := by omega
  have hresult20 : (frame + 16).toNat + 8 ≤ UInt32.size := by
    have h16 : (frame + 16).toNat = frame.toNat + 16 := by
      apply UInt32.add_ofNat_toNat_noWrap
      · decide
      · simpa only [UInt32.size] using
          (show frame.toNat + 16 < UInt32.size by omega)
    rw [h16]
    omega
  have hresult28 : (frame + 24).toNat + 8 ≤ UInt32.size := by
    have h24 : (frame + 24).toNat = frame.toNat + 24 := by
      apply UInt32.add_ofNat_toNat_noWrap
      · decide
      · simpa only [UInt32.size] using
          (show frame.toNat + 24 < UInt32.size by omega)
    rw [h24]
    omega
  iintro ⟨Hruntime, Hglobal, Hframe, Hworkspace, Hcont⟩
  isimp only [SortFrameOwn] at Hframe
  icases Hframe with
    ⟨%c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8, %c9, %c10, %c11,
      Hc0, Hc1, Hc2, Hc3, Hc4, Hc5, Hc6, Hc7, Hc8, Hc9, Hc10, Hc11⟩
  iapply sort_data_suffix_twp dataPtr length scratchPtr scratchLength frame mid
    c4 c5 hmidData hframe32 hresult20
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hc4]
  · iexact Hc4
  isplitl [Hc5]
  · iexact Hc5
  iintro Hruntime Hc4 Hc5
  iapply sort_scratch_suffix_to_second_recursive_call_twp
    dataPtr length scratchPtr scratchLength frame mid
    (dataPtr + (mid <<< 3)) (length - mid) c6 c7
    hmidScratch hframe32 hresult28
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hc6]
  · iexact Hc6
  isplitl [Hc7]
  · iexact Hc7
  iintro Hruntime Hc6 Hc7
  ihave HframeOwn : SortFrameOwn frame $$
      [Hc0 Hc1 Hc2 Hc3 Hc4 Hc5 Hc6 Hc7 Hc8 Hc9 Hc10 Hc11]
  · isimp only [SortFrameOwn]
    iexists c0
    iexists c1
    iexists c2
    iexists c3
    iexists (dataPtr + (mid <<< 3))
    iexists (length - mid)
    iexists (scratchPtr + (mid <<< 3))
    iexists (scratchLength - mid)
    iexists c8
    iexists c9
    iexists c10
    iexists c11
    iframe
  iapply Hcont $$ Hruntime Hglobal HframeOwn Hworkspace

/-- After the second recursive call, invoke generated `split_at` on the data
slice, load both returned descriptors, and stop exactly at merge `.call 127`.
No semantic property of either recursive call or of merge is assumed here. -/
theorem sort_split_to_merge_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame mid : UInt32)
    (oldFrame0 oldFrame4 oldFrame8 oldFrame12
      oldFrame16 oldFrame20 oldFrame24 oldFrame28
      oldResult0 oldResult4 oldResult8 oldResult12 : UInt32)
    (hmid : mid ≤ length)
    (hsplitFrameRoom : (frame - 32).toNat + 32 ≤ UInt32.size)
    (hfuncFrameRoom : frame.toNat + 48 ≤ UInt32.size)
    (hresultRoom : (frame + 32).toNat + 16 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 ((frame - 32) + 0) oldFrame0 ∗
      pointsTo_u32 ((frame - 32) + 4) oldFrame4 ∗
      pointsTo_u32 ((frame - 32) + 8) oldFrame8 ∗
      pointsTo_u32 ((frame - 32) + 12) oldFrame12 ∗
      pointsTo_u32 ((frame - 32) + 16) oldFrame16 ∗
      pointsTo_u32 ((frame - 32) + 20) oldFrame20 ∗
      pointsTo_u32 ((frame - 32) + 24) oldFrame24 ∗
      pointsTo_u32 ((frame - 32) + 28) oldFrame28 ∗
      pointsTo_u32 (frame + 32) oldResult0 ∗
      pointsTo_u32 (frame + 36) oldResult4 ∗
      pointsTo_u32 (frame + 40) oldResult8 ∗
      pointsTo_u32 (frame + 44) oldResult12 ∗
      ((runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 frame) ∗
        sliceDescriptorAt ((frame - 32) + 0) dataPtr mid ∗
        sliceDescriptorAt ((frame - 32) + 8)
          (dataPtr + (mid <<< 3)) (length - mid) ∗
        sliceDescriptorAt ((frame - 32) + 16) dataPtr mid ∗
        sliceDescriptorAt ((frame - 32) + 24)
          (dataPtr + (mid <<< 3)) (length - mid) ∗
        sliceDescriptorAt (frame + 32) dataPtr mid ∗
        sliceDescriptorAt (frame + 40)
          (dataPtr + (mid <<< 3)) (length - mid)) -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortSecondCallLocals frame mid dataPtr mid mid
                (dataPtr + (mid <<< 3)) (length - mid)
                (scratchLength - mid),
              [.i32 scratchLength, .i32 scratchPtr,
                .i32 (length - mid), .i32 (dataPtr + (mid <<< 3)),
                .i32 mid, .i32 dataPtr]⟩,
            sortAtMergeCall, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortSecondCallLocals frame mid dataPtr mid mid
            (dataPtr + (mid <<< 3)) (length - mid) (scratchLength - mid), []⟩,
        sortAfterSecondRecursiveCall, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h320, h321, h322, h323⟩ :=
    sortFullFrameSlotFacts frame 32 hfuncFrameRoom (by decide)
  obtain ⟨h360, h361, h362, h363⟩ :=
    sortFullFrameSlotFacts frame 36 hfuncFrameRoom (by decide)
  obtain ⟨h400, h401, h402, h403⟩ :=
    sortFullFrameSlotFacts frame 40 hfuncFrameRoom (by decide)
  obtain ⟨h440, h441, h442, h443⟩ :=
    sortFullFrameSlotFacts frame 44 hfuncFrameRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hf0, Hf4, Hf8, Hf12, Hf16, Hf20,
    Hf24, Hf28, Hr0, Hr4, Hr8, Hr12, Hcont⟩
  simp only [sortAfterSecondRecursiveCall, sortAtSecondRecursiveCall,
    sortAfterDataSuffix, sortAfterFirstRecursiveCall,
    sortAtFirstRecursiveCall, sortAfterFirstRange, sortAfterMid,
    sortRecursiveBody, sortAfterFrame, func126, List.drop]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (32 : UInt32) frame]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  have Hsplit := splitAt_call_twp (α := α)
    (frame + 32) dataPtr length mid 1050320 frame
    oldFrame0 oldFrame4 oldFrame8 oldFrame12
    oldFrame16 oldFrame20 oldFrame24 oldFrame28
    oldResult0 oldResult4 oldResult8 oldResult12
    hmid hsplitFrameRoom hresultRoom
    (callerLocals :=
      ⟨sortParams dataPtr length scratchPtr scratchLength,
        sortSecondCallLocals frame mid dataPtr mid mid
          (dataPtr + (mid <<< 3)) (length - mid) (scratchLength - mid), []⟩)
    (stack := []) (code := sortAfterSecondRecursiveCall.drop 8)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [sortAfterSecondRecursiveCall, sortAtSecondRecursiveCall,
    sortAfterDataSuffix, sortAfterFirstRecursiveCall,
    sortAtFirstRecursiveCall, sortAfterFirstRange, sortAfterMid,
    sortRecursiveBody, sortAfterFrame, func126,
    List.drop, List.append_nil] at Hsplit
  ihave Hr4At : pointsTo_u32 ((frame + 32) + 4) oldResult4 $$ [Hr4]
  · rw [show (frame + 32) + 4 = frame + 36 by bv_decide]
    iexact Hr4
  ihave Hr8At : pointsTo_u32 ((frame + 32) + 8) oldResult8 $$ [Hr8]
  · rw [show (frame + 32) + 8 = frame + 40 by bv_decide]
    iexact Hr8
  ihave Hr12At : pointsTo_u32 ((frame + 32) + 12) oldResult12 $$ [Hr12]
  · rw [show (frame + 32) + 12 = frame + 44 by bv_decide]
    iexact Hr12
  iapply Hsplit
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hf0]
  · iexact Hf0
  isplitl [Hf4]
  · iexact Hf4
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hf12]
  · iexact Hf12
  isplitl [Hf16]
  · iexact Hf16
  isplitl [Hf20]
  · iexact Hf20
  isplitl [Hf24]
  · iexact Hf24
  isplitl [Hf28]
  · iexact Hf28
  isplitl [Hr0]
  · iexact Hr0
  isplitl [Hr4At]
  · iexact Hr4At
  isplitl [Hr8At]
  · iexact Hr8At
  isplitl [Hr12At]
  · iexact Hr12At
  iintro Hpost
  icases Hpost with ⟨Hruntime, Hglobal, Hf0, Hf8, Hf16, Hf24,
    Hr0Desc, Hr8Desc⟩
  ihave Hr0Pair : pointsTo_u32 (frame + 32) dataPtr ∗
      pointsTo_u32 ((frame + 32) + 4) mid $$ [Hr0Desc]
  · iapply sort_sliceDescriptorAt_elim
    iexact Hr0Desc
  ihave Hr8Pair : pointsTo_u32 ((frame + 32) + 8)
      (dataPtr + (mid <<< 3)) ∗
      pointsTo_u32 (((frame + 32) + 8) + 4) (length - mid) $$ [Hr8Desc]
  · iapply sort_sliceDescriptorAt_elim
    iexact Hr8Desc
  icases Hr0Pair with ⟨Hr0, Hr4⟩
  icases Hr8Pair with ⟨Hr8, Hr12⟩
  iapply twp_localGet rfl
  iapply twp_load32 dataPtr h320 h321 h322 h323 $$ Hr0
  iintro Hr0
  iapply twp_localGet rfl
  ihave Hr4Plain : pointsTo_u32 (frame + 36) mid $$ [Hr4]
  · iapply sort_pointsTo_u32_at_eq
      (show (frame + 32) + 4 = frame + 36 by bv_decide)
    iexact Hr4
  iapply twp_load32 mid h360 h361 h362 h363 $$ Hr4Plain
  iintro Hr4
  iapply twp_localGet rfl
  ihave Hr8Plain : pointsTo_u32 (frame + 40)
      (dataPtr + (mid <<< 3)) $$ [Hr8]
  · iapply sort_pointsTo_u32_at_eq
      (show (frame + 32) + 8 = frame + 40 by bv_decide)
    iexact Hr8
  iapply twp_load32 (dataPtr + (mid <<< 3)) h400 h401 h402 h403 $$ Hr8Plain
  iintro Hr8
  iapply twp_localGet rfl
  ihave Hr12Plain : pointsTo_u32 (frame + 44) (length - mid) $$ [Hr12]
  · iapply sort_pointsTo_u32_at_eq
      (show ((frame + 32) + 8) + 4 = frame + 44 by bv_decide)
    iexact Hr12
  iapply twp_load32 (length - mid) h440 h441 h442 h443 $$ Hr12Plain
  iintro Hr12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [sortAtMergeCall, sortAfterSecondRecursiveCall,
    sortAtSecondRecursiveCall, sortAfterDataSuffix,
    sortAfterFirstRecursiveCall, sortAtFirstRecursiveCall,
    sortAfterFirstRange, sortAfterMid, sortRecursiveBody, sortAfterFrame,
    func126, List.drop]
  ihave Hr4Back : pointsTo_u32 ((frame + 32) + 4) mid $$ [Hr4]
  · iapply sort_pointsTo_u32_at_eq
      (show frame + 36 = (frame + 32) + 4 by bv_decide)
    iexact Hr4
  ihave Hr12Back : pointsTo_u32 ((frame + 40) + 4)
      (length - mid) $$ [Hr12]
  · iapply sort_pointsTo_u32_at_eq
      (show frame + 44 = (frame + 40) + 4 by bv_decide)
    iexact Hr12
  ispecialize Hcont $$
    [Hruntime Hglobal Hf0 Hf8 Hf16 Hf24 Hr0 Hr4Back Hr8 Hr12Back]
  · simp only [sliceDescriptorAt]
    iframe
  iapply Hcont

/-- Exact post-merge suffix.  The theorem does not assert what merge
produced: it receives arbitrary `merged` ownership at the scratch slice.
From there it executes generated clone-from-slice call 96, exits the outer
block, restores the shadow-stack global, and reaches the final `ret`. -/
theorem sort_copy_back_epilogue_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength frame stackTop mid : UInt32)
    (merged destination : List UInt64)
    (hscratchLength : scratchLength = length)
    (hnonempty : merged ≠ [])
    (hlengthValue : length.toNat = merged.length)
    (hlength : merged.length = destination.length)
    (hsourceRoom : scratchPtr.toNat + 8 * merged.length ≤ UInt32.size)
    (hdestinationRoom :
      dataPtr.toNat + 8 * destination.length ≤ UInt32.size)
    (hbytes : 8 * merged.length < UInt32.size)
    (hrestore : (48 : UInt32) + frame = stackTop)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      array64At scratchPtr merged ∗
      array64At dataPtr destination ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        array64At scratchPtr merged -∗
        array64At dataPtr merged -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortSecondCallLocals frame mid dataPtr mid mid
                (dataPtr + (mid <<< 3)) (length - mid)
                (scratchLength - mid), []⟩,
            [.ret], arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortSecondCallLocals frame mid dataPtr mid mid
            (dataPtr + (mid <<< 3)) (length - mid)
            (scratchLength - mid), []⟩,
        sortAfterMerge, arity, remainder, sortOuterFrame :: controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  subst scratchLength
  iintro ⟨Hruntime, Hglobal, Hscratch, Hdata, Hcont⟩
  simp only [sortAfterMerge, sortAtMergeCall,
    sortAfterSecondRecursiveCall, sortAtSecondRecursiveCall,
    sortAfterDataSuffix, sortAfterFirstRecursiveCall,
    sortAtFirstRecursiveCall, sortAfterFirstRange, sortAfterMid,
    sortRecursiveBody, sortAfterFrame, func126, List.drop]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_call_cloneFromSlice dataPtr scratchPtr length 1050336
    merged destination hnonempty hlengthValue hlength hsourceRoom
    hdestinationRoom hbytes
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hscratch]
  · iexact Hscratch
  isplitl [Hdata]
  · iexact Hdata
  iintro Hruntime Hscratch Hdata
  iapply twp_exitControl (by decide)
  simp only [sortOuterFrame, sortAfterOuterBlock, sortAfterFrame,
    sortRecursiveBody, func126, List.take_zero, List.nil_append,
    List.drop]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [hrestore]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [sortParams, sortSecondCallLocals]
  iapply Hcont $$ Hruntime Hglobal Hscratch Hdata

/-- Exact total rule for the generated base-case path of `func126`.

The continuation is deliberately positioned at the final generated `ret`,
so the rule is polymorphic in the surrounding call stack and composes with a
later direct-call rule.  Array ownership in the contract makes explicit that
the base case is an in-place identity operation.
-/
theorem sort_base_path_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength stackTop : UInt32)
    (input scratch : List UInt64)
    (hsmall : length ≤ 1)
    (hinputLength : input.length = length.toNat)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      array64At dataPtr input ∗
      array64At scratchPtr scratch ∗
      (⌜SortRel input input⌝ -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        array64At dataPtr input -∗
        array64At scratchPtr scratch -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortFramedLocals (stackTop - 48), []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortZeroLocals, []⟩,
        func126, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have hsmallNat : input.length ≤ 1 := by
    rw [hinputLength]
    rw [UInt32.le_iff_toNat_le] at hsmall
    simpa using hsmall
  iintro ⟨Hglobal, Hinput, Hscratch, Hcont⟩
  simp only [func126]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [sortParams, sortZeroLocals]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_leU (result := 1) (by simp [hsmall])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) rfl
  simp only [sortFramedLocals, List.take_zero, List.drop_zero,
    List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (48 : UInt32) + (stackTop - 48) = stackTop by bv_decide]
    iexact Hglobal
  iapply Hcont $$ %(sortRel_base hsmallNat) HglobalTop Hinput Hscratch

/-- Total direct-call rule for the generated base case at absolute function
index `128`.  The caller receives its original operand stack and a semantic
`SortRel` witness, with both arrays and the runtime-module capability intact.
-/
theorem sort_base_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength stackTop : UInt32)
    (input scratch : List UInt64)
    (hsmall : length ≤ 1)
    (hinputLength : input.length = length.toNat)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      array64At dataPtr input ∗
      array64At scratchPtr scratch ∗
      (runtimeModuleOwn «module» -∗
        ⌜SortRel input input⌝ -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        array64At dataPtr input -∗
        array64At scratchPtr scratch -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 scratchLength, .i32 scratchPtr, .i32 length, .i32 dataPtr] ++
            stack },
        .call 128 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hinput, Hscratch, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 128 sortFunction
      (by decide) sort_index $$ Hruntime
  iintro Hruntime
  simp [sortFunction, func126Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  have Hbody := sort_base_path_twp (α := α)
    dataPtr length scratchPtr scratchLength stackTop input scratch
    hsmall hinputLength (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [sortParams, sortZeroLocals] at Hbody
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinput]
  · iexact Hinput
  isplitl [Hscratch]
  · iexact Hscratch
  iintro %Hsort Hglobal Hinput Hscratch
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append,
    List.drop_eq_nil_of_le (by decide : 4 ≤
      [.i32 dataPtr, .i32 length, .i32 scratchPtr, .i32 scratchLength].length)]
  iapply Hcont $$ Hruntime %Hsort Hglobal Hinput Hscratch

/-- Base branch lifted to the recursive workspace contract used by the total
induction.  Neither the array contents nor any workspace frame changes. -/
theorem sort_body_small_workspace_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dataPtr length scratchPtr scratchLength stackTop : UInt32)
    (input scratch : List UInt64) (depth : Nat)
    (hsmall : length ≤ 1)
    (hinputLength : input.length = length.toNat)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      array64At dataPtr input ∗
      array64At scratchPtr scratch ∗
      SortWorkspace stackTop depth ∗
      (runtimeModuleOwn «module» -∗
        ⌜SortRel input input⌝ -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        array64At dataPtr input -∗
        array64At scratchPtr scratch -∗
        SortWorkspace stackTop depth -∗
        WP (.running
          ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
              sortFramedLocals (stackTop - 48), []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨sortParams dataPtr length scratchPtr scratchLength,
          sortZeroLocals, []⟩,
        func126, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hinput, Hscratch, Hworkspace, Hcont⟩
  iapply sort_base_path_twp dataPtr length scratchPtr scratchLength stackTop
    input scratch hsmall hinputLength
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinput]
  · iexact Hinput
  isplitl [Hscratch]
  · iexact Hscratch
  iintro %Hsort Hglobal Hinput Hscratch
  iapply Hcont $$ Hruntime %Hsort Hglobal Hinput Hscratch Hworkspace

end Project.Mergesort.SortFunctionProof
