import Project.Mergesort.CoreProof
import Project.Mergesort.RangeProof

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

def sortParams
    (dataPtr length scratchPtr scratchLength : UInt32) : List Value :=
  [.i32 dataPtr, .i32 length, .i32 scratchPtr, .i32 scratchLength]

/-- The typed zero-initialized locals of `func126Def`. -/
def sortZeroLocals : List Value :=
  [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

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

end Project.Mergesort.SortFunctionProof
