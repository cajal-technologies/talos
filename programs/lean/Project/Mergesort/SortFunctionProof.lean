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

theorem sortRel_base {input : List UInt64} (hlength : input.length ≤ 1) :
    SortRel input input :=
  .small hlength

theorem sortPost_base {input : List UInt64} (hlength : input.length ≤ 1) :
    SortPost input input := by
  exact sortedPermutation_of_sortRel (.small hlength)

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
