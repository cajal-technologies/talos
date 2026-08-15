import Project.Mergesort.CoreProof
import Project.Mergesort.RangeProof

/-!
# Generated `merge::<u64>` function proof

This file verifies the generated control-flow of local `func125` in layers.
The first layer below covers its exact shadow-stack prologue and exposes the
three counter slots used by the main and remainder loops.
-/

namespace Project.Mergesort.MergeFunctionProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.CoreProof

def mergeParams
    (leftPtr leftLength rightPtr rightLength scratchPtr scratchLength : UInt32) :
    List Value :=
  [.i32 leftPtr, .i32 leftLength, .i32 rightPtr, .i32 rightLength,
    .i32 scratchPtr, .i32 scratchLength]

/-- The typed zero-initialized locals of `func125Def`. -/
def mergeZeroLocals : List Value :=
  [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
    .i64 0, .i32 0, .i64 0, .i32 0, .i32 0, .i64 0, .i32 0,
    .i32 0, .i64 0, .i32 0]

/-- Locals immediately after `func125` installs its sixteen-byte frame. -/
def mergeInitializedLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
    .i64 0, .i32 0, .i64 0, .i32 0, .i32 0, .i64 0, .i32 0,
    .i32 0, .i64 0, .i32 0]

/-- The generated merge body after its fifteen-instruction prologue. -/
def mergeAfterInit : Program := func125.drop 15

/-- The body nested under the generated outer block and main loop. -/
def mergeMainLoopBody : Program :=
  match mergeAfterInit with
  | .block 0 0 (.loop 0 0 body :: _) :: _ => body
  | _ => []

/-- The main-loop body after both nonempty guards and `local 7 := i`. -/
def mergeMainAfterGuards : Program := mergeMainLoopBody.drop 19

/-- Generated code following the main-loop block. -/
def mergeAfterMain : Program := mergeAfterInit.drop 1

/-- Body of the outer remainder loop, which first tests/copies the left slice
and then enters the nested right remainder loop. -/
def mergeLeftLoopBody : Program :=
  match mergeAfterMain with
  | .loop 0 0 body :: _ => body
  | _ => []

def mergeLeftGuardBody : Program :=
  match mergeLeftLoopBody with
  | .block 0 0 body :: _ => body
  | _ => []

/-- Left-copy step reached by taking the generated depth-zero guard branch. -/
def mergeLeftRemainderStep : Program := mergeLeftLoopBody.drop 1

/-- Body installed in the control frame after entering the generated left
copy/update block. -/
def mergeLeftUpdateBody : Program :=
  match mergeLeftRemainderStep.drop 3 with
  | .block 0 0 body :: _ => body
  | _ => []

/-- Nested right-loop program reached when the left slice is exhausted. -/
def mergeAfterLeftGuard : Program := mergeLeftGuardBody.drop 7

def mergeRightLoopBody : Program :=
  match mergeAfterLeftGuard with
  | .loop 0 0 body :: _ => body
  | _ => []

def mergeRightGuardBody : Program :=
  match mergeRightLoopBody with
  | .block 0 0 body :: _ => body
  | _ => []

/-- Right-copy step reached by taking the nested guard branch. -/
def mergeRightRemainderStep : Program := mergeRightLoopBody.drop 1

/-- Body installed in the control frame after entering the generated right
copy/update block. -/
def mergeRightUpdateBody : Program :=
  match mergeRightRemainderStep.drop 3 with
  | .block 0 0 body :: _ => body
  | _ => []

/-- Generated stack restoration and return after both slices are exhausted. -/
def mergeEpilogue : Program := mergeRightGuardBody.drop 7

private theorem slotFacts (base : UInt32) (offset : Nat)
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

/-- Exact total rule for the generated shadow-stack prologue of `func125`.

It subtracts sixteen from the stack-pointer global, installs that value as
local 6, and initializes the `i`, `j`, and `k` counter words at frame offsets
4, 8, and 12.  The continuation starts at the generated outer merge block.
-/
theorem merge_init_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr leftLength rightPtr rightLength scratchPtr scratchLength
      stackTop : UInt32)
    (oldI oldJ oldK : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 4) oldI ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldJ ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldK ∗
      ((globalPointsTo 0 (.i32 (stackTop - 16)) ∗
        pointsTo_u32 ((stackTop - 16) + 4) 0 ∗
        pointsTo_u32 ((stackTop - 16) + 8) 0 ∗
        pointsTo_u32 ((stackTop - 16) + 12) 0) -∗
        WP (.running
          ⟨⟨mergeParams leftPtr leftLength rightPtr rightLength
                scratchPtr scratchLength,
              mergeInitializedLocals (stackTop - 16), []⟩,
            mergeAfterInit, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨mergeParams leftPtr leftLength rightPtr rightLength
            scratchPtr scratchLength,
          mergeZeroLocals, []⟩,
        func125, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  obtain ⟨hi0, hi1, hi2, hi3⟩ :=
    slotFacts frame 4 hframeRoom (by decide)
  obtain ⟨hj0, hj1, hj2, hj3⟩ :=
    slotFacts frame 8 hframeRoom (by decide)
  obtain ⟨hk0, hk1, hk2, hk3⟩ :=
    slotFacts frame 12 hframeRoom (by decide)
  iintro ⟨Hglobal, Hi, Hj, Hk, Hcont⟩
  simp only [func125]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [mergeParams, mergeZeroLocals]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldI hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldJ hj0 hj1 hj2 hj3 $$ Hj
  iintro Hj
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldK hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  simp only [mergeAfterInit, mergeInitializedLocals, func125, List.drop,
    List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply Hcont
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hi]
  · iexact Hi
  isplitl [Hj]
  · iexact Hj
  · iexact Hk

/-- Exact successful-path rule for the two generated main-loop guards.

Under `i < leftLength` and `j < rightLength`, both bounds checks fall
through.  The code then reloads `i` and records it in generated local 7,
which is the first temporary used by the nested element-selection blocks.
-/
theorem merge_main_guards_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr leftLength rightPtr rightLength scratchPtr scratchLength
      frame i j : UInt32)
    (localValues : List Value) (localsAfterI : Locals)
    (hi : i < leftLength) (hj : j < rightLength)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    (hframe :
      (⟨mergeParams leftPtr leftLength rightPtr rightLength
          scratchPtr scratchLength, localValues, []⟩ : Locals).get 6 =
        some (.i32 frame))
    (hsetI :
      (⟨mergeParams leftPtr leftLength rightPtr rightLength
          scratchPtr scratchLength, localValues, [.i32 i]⟩ : Locals).set?
          7 (.i32 i) = some localsAfterI)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 (frame + 4) i ∗
      pointsTo_u32 (frame + 8) j ∗
      ((pointsTo_u32 (frame + 4) i ∗
        pointsTo_u32 (frame + 8) j) -∗
        WP (.running
          ⟨{ localsAfterI with values := [] }, mergeMainAfterGuards,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨mergeParams leftPtr leftLength rightPtr rightLength
            scratchPtr scratchLength,
          localValues, []⟩,
        mergeMainLoopBody, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hi0, hi1, hi2, hi3⟩ :=
    slotFacts frame 4 hframeRoom (by decide)
  obtain ⟨hj0, hj1, hj2, hj3⟩ :=
    slotFacts frame 8 hframeRoom (by decide)
  iintro ⟨Hi, Hj, Hcont⟩
  simp only [mergeMainLoopBody, mergeAfterInit, func125, List.drop]
  iapply twp_localGet hframe
  iapply twp_load32 i hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1) (by simp [hi])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet hframe
  iapply twp_load32 j hj0 hj1 hj2 hj3 $$ Hj
  iintro Hj
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1) (by simp [hj])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet hframe
  iapply twp_load32 i hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_localSet hsetI
  simp only [mergeMainAfterGuards, mergeMainLoopBody, mergeAfterInit,
    func125, List.drop]
  iapply Hcont
  isplitl [Hi]
  · iexact Hi
  · iexact Hj

/-- Generated write/increment/backedge target for the branch which takes the
current element from the left slice. -/
def mergeTakeLeftUpdate : Program :=
  [.localGet 4, .localGet 16, .const 3, .shl, .add, .localGet 15,
    .store64 0,
    .localGet 6, .localGet 6, .load32 4, .const 1, .add, .store32 4,
    .localGet 6, .localGet 6, .load32 12, .const 1, .add, .store32 12,
    .br 1]

/-- Generated write/increment/backedge target for the branch which takes the
current element from the right slice. -/
def mergeTakeRightUpdate : Program :=
  [.localGet 4, .localGet 14, .const 3, .shl, .add, .localGet 13,
    .store64 0,
    .localGet 6, .localGet 6, .load32 8, .const 1, .add, .store32 8,
    .localGet 6, .localGet 6, .load32 12, .const 1, .add, .store32 12,
    .br 5]

/- One exact generated left-selection update.  Besides executing the Wasm
store and both counter increments, the rule exports the corresponding
`MergeSlicesInvariant.takeLeft` transition to the continuation. -/
set_option maxHeartbeats 2000000 in
theorem merge_takeLeft_update_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr rightPtr scratchPtr frame : UInt32)
    (left right scratch : List UInt64) (i j k : Nat)
    (emitted : List UInt64) (x y : UInt64)
    (localValues : List Value)
    (hinv : MergeSlicesInvariant left right scratch i j k emitted)
    (hi : i < left.length) (hj : j < right.length)
    (hx : left[i]? = some x) (hy : right[j]? = some y)
    (hxy : x ≤ y)
    (hscratchFit : scratchPtr.toNat + 8 * scratch.length ≤ UInt32.size)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    (hframe :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 6 =
        some (.i32 frame))
    (hscratch :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 4 =
        some (.i32 scratchPtr))
    (hkLocal :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 16 =
        some (.i32 (UInt32.ofNat k)))
    (hxLocal :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 15 =
        some (.i64 x))
    {arity : Nat} {remainder : List Value}
    {code targetCode : Program}
    {controls targetControls : List ControlFrame}
    {targetValues : List Value} {calls : List CallFrame}
    (htarget : branchTarget? arity 1 controls [] =
      some (targetCode, targetControls, targetValues)) :
    array64At scratchPtr scratch ∗
      pointsTo_u32 (frame + 4) (UInt32.ofNat i) ∗
      pointsTo_u32 (frame + 12) (UInt32.ofNat k) ∗
      ((⌜MergeSlicesInvariant left right (scratch.set k x)
          (i + 1) j (k + 1) (emitted ++ [x])⌝ ∗
        array64At scratchPtr (scratch.set k x) ∗
        pointsTo_u32 (frame + 4) (UInt32.ofNat i + 1) ∗
        pointsTo_u32 (frame + 12) (UInt32.ofNat k + 1)) -∗
        WP (.running
          ⟨⟨mergeParams leftPtr (UInt32.ofNat left.length)
                rightPtr (UInt32.ofNat right.length) scratchPtr
                (UInt32.ofNat scratch.length),
              localValues, targetValues⟩,
            targetCode, arity, remainder, targetControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨mergeParams leftPtr (UInt32.ofNat left.length)
            rightPtr (UInt32.ofNat right.length) scratchPtr
            (UInt32.ofNat scratch.length), localValues, []⟩,
        mergeTakeLeftUpdate ++ code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  have hk : k < scratch.length := hinv.k_lt hi
  have hnext := hinv.takeLeft hi hj hx hy hxy
  obtain ⟨hi0, hi1, hi2, hi3⟩ :=
    slotFacts frame 4 hframeRoom (by decide)
  obtain ⟨hk0, hk1, hk2, hk3⟩ :=
    slotFacts frame 12 hframeRoom (by decide)
  iintro ⟨Hscratch, Hi, Hk, Hcont⟩
  simp only [mergeTakeLeftUpdate, List.cons_append, List.nil_append]
  iapply twp_store64AtShift_raw hk hscratchFit hscratch hkLocal hxLocal
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hscratch
  iapply twp_localGet hframe
  iapply twp_localGet (by simpa using hframe)
  iapply twp_load32 (UInt32.ofNat i) hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 1]
  iapply twp_store32 (UInt32.ofNat i) hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_localGet hframe
  iapply twp_localGet (by simpa using hframe)
  iapply twp_load32 (UInt32.ofNat k) hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 1]
  iapply twp_store32 (UInt32.ofNat k) hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  iapply twp_br htarget
  iapply Hcont
  isplitr
  · ipureintro
    exact hnext
  isplitl [Hscratch]
  · iexact Hscratch
  isplitl [Hi]
  · iexact Hi
  · iexact Hk

/- Symmetric exact update for the generated right-selection target, exporting
`MergeSlicesInvariant.takeRight` to its continuation. -/
set_option maxHeartbeats 2000000 in
theorem merge_takeRight_update_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr rightPtr scratchPtr frame : UInt32)
    (left right scratch : List UInt64) (i j k : Nat)
    (emitted : List UInt64) (x y : UInt64)
    (localValues : List Value)
    (hinv : MergeSlicesInvariant left right scratch i j k emitted)
    (hi : i < left.length) (hj : j < right.length)
    (hx : left[i]? = some x) (hy : right[j]? = some y)
    (hxy : ¬x ≤ y)
    (hscratchFit : scratchPtr.toNat + 8 * scratch.length ≤ UInt32.size)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    (hframe :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 6 =
        some (.i32 frame))
    (hscratch :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 4 =
        some (.i32 scratchPtr))
    (hkLocal :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 14 =
        some (.i32 (UInt32.ofNat k)))
    (hyLocal :
      (⟨mergeParams leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat scratch.length), localValues, []⟩ : Locals).get 13 =
        some (.i64 y))
    {arity : Nat} {remainder : List Value}
    {code targetCode : Program}
    {controls targetControls : List ControlFrame}
    {targetValues : List Value} {calls : List CallFrame}
    (htarget : branchTarget? arity 5 controls [] =
      some (targetCode, targetControls, targetValues)) :
    array64At scratchPtr scratch ∗
      pointsTo_u32 (frame + 8) (UInt32.ofNat j) ∗
      pointsTo_u32 (frame + 12) (UInt32.ofNat k) ∗
      ((⌜MergeSlicesInvariant left right (scratch.set k y)
          i (j + 1) (k + 1) (emitted ++ [y])⌝ ∗
        array64At scratchPtr (scratch.set k y) ∗
        pointsTo_u32 (frame + 8) (UInt32.ofNat j + 1) ∗
        pointsTo_u32 (frame + 12) (UInt32.ofNat k + 1)) -∗
        WP (.running
          ⟨⟨mergeParams leftPtr (UInt32.ofNat left.length)
                rightPtr (UInt32.ofNat right.length) scratchPtr
                (UInt32.ofNat scratch.length),
              localValues, targetValues⟩,
            targetCode, arity, remainder, targetControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨mergeParams leftPtr (UInt32.ofNat left.length)
            rightPtr (UInt32.ofNat right.length) scratchPtr
            (UInt32.ofNat scratch.length), localValues, []⟩,
        mergeTakeRightUpdate ++ code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  have hk : k < scratch.length := hinv.k_lt hi
  have hnext := hinv.takeRight hi hj hx hy hxy
  obtain ⟨hj0, hj1, hj2, hj3⟩ :=
    slotFacts frame 8 hframeRoom (by decide)
  obtain ⟨hk0, hk1, hk2, hk3⟩ :=
    slotFacts frame 12 hframeRoom (by decide)
  iintro ⟨Hscratch, Hj, Hk, Hcont⟩
  simp only [mergeTakeRightUpdate, List.cons_append, List.nil_append]
  iapply twp_store64AtShift_raw hk hscratchFit hscratch hkLocal hyLocal
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hscratch
  iapply twp_localGet hframe
  iapply twp_localGet (by simpa using hframe)
  iapply twp_load32 (UInt32.ofNat j) hj0 hj1 hj2 hj3 $$ Hj
  iintro Hj
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 1]
  iapply twp_store32 (UInt32.ofNat j) hj0 hj1 hj2 hj3 $$ Hj
  iintro Hj
  iapply twp_localGet hframe
  iapply twp_localGet (by simpa using hframe)
  iapply twp_load32 (UInt32.ofNat k) hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 1]
  iapply twp_store32 (UInt32.ofNat k) hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  iapply twp_br htarget
  iapply Hcont
  isplitr
  · ipureintro
    exact hnext
  isplitl [Hscratch]
  · iexact Hscratch
  isplitl [Hj]
  · iexact Hj
  · iexact Hk

/-- The exact loaded-value comparison and two-way dispatch emitted inside
`func125`'s nested selection blocks. -/
def mergeLoadedCompare : Program :=
  [.localGet 8, .load64 0, .localGet 10, .load64 0, .leUI64,
    .const 1, .and, .br_if 2, .br 1]

private def Load64Facts (address : UInt32) : Prop :=
  ((address + 1).toNat = address.toNat + 1) ∧
  ((address + 2).toNat = address.toNat + 2) ∧
  ((address + 3).toNat = address.toNat + 3) ∧
  ((address + 4).toNat = address.toNat + 4) ∧
  ((address + 5).toNat = address.toNat + 5) ∧
  ((address + 6).toNat = address.toNat + 6) ∧
  ((address + 7).toNat = address.toNat + 7)

/-- Typed generated locals used while proving one main-loop iteration.  The
arguments correspond to absolute local indices 6 through 22. -/
def mergeSelectionLocals
    (l6 l7 l8 l9 l10 l11 l12 : UInt32)
    (l13 : UInt64) (l14 : UInt32) (l15 : UInt64)
    (l16 l17 : UInt32) (l18 : UInt64) (l19 l20 : UInt32)
    (l21 : UInt64) (l22 : UInt32) : List Value :=
  [.i32 l6, .i32 l7, .i32 l8, .i32 l9, .i32 l10, .i32 l11,
    .i32 l12, .i64 l13, .i32 l14, .i64 l15, .i32 l16, .i32 l17,
    .i64 l18, .i32 l19, .i32 l20, .i64 l21, .i32 l22]

private theorem load64Facts_array
    (base : UInt32) (length index : Nat)
    (hfit : base.toNat + 8 * length ≤ UInt32.size)
    (hindex : index < length) :
    Load64Facts (base + 8 * UInt32.ofNat index) := by
  let address := base + 8 * UInt32.ofNat index
  have haddress : address.toNat = base.toNat + 8 * index := by
    dsimp only [address]
    apply Mem.words64_slotAddr_toNat
    simp only [UInt32.size] at hfit ⊢
    omega
  have hroom : address.toNat + 8 ≤ UInt32.size := by
    rw [haddress]
    omega
  have hstep (n : Nat) (hn : 1 ≤ n ∧ n ≤ 7) :
      (address + UInt32.ofNat n).toNat = address.toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨hstep 1 (by omega), hstep 2 (by omega), hstep 3 (by omega),
    hstep 4 (by omega), hstep 5 (by omega), hstep 6 (by omega),
    hstep 7 (by omega)⟩

/- Exact total rule for the generated unsigned `u64` comparison.  A true
comparison takes branch depth two; a false comparison falls through the
conditional and takes branch depth one.  Both branches retain the loaded
words and receive the corresponding pure ordering fact. -/
set_option maxHeartbeats 2000000 in
theorem merge_loaded_compare_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues : List Value}
    (leftAddress rightAddress : UInt32) (x y : UInt64)
    (hleftLocal :
      (⟨params, localValues, []⟩ : Locals).get 8 =
        some (.i32 leftAddress))
    (hrightLocal :
      (⟨params, localValues, []⟩ : Locals).get 10 =
        some (.i32 rightAddress))
    (hleftFacts : Load64Facts leftAddress)
    (hrightFacts : Load64Facts rightAddress)
    {arity : Nat} {remainder : List Value} {code : Program}
    {controls leftControls rightControls : List ControlFrame}
    {leftCode rightCode : Program}
    {leftValues rightValues : List Value} {calls : List CallFrame}
    (hleftTarget : branchTarget? arity 2 controls [] =
      some (leftCode, leftControls, leftValues))
    (hrightTarget : branchTarget? arity 1 controls [] =
      some (rightCode, rightControls, rightValues)) :
    pointsTo_u64 leftAddress x ∗
      pointsTo_u64 rightAddress y ∗
      (((⌜x ≤ y⌝ ∗ pointsTo_u64 (leftAddress + 0) x ∗
          pointsTo_u64 (rightAddress + 0) y) -∗
        WP (.running
          ⟨⟨params, localValues, leftValues⟩, leftCode,
            arity, remainder, leftControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ∧
       ((⌜¬x ≤ y⌝ ∗ pointsTo_u64 (leftAddress + 0) x ∗
          pointsTo_u64 (rightAddress + 0) y) -∗
        WP (.running
          ⟨⟨params, localValues, rightValues⟩, rightCode,
            arity, remainder, rightControls, calls⟩ : Expr α)
          @ s; E [{ Φ }])) ⊢
    WP (.running
      ⟨⟨params, localValues, []⟩, mergeLoadedCompare ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  rcases hleftFacts with ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩
  rcases hrightFacts with ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩
  iintro ⟨Hleft, Hright, Hbranches⟩
  simp only [mergeLoadedCompare, List.cons_append, List.nil_append]
  iapply twp_localGet hleftLocal
  ihave HleftOffset : pointsTo_u64 (leftAddress + 0) x $$ [Hleft]
  · rw [UInt32.add_zero]
    iexact Hleft
  iapply twp_load64 x (by simp)
    (by simpa using hl1) (by simpa using hl2) (by simpa using hl3)
    (by simpa using hl4) (by simpa using hl5) (by simpa using hl6)
    (by simpa using hl7) $$ HleftOffset
  iintro HleftOffset
  iapply twp_localGet (by simpa using hrightLocal)
  ihave HrightOffset : pointsTo_u64 (rightAddress + 0) y $$ [Hright]
  · rw [UInt32.add_zero]
    iexact Hright
  iapply twp_load64 y (by simp)
    (by simpa using hr1) (by simpa using hr2) (by simpa using hr3)
    (by simpa using hr4) (by simpa using hr5) (by simpa using hr6)
    (by simpa using hr7) $$ HrightOffset
  iintro HrightOffset
  by_cases hxy : x ≤ y
  · iapply twp_leUI64 (result := 1) (by simp [hxy])
    iapply twp_const
    iapply twp_and
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply twp_brIf (by decide) hleftTarget
    ihave Hthen := BI.and_elim_l $$ Hbranches
    iapply Hthen
    isplitr
    · ipureintro
      exact hxy
    isplitl [HleftOffset]
    · iexact HleftOffset
    · iexact HrightOffset
  · iapply twp_leUI64 (result := 0) (by simp [hxy])
    iapply twp_const
    iapply twp_and
    rw [show (0 : UInt32) &&& 1 = 0 by decide]
    iapply twp_brIfZero
    iapply twp_br hrightTarget
    ihave Helse := BI.and_elim_r $$ Hbranches
    iapply Helse
    isplitr
    · ipureintro
      exact hxy
    isplitl [HleftOffset]
    · iexact HleftOffset
    · iexact HrightOffset

/-- The loop control frame surrounding `mergeMainLoopBody`. -/
def mergeLoopFrame (afterLoop : Program) : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := mergeMainLoopBody
    continuation := afterLoop
    belowStack := [] }

private theorem twp_loop_wf_family_from
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {ι : Type} (measure : ι → Nat)
    (locals : ι → Locals) (I : ι → IProp WasmHeapGF)
    (initial : ι) (initialLocals : Locals)
    {paramArity resultArity arity : Nat}
    {body code : Program} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hinitial : locals initial = initialLocals)
    (hbelow : belowStack = (locals initial).values.drop paramArity)
    (body_closes : ∀ current,
      ⊢@{IProp WasmHeapGF} (iprop%
        (∀ (next : ι), ⌜measure next < measure current⌝ -∗ I next -∗
          WP (loopBodyExpr (α := α) (locals next)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }]) -∗
        I current -∗
          WP (loopBodyExpr (α := α) (locals current)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }])) :
    I initial ⊢
      WP (.running
        ⟨initialLocals, .loop paramArity resultArity body :: code,
          arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] := by
  have closes : ∀ current,
      I current ⊢
        WP (loopBodyExpr (α := α) (locals current)
          paramArity resultArity arity body code remainder belowStack
          controls calls) @ s; E [{ Φ }] := by
    intro current
    induction hmeasure : measure current using Nat.strongRecOn
        generalizing current with
    | ind n ih =>
      subst n
      iintro HI
      iapply body_closes current
      · iintro %next %hnext Hnext
        ihave Hih := ih (measure next) hnext next rfl $$ Hnext
        iexact Hih
      · iexact HI
  simp only [loopBodyExpr] at closes
  subst initialLocals
  iintro HI
  iapply twp_loop (α := α)
  rw [← hbelow]
  ihave Hbody := closes initial $$ HI
  iexact Hbody

private theorem u32_ofNat_succ {n : Nat}
    (h : n + 1 < UInt32.size) :
    UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_add]
  have hn : n < UInt32.size := by omega
  rw [UInt32.toNat_ofNat_of_lt' hn]
  have hone : (1 : UInt32).toNat = 1 := by decide
  rw [hone, Nat.mod_eq_of_lt]
  · symm
    exact UInt32.toNat_ofNat_of_lt' h
  · simpa only [UInt32.size] using h

/-- Runtime data needed to describe the generated locals at a main-loop
backedge.  The merge data and all compiler temporaries travel together so the
well-founded family exactly matches the machine state. -/
structure MergeMainRuntimeState where
  scratch : List UInt64
  i : Nat
  j : Nat
  k : Nat
  emitted : List UInt64
  l7 : UInt32
  l8 : UInt32
  l9 : UInt32
  l10 : UInt32
  l11 : UInt32
  l12 : UInt32
  l13 : UInt64
  l14 : UInt32
  l15 : UInt64
  l16 : UInt32
  l17 : UInt32
  l18 : UInt64
  l19 : UInt32
  l20 : UInt32
  l21 : UInt64
  l22 : UInt32

def mergeMainRuntimeLocals
    (leftPtr rightPtr scratchPtr frame : UInt32)
    (left right : List UInt64) (state : MergeMainRuntimeState) : Locals :=
  ⟨mergeParams leftPtr (UInt32.ofNat left.length)
      rightPtr (UInt32.ofNat right.length) scratchPtr
      (UInt32.ofNat (left.length + right.length)),
    mergeSelectionLocals frame state.l7 state.l8 state.l9 state.l10
      state.l11 state.l12 state.l13 state.l14 state.l15 state.l16
      state.l17 state.l18 state.l19 state.l20 state.l21 state.l22,
    []⟩

def MergeMainRuntimeState.takeLeft
    (leftPtr rightPtr : UInt32) (x : UInt64)
    (state : MergeMainRuntimeState) : MergeMainRuntimeState :=
  { state with
    scratch := state.scratch.set state.k x
    i := state.i + 1
    k := state.k + 1
    emitted := state.emitted ++ [x]
    l7 := UInt32.ofNat state.i
    l8 := leftPtr + 8 * UInt32.ofNat state.i
    l9 := UInt32.ofNat state.j
    l10 := rightPtr + 8 * UInt32.ofNat state.j
    l12 := UInt32.ofNat state.i
    l15 := x
    l16 := UInt32.ofNat state.k }

def MergeMainRuntimeState.takeRight
    (leftPtr rightPtr : UInt32) (y : UInt64)
    (state : MergeMainRuntimeState) : MergeMainRuntimeState :=
  { state with
    scratch := state.scratch.set state.k y
    j := state.j + 1
    k := state.k + 1
    emitted := state.emitted ++ [y]
    l7 := UInt32.ofNat state.i
    l8 := leftPtr + 8 * UInt32.ofNat state.i
    l9 := UInt32.ofNat state.j
    l10 := rightPtr + 8 * UInt32.ofNat state.j
    l11 := UInt32.ofNat state.j
    l13 := y
    l14 := UInt32.ofNat state.k }

def MergeMainRuntimeState.takeRemainingLeft
    (x : UInt64) (state : MergeMainRuntimeState) : MergeMainRuntimeState :=
  { state with
    scratch := state.scratch.set state.k x
    i := state.i + 1
    k := state.k + 1
    emitted := state.emitted ++ [x]
    l20 := UInt32.ofNat state.i
    l21 := x
    l22 := UInt32.ofNat state.k }

def MergeMainRuntimeState.takeRemainingRight
    (y : UInt64) (state : MergeMainRuntimeState) : MergeMainRuntimeState :=
  { state with
    scratch := state.scratch.set state.k y
    j := state.j + 1
    k := state.k + 1
    emitted := state.emitted ++ [y]
    l17 := UInt32.ofNat state.j
    l18 := y
    l19 := UInt32.ofNat state.k }

/- One complete generated main-loop iteration, from the nested selection
blocks through the comparison, selected-value safety checks, scratch write,
counter updates, and loop backedge. -/
set_option maxHeartbeats 8000000 in
theorem merge_main_iteration_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr rightPtr scratchPtr frame : UInt32)
    (left right scratch : List UInt64) (i j k : Nat)
    (emitted : List UInt64) (x y : UInt64)
    (a8 a9 a10 a11 a12 a14 a16 a17 a19 a20 a22 : UInt32)
    (v13 v15 v18 v21 : UInt64)
    (hinv : MergeSlicesInvariant left right scratch i j k emitted)
    (hi : i < left.length) (hj : j < right.length)
    (hx : left[i]? = some x) (hy : right[j]? = some y)
    (hleftFit : leftPtr.toNat + 8 * left.length ≤ UInt32.size)
    (hrightFit : rightPtr.toNat + 8 * right.length ≤ UInt32.size)
    (hscratchFit : scratchPtr.toNat + 8 * scratch.length ≤ UInt32.size)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value} {afterLoop : Program}
    {outerControls : List ControlFrame} {calls : List CallFrame} :
    array64At leftPtr left ∗ array64At rightPtr right ∗
      array64At scratchPtr scratch ∗
      pointsTo_u32 (frame + 4) (UInt32.ofNat i) ∗
      pointsTo_u32 (frame + 8) (UInt32.ofNat j) ∗
      pointsTo_u32 (frame + 12) (UInt32.ofNat k) ∗
      (((⌜x ≤ y⌝ ∗
          ⌜MergeSlicesInvariant left right (scratch.set k x)
            (i + 1) j (k + 1) (emitted ++ [x])⌝ ∗
          array64At leftPtr left ∗ array64At rightPtr right ∗
          array64At scratchPtr (scratch.set k x) ∗
          pointsTo_u32 (frame + 4) (UInt32.ofNat i + 1) ∗
          pointsTo_u32 (frame + 8) (UInt32.ofNat j) ∗
          pointsTo_u32 (frame + 12) (UInt32.ofNat k + 1)) -∗
        WP (.running
          ⟨⟨mergeParams leftPtr (UInt32.ofNat left.length)
                rightPtr (UInt32.ofNat right.length) scratchPtr
                (UInt32.ofNat scratch.length),
              mergeSelectionLocals frame (UInt32.ofNat i)
                (leftPtr + 8 * UInt32.ofNat i) (UInt32.ofNat j)
                (rightPtr + 8 * UInt32.ofNat j) a11 (UInt32.ofNat i)
                v13 a14 x (UInt32.ofNat k) a17 v18 a19 a20 v21 a22,
              []⟩,
            mergeMainLoopBody, arity, remainder,
            mergeLoopFrame afterLoop :: outerControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ∧
       ((⌜¬x ≤ y⌝ ∗
          ⌜MergeSlicesInvariant left right (scratch.set k y)
            i (j + 1) (k + 1) (emitted ++ [y])⌝ ∗
          array64At leftPtr left ∗ array64At rightPtr right ∗
          array64At scratchPtr (scratch.set k y) ∗
          pointsTo_u32 (frame + 4) (UInt32.ofNat i) ∗
          pointsTo_u32 (frame + 8) (UInt32.ofNat j + 1) ∗
          pointsTo_u32 (frame + 12) (UInt32.ofNat k + 1)) -∗
        WP (.running
          ⟨⟨mergeParams leftPtr (UInt32.ofNat left.length)
                rightPtr (UInt32.ofNat right.length) scratchPtr
                (UInt32.ofNat scratch.length),
              mergeSelectionLocals frame (UInt32.ofNat i)
                (leftPtr + 8 * UInt32.ofNat i) (UInt32.ofNat j)
                (rightPtr + 8 * UInt32.ofNat j) (UInt32.ofNat j) a12
                y (UInt32.ofNat k) v15 a16 a17 v18 a19 a20 v21 a22,
              []⟩,
            mergeMainLoopBody, arity, remainder,
            mergeLoopFrame afterLoop :: outerControls, calls⟩ : Expr α)
          @ s; E [{ Φ }])) ⊢
    WP (.running
      ⟨⟨mergeParams leftPtr (UInt32.ofNat left.length)
            rightPtr (UInt32.ofNat right.length) scratchPtr
            (UInt32.ofNat scratch.length),
          mergeSelectionLocals frame (UInt32.ofNat i) a8 a9 a10 a11 a12
            v13 a14 v15 a16 a17 v18 a19 a20 v21 a22, []⟩,
        mergeMainAfterGuards, arity, remainder,
        mergeLoopFrame afterLoop :: outerControls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let leftAddress := leftPtr + 8 * UInt32.ofNat i
  let rightAddress := rightPtr + 8 * UInt32.ofNat j
  have hleftFacts := load64Facts_array leftPtr left.length i hleftFit hi
  have hrightFacts := load64Facts_array rightPtr right.length j hrightFit hj
  have hleftLength : left.length < UInt32.size := by
    simp only [UInt32.size] at hleftFit ⊢
    omega
  have hrightLength : right.length < UInt32.size := by
    simp only [UInt32.size] at hrightFit ⊢
    omega
  have hiU : UInt32.ofNat i < UInt32.ofNat left.length := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' (by omega),
      UInt32.toNat_ofNat_of_lt' hleftLength]
    exact hi
  have hjU : UInt32.ofNat j < UInt32.ofNat right.length := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' (by omega),
      UInt32.toNat_ofNat_of_lt' hrightLength]
    exact hj
  have hxElem : left[i] = x := by
    have hxOption := hx
    rw [List.getElem?_eq_getElem hi] at hxOption
    exact Option.some.inj hxOption
  have hyElem : right[j] = y := by
    have hyOption := hy
    rw [List.getElem?_eq_getElem hj] at hyOption
    exact Option.some.inj hyOption
  have hk : k < scratch.length := hinv.k_lt hi
  have hscratchLength : scratch.length < UInt32.size := by
    simp only [UInt32.size] at hscratchFit ⊢
    omega
  have hkU : UInt32.ofNat k < UInt32.ofNat scratch.length := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' (by omega),
      UInt32.toNat_ofNat_of_lt' hscratchLength]
    exact hk
  obtain ⟨hi0, hi1, hi2, hi3⟩ :=
    slotFacts frame 4 hframeRoom (by decide)
  obtain ⟨hj0, hj1, hj2, hj3⟩ :=
    slotFacts frame 8 hframeRoom (by decide)
  obtain ⟨hk0, hk1, hk2, hk3⟩ :=
    slotFacts frame 12 hframeRoom (by decide)
  iintro ⟨Hleft, Hright, Hscratch, Hi, Hj, Hk, Hbranches⟩
  simp only [mergeMainAfterGuards, mergeMainLoopBody, mergeAfterInit,
    func125, List.drop]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1) (by simp [hiU])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  rw [shiftAddress64_eq]
  iapply twp_localSet rfl
  simp only [mergeSelectionLocals, mergeParams, List.set,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat j) hj0 hj1 hj2 hj3 $$ Hj
  iintro Hj
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1) (by simp [hjU])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  rw [shiftAddress64_eq]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.take_zero, List.nil_append]
  ihave HleftAt := array64At_get leftPtr left i hi $$ Hleft
  icases HleftAt with ⟨HleftWord, HleftClose⟩
  ihave HrightAt := array64At_get rightPtr right j hj $$ Hright
  icases HrightAt with ⟨HrightWord, HrightClose⟩
  rw [show
    [.localGet 8, .load64 0, .localGet 10, .load64 0, .leUI64,
      .const 1, .and, .br_if 2, .br 1] = mergeLoadedCompare by rfl]
  rw [← List.append_nil mergeLoadedCompare]
  iapply merge_loaded_compare_twp
      (leftAddress := leftAddress) (rightAddress := rightAddress)
      (x := x) (y := y) rfl rfl hleftFacts hrightFacts
      (hleftTarget := by rfl) (hrightTarget := by rfl)
  isplitl [HleftWord]
  · dsimp only [leftAddress]
    rw [← hxElem]
    iexact HleftWord
  isplitl [HrightWord]
  · dsimp only [rightAddress]
    rw [← hyElem]
    iexact HrightWord
  isplit
  · iintro ⟨%hxy, HleftWord, HrightWord⟩
    ihave HleftOriginal :
        pointsTo_u64 (leftPtr + 8 * UInt32.ofNat i) left[i] $$ [HleftWord]
    · dsimp only [leftAddress]
      rw [UInt32.add_zero, hxElem]
      iexact HleftWord
    ihave Hleft := HleftClose $$ HleftOriginal
    ihave HrightOriginal :
        pointsTo_u64 (rightPtr + 8 * UInt32.ofNat j) right[j] $$ [HrightWord]
    · dsimp only [rightAddress]
      rw [UInt32.add_zero, hyElem]
      iexact HrightWord
    ihave Hright := HrightClose $$ HrightOriginal
    simp only [List.take_zero, List.nil_append]
    iapply twp_localGet rfl
    iapply twp_load32 (UInt32.ofNat i) hi0 hi1 hi2 hi3 $$ Hi
    iintro Hi
    iapply twp_localSet rfl
    simp only [List.set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_ltU (result := 1) (by simp [hiU])
    iapply twp_const
    iapply twp_and
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    iapply twp_load64AtShift_raw hi hleftFit rfl rfl
    isplitl [Hleft]
    · iexact Hleft
    iintro Hleft
    rw [hxElem]
    iapply twp_localSet rfl
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_localGet rfl
    iapply twp_load32 (UInt32.ofNat k) hk0 hk1 hk2 hk3 $$ Hk
    iintro Hk
    iapply twp_localSet rfl
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_ltU (result := 1) (by simp [hkU])
    iapply twp_const
    iapply twp_and
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    rw [show
      [.localGet 4, .localGet 16, .const 3, .shl, .add, .localGet 15,
        .store64 0,
        .localGet 6, .localGet 6, .load32 4, .const 1, .add, .store32 4,
        .localGet 6, .localGet 6, .load32 12, .const 1, .add, .store32 12,
        .br 1] = mergeTakeLeftUpdate by rfl]
    rw [← List.append_nil mergeTakeLeftUpdate]
    rw [show
      [.i32 leftPtr, .i32 (UInt32.ofNat left.length), .i32 rightPtr,
        .i32 (UInt32.ofNat right.length), .i32 scratchPtr,
        .i32 (UInt32.ofNat scratch.length)] =
          mergeParams leftPtr (UInt32.ofNat left.length) rightPtr
            (UInt32.ofNat right.length) scratchPtr
            (UInt32.ofNat scratch.length) by rfl]
    rw [show
      [.i32 frame, .i32 (UInt32.ofNat i),
        .i32 (leftPtr + 8 * UInt32.ofNat i), .i32 (UInt32.ofNat j),
        .i32 (rightPtr + 8 * UInt32.ofNat j), .i32 a11,
        .i32 (UInt32.ofNat i), .i64 v13, .i32 a14, .i64 x,
        .i32 (UInt32.ofNat k), .i32 a17, .i64 v18, .i32 a19,
        .i32 a20, .i64 v21, .i32 a22] =
          mergeSelectionLocals frame (UInt32.ofNat i)
            (leftPtr + 8 * UInt32.ofNat i) (UInt32.ofNat j)
            (rightPtr + 8 * UInt32.ofNat j) a11 (UInt32.ofNat i)
            v13 a14 x (UInt32.ofNat k) a17 v18 a19 a20 v21 a22 by rfl]
    iapply merge_takeLeft_update_twp
      (leftPtr := leftPtr) (rightPtr := rightPtr) (scratchPtr := scratchPtr)
      (frame := frame) (left := left) (right := right) (scratch := scratch)
      (i := i) (j := j) (k := k) (emitted := emitted) (x := x) (y := y)
      (localValues := mergeSelectionLocals frame (UInt32.ofNat i)
        (leftPtr + 8 * UInt32.ofNat i) (UInt32.ofNat j)
        (rightPtr + 8 * UInt32.ofNat j) a11 (UInt32.ofNat i)
        v13 a14 x (UInt32.ofNat k) a17 v18 a19 a20 v21 a22)
      (hinv := hinv) (hi := hi) (hj := hj) (hx := hx) (hy := hy)
      (hxy := hxy) (hscratchFit := hscratchFit)
      (hframeRoom := hframeRoom) (hframe := by rfl) (hscratch := by rfl)
      (hkLocal := by rfl) (hxLocal := by rfl)
      (htarget := by rfl)
    isplitl [Hscratch]
    · iexact Hscratch
    isplitl [Hi]
    · iexact Hi
    isplitl [Hk]
    · iexact Hk
    iintro ⟨%hnext, Hscratch, Hi, Hk⟩
    simp only [mergeLoopFrame, List.take_zero,
      mergeMainLoopBody, mergeAfterInit, func125, List.drop,
      mergeLoadedCompare, mergeTakeLeftUpdate, List.append_nil]
    ihave Hthen := BI.and_elim_l $$ Hbranches
    iapply Hthen
    isplitr
    · ipureintro
      exact hxy
    isplitr
    · ipureintro
      exact hnext
    isplitl [Hleft]
    · iexact Hleft
    isplitl [Hright]
    · iexact Hright
    isplitl [Hscratch]
    · iexact Hscratch
    isplitl [Hi]
    · iexact Hi
    isplitl [Hj]
    · iexact Hj
    · iexact Hk
  · iintro ⟨%hxy, HleftWord, HrightWord⟩
    ihave HleftOriginal :
        pointsTo_u64 (leftPtr + 8 * UInt32.ofNat i) left[i] $$ [HleftWord]
    · dsimp only [leftAddress]
      rw [UInt32.add_zero, hxElem]
      iexact HleftWord
    ihave Hleft := HleftClose $$ HleftOriginal
    ihave HrightOriginal :
        pointsTo_u64 (rightPtr + 8 * UInt32.ofNat j) right[j] $$ [HrightWord]
    · dsimp only [rightAddress]
      rw [UInt32.add_zero, hyElem]
      iexact HrightWord
    ihave Hright := HrightClose $$ HrightOriginal
    simp only [List.take_zero, List.nil_append]
    iapply twp_localGet rfl
    iapply twp_load32 (UInt32.ofNat j) hj0 hj1 hj2 hj3 $$ Hj
    iintro Hj
    iapply twp_localSet rfl
    simp only [List.set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_ltU (result := 1) (by simp [hjU])
    iapply twp_const
    iapply twp_and
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    iapply twp_load64AtShift_raw hj hrightFit rfl rfl
    isplitl [Hright]
    · iexact Hright
    iintro Hright
    rw [hyElem]
    iapply twp_localSet rfl
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_localGet rfl
    iapply twp_load32 (UInt32.ofNat k) hk0 hk1 hk2 hk3 $$ Hk
    iintro Hk
    iapply twp_localSet rfl
    simp only [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_ltU (result := 1) (by simp [hkU])
    iapply twp_const
    iapply twp_and
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    rw [show
      [.localGet 4, .localGet 14, .const 3, .shl, .add, .localGet 13,
        .store64 0,
        .localGet 6, .localGet 6, .load32 8, .const 1, .add, .store32 8,
        .localGet 6, .localGet 6, .load32 12, .const 1, .add, .store32 12,
        .br 5] = mergeTakeRightUpdate by rfl]
    rw [← List.append_nil mergeTakeRightUpdate]
    rw [show
      [.i32 leftPtr, .i32 (UInt32.ofNat left.length), .i32 rightPtr,
        .i32 (UInt32.ofNat right.length), .i32 scratchPtr,
        .i32 (UInt32.ofNat scratch.length)] =
          mergeParams leftPtr (UInt32.ofNat left.length) rightPtr
            (UInt32.ofNat right.length) scratchPtr
            (UInt32.ofNat scratch.length) by rfl]
    rw [show
      [.i32 frame, .i32 (UInt32.ofNat i),
        .i32 (leftPtr + 8 * UInt32.ofNat i), .i32 (UInt32.ofNat j),
        .i32 (rightPtr + 8 * UInt32.ofNat j), .i32 (UInt32.ofNat j),
        .i32 a12, .i64 y, .i32 (UInt32.ofNat k), .i64 v15,
        .i32 a16, .i32 a17, .i64 v18, .i32 a19,
        .i32 a20, .i64 v21, .i32 a22] =
          mergeSelectionLocals frame (UInt32.ofNat i)
            (leftPtr + 8 * UInt32.ofNat i) (UInt32.ofNat j)
            (rightPtr + 8 * UInt32.ofNat j) (UInt32.ofNat j) a12
            y (UInt32.ofNat k) v15 a16 a17 v18 a19 a20 v21 a22 by rfl]
    iapply merge_takeRight_update_twp
      (leftPtr := leftPtr) (rightPtr := rightPtr) (scratchPtr := scratchPtr)
      (frame := frame) (left := left) (right := right) (scratch := scratch)
      (i := i) (j := j) (k := k) (emitted := emitted) (x := x) (y := y)
      (localValues := mergeSelectionLocals frame (UInt32.ofNat i)
        (leftPtr + 8 * UInt32.ofNat i) (UInt32.ofNat j)
        (rightPtr + 8 * UInt32.ofNat j) (UInt32.ofNat j) a12
        y (UInt32.ofNat k) v15 a16 a17 v18 a19 a20 v21 a22)
      (hinv := hinv) (hi := hi) (hj := hj) (hx := hx) (hy := hy)
      (hxy := hxy) (hscratchFit := hscratchFit)
      (hframeRoom := hframeRoom) (hframe := by rfl) (hscratch := by rfl)
      (hkLocal := by rfl) (hyLocal := by rfl)
      (htarget := by rfl)
    isplitl [Hscratch]
    · iexact Hscratch
    isplitl [Hj]
    · iexact Hj
    isplitl [Hk]
    · iexact Hk
    iintro ⟨%hnext, Hscratch, Hj, Hk⟩
    simp only [mergeLoopFrame, List.take_zero,
      mergeMainLoopBody, mergeAfterInit, func125, List.drop,
      mergeLoadedCompare, mergeTakeRightUpdate, List.append_nil]
    ihave Helse := BI.and_elim_r $$ Hbranches
    iapply Helse
    isplitr
    · ipureintro
      exact hxy
    isplitr
    · ipureintro
      exact hnext
    isplitl [Hleft]
    · iexact Hleft
    isplitl [Hright]
    · iexact Hright
    isplitl [Hscratch]
    · iexact Hscratch
    isplitl [Hi]
    · iexact Hi
    isplitl [Hj]
    · iexact Hj
    · iexact Hk

/- Total well-founded composition of the generated main merge loop.  Each
backedge consumes one element, so the sum of the two remaining slice lengths
strictly decreases. -/
set_option maxHeartbeats 12000000 in
theorem merge_main_loop_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr rightPtr scratchPtr frame : UInt32)
    (left right : List UInt64) (initial : MergeMainRuntimeState)
    (hinitial : MergeSlicesInvariant left right initial.scratch
      initial.i initial.j initial.k initial.emitted)
    (hleftFit : leftPtr.toNat + 8 * left.length ≤ UInt32.size)
    (hrightFit : rightPtr.toNat + 8 * right.length ≤ UInt32.size)
    (hscratchFit : scratchPtr.toNat +
      8 * (left.length + right.length) ≤ UInt32.size)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value} {afterLoop : Program}
    {outerControls : List ControlFrame} {calls : List CallFrame} :
    array64At leftPtr left ∗ array64At rightPtr right ∗
      array64At scratchPtr initial.scratch ∗
      pointsTo_u32 (frame + 4) (UInt32.ofNat initial.i) ∗
      pointsTo_u32 (frame + 8) (UInt32.ofNat initial.j) ∗
      pointsTo_u32 (frame + 12) (UInt32.ofNat initial.k) ∗
      (∀ (final : MergeMainRuntimeState),
        ⌜MergeSlicesInvariant left right final.scratch
          final.i final.j final.k final.emitted⌝ -∗
        ⌜final.i = left.length ∨ final.j = right.length⌝ -∗
        array64At leftPtr left -∗ array64At rightPtr right -∗
        array64At scratchPtr final.scratch -∗
        pointsTo_u32 (frame + 4) (UInt32.ofNat final.i) -∗
        pointsTo_u32 (frame + 8) (UInt32.ofNat final.j) -∗
        pointsTo_u32 (frame + 12) (UInt32.ofNat final.k) -∗
        WP (.running
          ⟨mergeMainRuntimeLocals leftPtr rightPtr scratchPtr frame
              left right final,
            afterLoop, arity, remainder, outerControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨mergeMainRuntimeLocals leftPtr rightPtr scratchPtr frame
          left right initial,
        .block 0 0 [.loop 0 0 mergeMainLoopBody] :: afterLoop,
        arity, remainder, outerControls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let Finish : IProp WasmHeapGF := iprop%
    ∀ (final : MergeMainRuntimeState),
      ⌜MergeSlicesInvariant left right final.scratch
        final.i final.j final.k final.emitted⌝ -∗
      ⌜final.i = left.length ∨ final.j = right.length⌝ -∗
      array64At leftPtr left -∗ array64At rightPtr right -∗
      array64At scratchPtr final.scratch -∗
      pointsTo_u32 (frame + 4) (UInt32.ofNat final.i) -∗
      pointsTo_u32 (frame + 8) (UInt32.ofNat final.j) -∗
      pointsTo_u32 (frame + 12) (UInt32.ofNat final.k) -∗
      WP (.running
        ⟨mergeMainRuntimeLocals leftPtr rightPtr scratchPtr frame
            left right final,
          afterLoop, arity, remainder, outerControls, calls⟩ : Expr α)
        @ s; E [{ Φ }]
  let Inv : MergeMainRuntimeState → IProp WasmHeapGF := fun state => iprop%
    ⌜MergeSlicesInvariant left right state.scratch
      state.i state.j state.k state.emitted⌝ ∗
    array64At leftPtr left ∗ array64At rightPtr right ∗
    array64At scratchPtr state.scratch ∗
    pointsTo_u32 (frame + 4) (UInt32.ofNat state.i) ∗
    pointsTo_u32 (frame + 8) (UInt32.ofNat state.j) ∗
    pointsTo_u32 (frame + 12) (UInt32.ofNat state.k) ∗ Finish
  let mainBlockFrame : ControlFrame :=
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := [.loop 0 0 mergeMainLoopBody]
      continuation := afterLoop
      belowStack := [] }
  iintro ⟨Hleft, Hright, Hscratch, Hi, Hj, Hk, Hfinish⟩
  iapply twp_block
  iapply twp_loop_wf_family_from (α := α)
    (ι := MergeMainRuntimeState)
    (measure := fun state =>
      (left.length - state.i) + (right.length - state.j))
    (locals := mergeMainRuntimeLocals leftPtr rightPtr scratchPtr frame
      left right)
    (I := Inv) (initial := initial)
    (initialLocals := mergeMainRuntimeLocals leftPtr rightPtr scratchPtr frame
      left right initial)
    (body := mergeMainLoopBody) (code := []) (belowStack := [])
    rfl rfl
  · intro state
    simp only [Inv, loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨%hstate, Hleft, Hright, Hscratch, Hi, Hj, Hk, Hfinish⟩
    have hdata := hstate
    unfold MergeSlicesInvariant at hdata
    have hleftLength : left.length < UInt32.size := by
      simp only [UInt32.size] at hleftFit ⊢
      omega
    have hrightLength : right.length < UInt32.size := by
      simp only [UInt32.size] at hrightFit ⊢
      omega
    have hiSize : state.i < UInt32.size := by omega
    have hjSize : state.j < UInt32.size := by omega
    have hkSize : state.k < UInt32.size := by
      simp only [UInt32.size] at hscratchFit ⊢
      omega
    have hiCmp :
        (UInt32.ofNat state.i < UInt32.ofNat left.length) ↔
          state.i < left.length := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hiSize,
        UInt32.toNat_ofNat_of_lt' hleftLength]
    have hjCmp :
        (UInt32.ofNat state.j < UInt32.ofNat right.length) ↔
          state.j < right.length := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hjSize,
        UInt32.toNat_ofNat_of_lt' hrightLength]
    have hstateScratchFit :
        scratchPtr.toNat + 8 * state.scratch.length ≤ UInt32.size := by
      rw [hdata.2.2.1]
      exact hscratchFit
    obtain ⟨hi0, hi1, hi2, hi3⟩ :=
      slotFacts frame 4 hframeRoom (by decide)
    obtain ⟨hj0, hj1, hj2, hj3⟩ :=
      slotFacts frame 8 hframeRoom (by decide)
    by_cases hi : state.i < left.length
    · by_cases hj : state.j < right.length
      · let x := left[state.i]
        let y := right[state.j]
        have hx : left[state.i]? = some x := by
          dsimp only [x]
          exact List.getElem?_eq_getElem hi
        have hy : right[state.j]? = some y := by
          dsimp only [y]
          exact List.getElem?_eq_getElem hj
        have hiSucc : state.i + 1 < UInt32.size := by omega
        have hjSucc : state.j + 1 < UInt32.size := by omega
        have hkSucc : state.k + 1 < UInt32.size := by
          simp only [UInt32.size] at hscratchFit ⊢
          omega
        have hiValue :
            UInt32.ofNat state.i + 1 = UInt32.ofNat (state.i + 1) := by
          rw [u32_ofNat_succ hiSucc]
        have hjValue :
            UInt32.ofNat state.j + 1 = UInt32.ofNat (state.j + 1) := by
          rw [u32_ofNat_succ hjSucc]
        have hkValue :
            UInt32.ofNat state.k + 1 = UInt32.ofNat (state.k + 1) := by
          rw [u32_ofNat_succ hkSucc]
        simp only [mergeMainRuntimeLocals]
        iapply merge_main_guards_twp leftPtr (UInt32.ofNat left.length)
          rightPtr (UInt32.ofNat right.length) scratchPtr
          (UInt32.ofNat (left.length + right.length)) frame
          (UInt32.ofNat state.i) (UInt32.ofNat state.j)
          (mergeSelectionLocals frame state.l7 state.l8 state.l9 state.l10
            state.l11 state.l12 state.l13 state.l14 state.l15 state.l16
            state.l17 state.l18 state.l19 state.l20 state.l21 state.l22)
          (⟨mergeParams leftPtr (UInt32.ofNat left.length) rightPtr
              (UInt32.ofNat right.length) scratchPtr
              (UInt32.ofNat (left.length + right.length)),
            mergeSelectionLocals frame (UInt32.ofNat state.i) state.l8
              state.l9 state.l10 state.l11 state.l12 state.l13 state.l14
              state.l15 state.l16 state.l17 state.l18 state.l19 state.l20
              state.l21 state.l22,
            [.i32 (UInt32.ofNat state.i)]⟩ : Locals)
          (by simpa [hiCmp]) (by simpa [hjCmp]) hframeRoom rfl rfl
        isplitl [Hi]
        · iexact Hi
        isplitl [Hj]
        · iexact Hj
        iintro ⟨Hi, Hj⟩
        simp only [List.drop_zero]
        rw [← hdata.2.2.1]
        have Hiter := merge_main_iteration_twp
          (α := α) (s := s) (E := E) (Φ := Φ)
          leftPtr rightPtr scratchPtr frame
          left right state.scratch state.i state.j state.k state.emitted x y
          state.l8 state.l9 state.l10 state.l11 state.l12 state.l14
          state.l16 state.l17 state.l19 state.l20 state.l22
          state.l13 state.l15 state.l18 state.l21
          hstate hi hj hx hy hleftFit hrightFit hstateScratchFit hframeRoom
          (arity := arity) (remainder := remainder) (afterLoop := [])
          (outerControls := mainBlockFrame :: outerControls) (calls := calls)
        simp only [mergeLoopFrame, mainBlockFrame] at Hiter
        iapply Hiter
        isplitl [Hleft]
        · iexact Hleft
        isplitl [Hright]
        · iexact Hright
        isplitl [Hscratch]
        · iexact Hscratch
        isplitl [Hi]
        · iexact Hi
        isplitl [Hj]
        · iexact Hj
        isplitl [Hk]
        · iexact Hk
        isplit
        · iintro ⟨%_hxy, %hnext, Hleft, Hright, Hscratch, Hi, Hj, Hk⟩
          ispecialize Hrec $$
            %(MergeMainRuntimeState.takeLeft leftPtr rightPtr x state)
          isimp only [MergeMainRuntimeState.takeLeft,
            mergeMainRuntimeLocals] at Hrec
          iapply Hrec
          · ipureintro
            omega
          isplitr
          · ipureintro
            exact hnext
          isplitl [Hleft]
          · iexact Hleft
          isplitl [Hright]
          · iexact Hright
          isplitl [Hscratch]
          · iexact Hscratch
          isplitl [Hi]
          · rw [← hiValue]
            iexact Hi
          isplitl [Hj]
          · iexact Hj
          isplitl [Hk]
          · rw [← hkValue]
            iexact Hk
          · iexact Hfinish
        · iintro ⟨%_hxy, %hnext, Hleft, Hright, Hscratch, Hi, Hj, Hk⟩
          ispecialize Hrec $$
            %(MergeMainRuntimeState.takeRight leftPtr rightPtr y state)
          isimp only [MergeMainRuntimeState.takeRight,
            mergeMainRuntimeLocals] at Hrec
          iapply Hrec
          · ipureintro
            omega
          isplitr
          · ipureintro
            exact hnext
          isplitl [Hleft]
          · iexact Hleft
          isplitl [Hright]
          · iexact Hright
          isplitl [Hscratch]
          · iexact Hscratch
          isplitl [Hi]
          · iexact Hi
          isplitl [Hj]
          · rw [← hjValue]
            iexact Hj
          isplitl [Hk]
          · rw [← hkValue]
            iexact Hk
          · iexact Hfinish
      · have hjEq : state.j = right.length := by omega
        simp only [mergeMainRuntimeLocals, mergeMainLoopBody,
          mergeAfterInit, func125, List.drop]
        iapply twp_localGet rfl
        iapply twp_load32 (UInt32.ofNat state.i) hi0 hi1 hi2 hi3 $$ Hi
        iintro Hi
        iapply twp_localGet rfl
        iapply twp_ltU (result := 1) (by simp [hiCmp, hi])
        iapply twp_const
        iapply twp_and
        rw [show (1 : UInt32) &&& 1 = 1 by decide]
        iapply twp_eqz (result := 0) (by decide)
        iapply twp_brIfZero
        iapply twp_localGet rfl
        iapply twp_load32 (UInt32.ofNat state.j) hj0 hj1 hj2 hj3 $$ Hj
        iintro Hj
        iapply twp_localGet rfl
        iapply twp_ltU (result := 0) (by simp [hjCmp, hj])
        iapply twp_const
        iapply twp_and
        rw [show (0 : UInt32) &&& 1 = 0 by decide]
        iapply twp_eqz (result := 1) (by decide)
        iapply twp_brIf (by decide) (by rfl)
        simp only [List.take_zero, List.nil_append]
        isimp only [Finish] at Hfinish
        ihave Hdone := Hfinish $$ %state %hstate %(Or.inr hjEq)
          Hleft Hright Hscratch Hi Hj Hk
        isimp only [mergeMainRuntimeLocals] at Hdone
        iexact Hdone
    · have hiEq : state.i = left.length := by omega
      simp only [mergeMainRuntimeLocals, mergeMainLoopBody,
        mergeAfterInit, func125, List.drop]
      iapply twp_localGet rfl
      iapply twp_load32 (UInt32.ofNat state.i) hi0 hi1 hi2 hi3 $$ Hi
      iintro Hi
      iapply twp_localGet rfl
      iapply twp_ltU (result := 0) (by simp [hiCmp, hi])
      iapply twp_const
      iapply twp_and
      rw [show (0 : UInt32) &&& 1 = 0 by decide]
      iapply twp_eqz (result := 1) (by decide)
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.nil_append]
      isimp only [Finish] at Hfinish
      ihave Hdone := Hfinish $$ %state %hstate %(Or.inl hiEq)
        Hleft Hright Hscratch Hi Hj Hk
      isimp only [mergeMainRuntimeLocals] at Hdone
      iexact Hdone
  · simp only [Inv, Finish]
    isplitr
    · ipureintro
      exact hinitial
    iframe

/- Exact generated step for copying one remaining left element after the main
loop has established that the right slice is exhausted. -/
set_option maxHeartbeats 4000000 in
theorem merge_left_remainder_step_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr rightPtr scratchPtr frame : UInt32)
    (left right : List UInt64) (state : MergeMainRuntimeState)
    (x : UInt64)
    (hinv : MergeSlicesInvariant left right state.scratch
      state.i right.length state.k state.emitted)
    (hi : state.i < left.length) (hx : left[state.i]? = some x)
    (hleftFit : leftPtr.toNat + 8 * left.length ≤ UInt32.size)
    (hscratchFit : scratchPtr.toNat +
      8 * state.scratch.length ≤ UInt32.size)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value} {code : Program}
    {controls targetControls : List ControlFrame}
    {targetCode : Program} {targetValues : List Value}
    {calls : List CallFrame}
    (htarget : branchTarget? arity 0 controls [] =
      some (targetCode, targetControls, targetValues)) :
    array64At leftPtr left ∗ array64At scratchPtr state.scratch ∗
      pointsTo_u32 (frame + 4) (UInt32.ofNat state.i) ∗
      pointsTo_u32 (frame + 12) (UInt32.ofNat state.k) ∗
      ((⌜MergeSlicesInvariant left right
          (state.scratch.set state.k x) (state.i + 1) right.length
          (state.k + 1) (state.emitted ++ [x])⌝ ∗
        array64At leftPtr left ∗
        array64At scratchPtr (state.scratch.set state.k x) ∗
        pointsTo_u32 (frame + 4) (UInt32.ofNat state.i + 1) ∗
        pointsTo_u32 (frame + 12) (UInt32.ofNat state.k + 1)) -∗
        WP (.running
          ⟨{ mergeMainRuntimeLocals leftPtr rightPtr scratchPtr frame
                left right (state.takeRemainingLeft x) with
              values := targetValues },
            targetCode, arity, remainder, targetControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨mergeMainRuntimeLocals leftPtr rightPtr scratchPtr frame left right state,
        mergeLeftRemainderStep ++ code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  have hk : state.k < state.scratch.length := hinv.k_lt hi
  have hnext := hinv.takeRemainingLeft hi hx
  let updateFrame : ControlFrame :=
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := mergeLeftUpdateBody
      continuation := code
      belowStack := [] }
  have hscratchEq :
      state.scratch.length = left.length + right.length := by
    unfold MergeSlicesInvariant at hinv
    exact hinv.2.2.1
  have hleftLength : left.length < UInt32.size := by
    simp only [UInt32.size] at hleftFit ⊢
    omega
  have hiSize : state.i < UInt32.size := by omega
  have hiU : UInt32.ofNat state.i < UInt32.ofNat left.length := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' hiSize,
      UInt32.toNat_ofNat_of_lt' hleftLength]
    exact hi
  have hscratchLength : state.scratch.length < UInt32.size := by
    simp only [UInt32.size] at hscratchFit ⊢
    omega
  have hkSize : state.k < UInt32.size := by omega
  have hkU : UInt32.ofNat state.k <
      UInt32.ofNat state.scratch.length := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' hkSize,
      UInt32.toNat_ofNat_of_lt' hscratchLength]
    exact hk
  obtain ⟨hi0, hi1, hi2, hi3⟩ :=
    slotFacts frame 4 hframeRoom (by decide)
  obtain ⟨hk0, hk1, hk2, hk3⟩ :=
    slotFacts frame 12 hframeRoom (by decide)
  iintro ⟨Hleft, Hscratch, Hi, Hk, Hcont⟩
  simp only [mergeLeftRemainderStep, mergeLeftLoopBody, mergeAfterMain,
    mergeAfterInit, func125, List.drop, List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat state.i) hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_localSet rfl
  simp only [mergeMainRuntimeLocals, mergeSelectionLocals, mergeParams,
    List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1) (by simp [hiU])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_load64AtShift_raw hi hleftFit rfl rfl
  isplitl [Hleft]
  · iexact Hleft
  iintro Hleft
  have hxElem : left[state.i] = x := by
    have hxOption := hx
    rw [List.getElem?_eq_getElem hi] at hxOption
    exact Option.some.inj hxOption
  rw [hxElem]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat state.k) hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1) (by simpa [hscratchEq] using hkU)
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_store64AtShift_raw hk hscratchFit rfl rfl rfl
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hscratch
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat state.i) hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 1]
  iapply twp_store32 (UInt32.ofNat state.i) hi0 hi1 hi2 hi3 $$ Hi
  iintro Hi
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat state.k) hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 1]
  iapply twp_store32 (UInt32.ofNat state.k) hk0 hk1 hk2 hk3 $$ Hk
  iintro Hk
  simp only [List.drop_zero]
  have Hbr := twp_br
    (α := α) (s := s) (E := E) (Φ := Φ)
    (params := mergeParams leftPtr (UInt32.ofNat left.length) rightPtr
      (UInt32.ofNat right.length) scratchPtr
      (UInt32.ofNat (left.length + right.length)))
    (localValues := mergeSelectionLocals frame state.l7 state.l8 state.l9
      state.l10 state.l11 state.l12 state.l13 state.l14 state.l15 state.l16
      state.l17 state.l18 state.l19 (UInt32.ofNat state.i) x
      (UInt32.ofNat state.k))
    (values := []) (targetValues := targetValues) (depth := 1)
    (arity := arity) (code := []) (targetCode := targetCode)
    (remainder := remainder) (controls := updateFrame :: controls)
    (targetControl := targetControls) (calls := calls)
    (by simpa only [branchTarget?] using htarget)
  simp only [updateFrame, mergeLeftUpdateBody, mergeLeftRemainderStep, mergeLeftLoopBody,
    mergeAfterMain, mergeAfterInit, func125, mergeParams,
    mergeSelectionLocals, List.drop] at Hbr
  iapply Hbr
  isimp only [mergeMainRuntimeLocals,
    MergeMainRuntimeState.takeRemainingLeft] at Hcont
  iapply Hcont
  isplitr
  · ipureintro
    exact hnext
  isplitl [Hleft]
  · iexact Hleft
  isplitl [Hscratch]
  · iexact Hscratch
  isplitl [Hi]
  · iexact Hi
  · iexact Hk

end Project.Mergesort.MergeFunctionProof
