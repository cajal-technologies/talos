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

end Project.Mergesort.MergeFunctionProof
