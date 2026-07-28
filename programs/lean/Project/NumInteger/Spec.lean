import Project.NumInteger.Program

/-!
# Specification for `gcd_u64`

The exported `gcd_u64` function implements the binary GCD (Stein's
algorithm) on `u64` operands. By the `num-integer` convention the function
returns `0` on `(0, 0)`.

Unlike the previous optimized build, the unoptimized (`opt-level = 0`)
module keeps the operands in linear memory: the exported wrapper (`func2`)
calls `func0`, which spills the two arguments to a 16-byte stack frame and
hands pointers to `func1`, the actual binary-GCD loop. `func1` copies the
operands into its own 48-byte scratch frame and runs Stein's algorithm
entirely through `i64.load`/`i64.store`. The proof therefore threads the
running values through the memory model with the read-after-write framing
lemmas from `CodeLib.RustStd.Frame`, reusing the `UInt64` Stein lemmas
from `CodeLib` for the arithmetic core.
-/

namespace Project.NumInteger.Spec

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic

set_option maxRecDepth 1048576

/-! ## Physical stack-frame ownership

The outer wrapper's 16-byte frame and `func1`'s 48-byte frame are adjacent.
Keeping them in one finite heap lets the Iris proof frame every scratch slot
across calls while exposing typed ownership only for the slot currently used. -/

def gcdFrameHeap
    (result x y : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (outerA outerB : UInt64) : WasmHeapMap (Option UInt8) :=
  store64Heap
    (store64Heap
      (store32Heap
        (store32Heap
          (store32Heap
            (store32Heap
              (store32Heap
                (store64Heap
                  (store64Heap
                    (store64Heap ∅ 1048512 result)
                    1048520 x)
                  1048528 y)
                1048540 nextX)
              1048544 nextY)
            1048548 shiftY)
          1048552 shiftX)
        1048556 shiftXY)
      1048560 outerA)
    1048568 outerB

def gcdFrameMem
    (mem : Mem)
    (result x y : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (outerA outerB : UInt64) : Mem :=
  (((((((((mem.write64 1048512 result).write64 1048520 x).write64 1048528 y)
      |>.write32 1048540 nextX).write32 1048544 nextY).write32 1048548 shiftY)
      |>.write32 1048552 shiftX).write32 1048556 shiftXY).write64 1048560 outerA)
      |>.write64 1048568 outerB

theorem gcdFrameHeap_agrees
    (mem : Mem)
    (result x y : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (outerA outerB : UInt64) :
    heapAgreesWithMem
      (gcdFrameHeap result x y shiftXY shiftX shiftY nextY nextX outerA outerB)
      (gcdFrameMem mem result x y shiftXY shiftX shiftY nextY nextX outerA outerB) := by
  unfold gcdFrameHeap gcdFrameMem
  apply store64_sound <;> try rfl
  apply store64_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store64_sound <;> try rfl
  apply store64_sound <;> try rfl
  apply store64_sound <;> try rfl
  intro address byte hget
  rw [get?_empty] at hget
  contradiction

theorem gcdFrameHeap_inBounds
    (mem : Mem) (hpages : 16 ≤ mem.pages)
    (result x y : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (outerA outerB : UInt64) :
    heapAddressesInBounds
      (gcdFrameHeap result x y shiftXY shiftX shiftY nextY nextX outerA outerB)
      (gcdFrameMem mem result x y shiftXY shiftX shiftY nextY nextX outerA outerB) := by
  unfold gcdFrameHeap gcdFrameMem
  apply store64_inBounds <;> try rfl
  apply store64_inBounds <;> try rfl
  apply store32_inBounds <;> try rfl
  apply store32_inBounds <;> try rfl
  apply store32_inBounds <;> try rfl
  apply store32_inBounds <;> try rfl
  apply store32_inBounds <;> try rfl
  apply store64_inBounds <;> try rfl
  apply store64_inBounds <;> try rfl
  apply store64_inBounds <;> try rfl
  · intro address byte hget
    rw [get?_empty] at hget
    contradiction
  all_goals
    simp only [Mem.write64_pages, Mem.write32_pages, UInt32.reduceToNat]
    have hcapacity : 1048576 ≤ mem.pages * 65536 := by
      calc
        1048576 = 16 * 65536 := by norm_num
        _ ≤ mem.pages * 65536 := Nat.mul_le_mul_right 65536 hpages
    omega

set_option linter.unusedSimpArgs false in
theorem gcdFrameHeap_pointsTo
    [WasmHeapGS]
    (result x y : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (outerA outerB : UInt64) :
    ([∗map] address ↦ byte ∈
        gcdFrameHeap result x y shiftXY shiftX shiftY nextY nextX outerA outerB,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) byte) ⊢
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 x ∗
      pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048556 shiftXY ∗
      pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗
      pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 outerA ∗
      pointsTo_u64 1048568 outerB := by
  unfold gcdFrameHeap
  iintro Hframe
  ihave HsplitB := store64Heap_pointsTo _ 1048568 outerB
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) $$ Hframe
  icases HsplitB with ⟨HouterB, Hframe⟩
  ihave HsplitA := store64Heap_pointsTo _ 1048560 outerA
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) $$ Hframe
  icases HsplitA with ⟨HouterA, Hframe⟩
  ihave HsplitShiftXY := store32Heap_pointsTo _ 1048556 shiftXY
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by decide) (by decide) (by decide) $$ Hframe
  icases HsplitShiftXY with ⟨HshiftXY, Hframe⟩
  ihave HsplitShiftX := store32Heap_pointsTo _ 1048552 shiftX
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by decide) (by decide) (by decide) $$ Hframe
  icases HsplitShiftX with ⟨HshiftX, Hframe⟩
  ihave HsplitShiftY := store32Heap_pointsTo _ 1048548 shiftY
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by decide) (by decide) (by decide) $$ Hframe
  icases HsplitShiftY with ⟨HshiftY, Hframe⟩
  ihave HsplitNextY := store32Heap_pointsTo _ 1048544 nextY
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by decide) (by decide) (by decide) $$ Hframe
  icases HsplitNextY with ⟨HnextY, Hframe⟩
  ihave HsplitNextX := store32Heap_pointsTo _ 1048540 nextX
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by decide) (by decide) (by decide) $$ Hframe
  icases HsplitNextX with ⟨HnextX, Hframe⟩
  ihave HsplitY := store64Heap_pointsTo _ 1048528 y
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) $$ Hframe
  icases HsplitY with ⟨Hy, Hframe⟩
  ihave HsplitX := store64Heap_pointsTo _ 1048520 x
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) $$ Hframe
  icases HsplitX with ⟨Hx, Hframe⟩
  ihave HsplitResult := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 1048512 result
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty])
    (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) (by simp [store64Heap, store32Heap, get?_insert_ne, get?_empty]) $$ Hframe
  icases HsplitResult with ⟨Hresult, _Hempty⟩
  iframe

def func1InitialLocals : List Value :=
  [.i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0, .i32 0]

def func1SpilledLocals : List Value :=
  [.i32 1048512, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0, .i32 0]

/-- The memory-backed GCD prologue moves its pointer arguments into the
callee's own frame. This is the first reusable Iris slice of opt0 `func1`:
the caller words remain owned, while the two scratch words are updated to the
loaded operands and all unrelated resources are framed by `R`. -/
theorem func1_spillPrefix_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b oldX oldY : UInt64)
    (hcontinue :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
        pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
          func1.drop 12, 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB, Hx, Hy⟩
  simp only [func1, func1InitialLocals]
  iapply Wasm.SmallStep.wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_sub
  inext
  rw [show (1048560 : UInt32) - 48 = 1048512 by decide]
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HouterALater : ▷ pointsTo_u64 (1048560 + 0) a $$ [HouterA]
  · inext
    rw [show (1048560 : UInt32) + 0 = 1048560 by decide]
    iexact HouterA
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HouterALater
  inext
  iintro HouterA
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) oldX $$ [Hx]
  · inext
    rw [show (1048512 : UInt32) + 8 = 1048520 by decide]
    iexact Hx
  iapply Wasm.SmallStep.wp_store64 oldX
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HouterBLater : ▷ pointsTo_u64 (1048568 + 0) b $$ [HouterB]
  · inext
    rw [show (1048568 : UInt32) + 0 = 1048568 by decide]
    iexact HouterB
  iapply Wasm.SmallStep.wp_load64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HouterBLater
  inext
  iintro HouterB
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) oldY $$ [Hy]
  · inext
    rw [show (1048512 : UInt32) + 16 = 1048528 by decide]
    iexact Hy
  iapply Wasm.SmallStep.wp_store64 oldY
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  simp only [func1SpilledLocals, func1, List.drop] at hcontinue
  have hOuterAProp :
      pointsTo_u64 ((1048560 : UInt32) + 0) a = pointsTo_u64 1048560 a :=
    congrArg (fun address => pointsTo_u64 address a) (by decide)
  have hOuterBProp :
      pointsTo_u64 ((1048568 : UInt32) + 0) b = pointsTo_u64 1048568 b :=
    congrArg (fun address => pointsTo_u64 address b) (by decide)
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8) a = pointsTo_u64 1048520 a :=
    congrArg (fun address => pointsTo_u64 address a) (by decide)
  have hYProp :
      pointsTo_u64 ((1048512 : UInt32) + 16) b = pointsTo_u64 1048528 b :=
    congrArg (fun address => pointsTo_u64 address b) (by decide)
  ihave HouterAExact : pointsTo_u64 1048560 a $$ [HouterA]
  · rw [← hOuterAProp]
    iexact HouterA
  ihave HouterBExact : pointsTo_u64 1048568 b $$ [HouterB]
  · rw [← hOuterBProp]
    iexact HouterB
  ihave HxExact : pointsTo_u64 1048520 a $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 b $$ [Hy]
  · rw [← hYProp]
    iexact Hy
  iapply hcontinue
  iframe

/-- Frame-level form of `func1_spillPrefix_smallStep_wp`. It connects the
finite authoritative heap used by adequacy to the typed resources used by
instruction rules, without exposing individual byte ownership to clients. -/
theorem func1_spillPrefix_frame_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (calls : List Wasm.SmallStep.CallFrame)
    (result oldX oldY : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (a b : UInt64)
    (hcontinue :
      pointsTo_u64 1048512 result ∗
        pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
        pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
        pointsTo_u32 1048540 nextX ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
        pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
          func1.drop 12, 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    globalPointsTo 0 (.i32 1048560) ∗
      ([∗map] address ↦ byte ∈
        gcdFrameHeap result oldX oldY shiftXY shiftX shiftY nextY nextX a b,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) byte) ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hglobal, Hframe⟩
  ihave Hslots := gcdFrameHeap_pointsTo
    result oldX oldY shiftXY shiftX shiftY nextY nextX a b $$ Hframe
  icases Hslots with
    ⟨Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY, HnextY, HnextX,
      HouterA, HouterB⟩
  iapply func1_spillPrefix_smallStep_wp
    (R := iprop(pointsTo_u64 1048512 result ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX))
    (calls := calls) (a := a) (b := b) (oldX := oldX) (oldY := oldY)
  · iintro Hresources
    icases Hresources with
      ⟨HR', Hglobal', HouterA', HouterB', Hx', Hy'⟩
    icases HR' with
      ⟨Hresult', HshiftXY', HshiftX', HshiftY', HnextY', HnextX'⟩
    iapply hcontinue
    iframe
  · iframe

/-- Complete left-zero path of the memory-backed GCD core. The result is
written through the callee frame, read back, and returned as an Iris value. -/
theorem func1_leftZero_core_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (result b : UInt64)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
        pointsTo_u64 1048512 b ∗
        pointsTo_u64 1048520 0 ∗ pointsTo_u64 1048528 b ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, [.i64 b]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 0 ∗ pointsTo_u64 1048528 b ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        func1.drop 12, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ Φ }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy⟩
  simp only [func1SpilledLocals, func1, List.drop]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) 0 $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) 0 =
          pointsTo_u64 1048520 0 :=
      congrArg (fun address => pointsTo_u64 address 0) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 0
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_constI64
  inext
  iapply Wasm.SmallStep.wp_eqI64 (result := 1) (by decide)
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  rw [show (1 &&& 1 : UInt32) = 1 by decide]
  iapply Wasm.SmallStep.wp_brIf (by decide) rfl
  inext
  simp only [List.take_nil, List.drop_nil, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) 0 $$ [Hx]
  · inext
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 0
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) b $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) b =
          pointsTo_u64 1048528 b :=
      congrArg (fun address => pointsTo_u64 address b) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_orI64
  inext
  rw [show (0 : UInt64) ||| b = b by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_or]
    simp]
  ihave HresultLater : ▷ pointsTo_u64 (1048512 + 0) result $$ [Hresult]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 0) result =
          pointsTo_u64 1048512 result :=
      congrArg (fun address => pointsTo_u64 address result) (by decide)
    rw [h]
    iexact Hresult
  iapply Wasm.SmallStep.wp_store64 result
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HresultLater
  inext
  iintro Hresult
  iapply Wasm.SmallStep.wp_br rfl
  inext
  simp only [List.take_nil, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HresultLater : ▷ pointsTo_u64 (1048512 + 0) b $$ [Hresult]
  · inext
    iexact Hresult
  iapply Wasm.SmallStep.wp_load64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HresultLater
  inext
  iintro Hresult
  have hResultProp :
      pointsTo_u64 ((1048512 : UInt32) + 0) b = pointsTo_u64 1048512 b :=
    congrArg (fun address => pointsTo_u64 address b) (by decide)
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8) 0 = pointsTo_u64 1048520 0 :=
    congrArg (fun address => pointsTo_u64 address 0) (by decide)
  have hYProp :
      pointsTo_u64 ((1048512 : UInt32) + 16) b = pointsTo_u64 1048528 b :=
    congrArg (fun address => pointsTo_u64 address b) (by decide)
  ihave HresultExact : pointsTo_u64 1048512 b $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  ihave HxExact : pointsTo_u64 1048520 0 $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 b $$ [Hy]
  · rw [← hYProp]
    iexact Hy
  simp only [func1SpilledLocals] at hreturn
  iapply hreturn
  iframe

/-- Closed top-level corollary of the contextual left-zero core. -/
theorem func1_leftZero_core_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (result b : UInt64) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 0 ∗ pointsTo_u64 1048528 b ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        func1.drop 12, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 b]⌝ ∗ R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
          pointsTo_u64 1048512 b ∗
          pointsTo_u64 1048520 0 ∗ pointsTo_u64 1048528 b }} := by
  iintro Hresources
  iapply func1_leftZero_core_smallStep_wp_to_return R [] result b
  · iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromFunction
    inext
    simp only [List.take, List.append_nil]
    iapply wp_value'
    isplit
    · ipureintro
      rfl
    · iexact Hresources
  · iexact Hresources

/-- Contextual end-to-end left-zero rule, retaining the caller's call stack
until the explicit return transition. -/
theorem func1_leftZero_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (result oldX oldY b : UInt64)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
        pointsTo_u64 1048512 b ∗
        pointsTo_u64 1048520 0 ∗ pointsTo_u64 1048528 b ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, [.i64 b]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy⟩
  iapply func1_spillPrefix_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048512 result))
    (calls := calls) (a := 0) (b := b) (oldX := oldX) (oldY := oldY)
  · iintro Hresources
    icases Hresources with
      ⟨HRresult, Hglobal', HouterA', HouterB', Hx', Hy'⟩
    icases HRresult with ⟨HR', Hresult'⟩
    iapply func1_leftZero_core_smallStep_wp_to_return
      R calls result b hreturn
    iframe
  · iframe

/-- End-to-end `func1` theorem for a zero left operand, including frame
allocation, pointer loads, spills, structured control, result memory, and the
top-level return transition. -/
theorem func1_leftZero_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (result oldX oldY b : UInt64) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 b]⌝ ∗ R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 0 ∗ pointsTo_u64 1048568 b ∗
          pointsTo_u64 1048512 b ∗
          pointsTo_u64 1048520 0 ∗ pointsTo_u64 1048528 b }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy⟩
  iapply func1_spillPrefix_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048512 result))
    (calls := []) (a := 0) (b := b) (oldX := oldX) (oldY := oldY)
  · iintro Hresources
    icases Hresources with
      ⟨HRresult, Hglobal', HouterA', HouterB', Hx', Hy'⟩
    icases HRresult with ⟨HR', Hresult'⟩
    iapply func1_leftZero_core_smallStep_wp R result b
    iframe
  · iframe

/-- Complete right-zero path of the memory-backed GCD core. The nonzero
left operand is preserved as the result. -/
theorem func1_rightZero_core_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (result a : UInt64) (ha : a ≠ 0)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
        pointsTo_u64 1048512 a ∗
        pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 0 ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, [.i64 a]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 0 ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        func1.drop 12, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ Φ }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy⟩
  simp only [func1SpilledLocals, func1, List.drop]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) a $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) a =
          pointsTo_u64 1048520 a :=
      congrArg (fun address => pointsTo_u64 address a) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_constI64
  inext
  iapply Wasm.SmallStep.wp_eqI64 (result := 0) (by simp [ha])
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  rw [show (0 &&& 1 : UInt32) = 0 by decide]
  iapply Wasm.SmallStep.wp_brIfZero
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) 0 $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) 0 =
          pointsTo_u64 1048528 0 :=
      congrArg (fun address => pointsTo_u64 address 0) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 0
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_constI64
  inext
  iapply Wasm.SmallStep.wp_eqI64 (result := 1) (by decide)
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  rw [show (1 &&& 1 : UInt32) = 1 by decide]
  iapply Wasm.SmallStep.wp_eqz (result := 0) (by decide)
  inext
  iapply Wasm.SmallStep.wp_brIfZero
  inext
  iapply Wasm.SmallStep.wp_exitControl rfl
  inext
  simp only [List.take_nil, List.drop_nil, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) a $$ [Hx]
  · inext
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) 0 $$ [Hy]
  · inext
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 0
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_orI64
  inext
  rw [show a ||| (0 : UInt64) = a by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_or]
    simp]
  ihave HresultLater : ▷ pointsTo_u64 (1048512 + 0) result $$ [Hresult]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 0) result =
          pointsTo_u64 1048512 result :=
      congrArg (fun address => pointsTo_u64 address result) (by decide)
    rw [h]
    iexact Hresult
  iapply Wasm.SmallStep.wp_store64 result
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HresultLater
  inext
  iintro Hresult
  iapply Wasm.SmallStep.wp_br rfl
  inext
  simp only [List.take_nil, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HresultLater : ▷ pointsTo_u64 (1048512 + 0) a $$ [Hresult]
  · inext
    iexact Hresult
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HresultLater
  inext
  iintro Hresult
  have hResultProp :
      pointsTo_u64 ((1048512 : UInt32) + 0) a = pointsTo_u64 1048512 a :=
    congrArg (fun address => pointsTo_u64 address a) (by decide)
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8) a = pointsTo_u64 1048520 a :=
    congrArg (fun address => pointsTo_u64 address a) (by decide)
  have hYProp :
      pointsTo_u64 ((1048512 : UInt32) + 16) 0 = pointsTo_u64 1048528 0 :=
    congrArg (fun address => pointsTo_u64 address 0) (by decide)
  ihave HresultExact : pointsTo_u64 1048512 a $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  ihave HxExact : pointsTo_u64 1048520 a $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 0 $$ [Hy]
  · rw [← hYProp]
    iexact Hy
  simp only [func1SpilledLocals] at hreturn
  iapply hreturn
  iframe

/-- Closed top-level corollary of the contextual right-zero core. -/
theorem func1_rightZero_core_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (result a : UInt64) (ha : a ≠ 0) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 0 ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        func1.drop 12, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 a]⌝ ∗ R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
          pointsTo_u64 1048512 a ∗
          pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 0 }} := by
  iintro Hresources
  iapply func1_rightZero_core_smallStep_wp_to_return R [] result a ha
  · iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromFunction
    inext
    simp only [List.take]
    iapply wp_value'
    isplit
    · ipureintro
      rfl
    · iexact Hresources
  · iexact Hresources

/-- Contextual end-to-end right-zero rule, retaining the caller's call stack
until the explicit return transition. -/
theorem func1_rightZero_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (result oldX oldY a : UInt64) (ha : a ≠ 0)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
        pointsTo_u64 1048512 a ∗
        pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 0 ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, [.i64 a]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy⟩
  iapply func1_spillPrefix_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048512 result))
    (calls := calls) (a := a) (b := 0) (oldX := oldX) (oldY := oldY)
  · iintro Hresources
    icases Hresources with
      ⟨HRresult, Hglobal', HouterA', HouterB', Hx', Hy'⟩
    icases HRresult with ⟨HR', Hresult'⟩
    iapply func1_rightZero_core_smallStep_wp_to_return
      R calls result a ha hreturn
    iframe
  · iframe

/-- End-to-end `func1` theorem for a nonzero left operand and zero right
operand, including the memory spill prologue. -/
theorem func1_rightZero_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (result oldX oldY a : UInt64) (ha : a ≠ 0) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 a]⌝ ∗ R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 0 ∗
          pointsTo_u64 1048512 a ∗
          pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 0 }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy⟩
  iapply func1_spillPrefix_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048512 result))
    (calls := []) (a := a) (b := 0) (oldX := oldX) (oldY := oldY)
  · iintro Hresources
    icases Hresources with
      ⟨HRresult, Hglobal', HouterA', HouterB', Hx', Hy'⟩
    icases HRresult with ⟨HR', Hresult'⟩
    iapply func1_rightZero_core_smallStep_wp R result a ha
    iframe
  · iframe

/-- Public zero-case rule for `func1`, phrased using the mathematical GCD
result rather than the compiler's two control-flow branches. -/
theorem func1_zero_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (result oldX oldY a b : UInt64) (hz : a = 0 ∨ b = 0) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
          R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
          pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
          pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b }} := by
  rcases hz with ha | hb
  · subst a
    simpa using func1_leftZero_smallStep_wp R result oldX oldY b
  · subst b
    by_cases ha : a = 0
    · subst a
      simpa using func1_leftZero_smallStep_wp R result oldX oldY 0
    · simpa using func1_rightZero_smallStep_wp R result oldX oldY a ha

/-- Finite-heap form of the complete zero-case rule. This is the shape needed
by the authoritative heap adequacy theorem. -/
theorem func1_zero_frame_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (result oldX oldY : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (a b : UInt64) (hz : a = 0 ∨ b = 0) :
    globalPointsTo 0 (.i32 1048560) ∗
      ([∗map] address ↦ byte ∈
        gcdFrameHeap result oldX oldY shiftXY shiftX shiftY nextY nextX a b,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) byte) ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
          (pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
            pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
            pointsTo_u32 1048540 nextX) ∗
          globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
          pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
          pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b }} := by
  iintro ⟨Hglobal, Hframe⟩
  ihave Hslots := gcdFrameHeap_pointsTo
    result oldX oldY shiftXY shiftX shiftY nextY nextX a b $$ Hframe
  icases Hslots with
    ⟨Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY, HnextY, HnextX,
      HouterA, HouterB⟩
  iapply func1_zero_smallStep_wp
    (R := iprop(pointsTo_u32 1048556 shiftXY ∗
      pointsTo_u32 1048552 shiftX ∗ pointsTo_u32 1048548 shiftY ∗
      pointsTo_u32 1048544 nextY ∗ pointsTo_u32 1048540 nextX))
    result oldX oldY a b hz
  iframe

def func1GlobalHeap : WasmGlobalMap Value :=
  insert ∅ 0 (.i32 1048560)

theorem func1GlobalHeap_agrees :
    globalHeapAgrees func1GlobalHeap
      ({ globals := [.i32 1048560, .i32 1048576, .i32 1048576] } :
        Globals) := by
  intro index value hget
  unfold func1GlobalHeap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (Ne.symm hindex), get?_empty] at hget
    contradiction

theorem func1GlobalHeap_pointsTo [WasmGlobalGS] :
    ([∗map] index ↦ value ∈ func1GlobalHeap,
      globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048560) := by
  unfold func1GlobalHeap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty 0)).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  exact .rfl

def func1ZeroConfig
    (result oldX oldY : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (a b : UInt64) : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm :=
          { initial with
            mem := gcdFrameMem initial.mem result oldX oldY
              shiftXY shiftX shiftY nextY nextX a b
            globals :=
              { globals := [.i32 1048560, .i32 1048576, .i32 1048576] } } } }

/-- Closed operational partial correctness for both zero cases of opt0
`func1`, obtained from iris-lean adequacy and authoritative physical memory. -/
theorem func1_zero_smallStep_partiallyMeets
    (result oldX oldY : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (a b : UInt64) (hz : a = 0 ∨ b = 0) :
    Wasm.SmallStep.PartiallyMeets
      (func1ZeroConfig result oldX oldY shiftXY shiftX shiftY nextY nextX a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
    (α := Unit)
    (σ := gcdFrameHeap result oldX oldY
      shiftXY shiftX shiftY nextY nextX a b)
    (globalσ := func1GlobalHeap)
    (φ := fun rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])
  · exact gcdFrameHeap_agrees («module».initialStore : Store Unit).mem
      result oldX oldY shiftXY shiftX shiftY nextY nextX a b
  · apply gcdFrameHeap_inBounds
    rfl
  · exact func1GlobalHeap_agrees
  · intro gs
    iintro ⟨Hframe, Hglobals, Hruntime⟩
    ihave Hglobal := func1GlobalHeap_pointsTo $$ Hglobals
    have hpost : ∀ rs : List Value,
        (iprop(
          ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
            (pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
              pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
              pointsTo_u32 1048540 nextX) ∗
            globalPointsTo 0 (.i32 1048560) ∗
            pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
            pointsTo_u64 1048512
              (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
            pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b)) ⊢
          (iprop(⌜rs =
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝)) := by
      intro rs
      iintro ⟨%hrs, _Hresources⟩
      ipureintro
      exact hrs
    simp only [func1ZeroConfig]
    iclear Hruntime
    iapply wp_mono hpost
    iapply func1_zero_frame_smallStep_wp
      result oldX oldY shiftXY shiftX shiftY nextY nextX a b hz
    iframe

/-! ## Shift-amount bridge

The wasm computes each Stein shift count by `i64.ctz`, narrows it to an
`i32` (`i32.wrap_i64`), spills/reloads it through a scratch slot, masks
with `& 63`, and widens back with `i64.extend_i32_u` before the shift.
For a nonzero operand `v` (so `ctz64 64 v < 64`) all of that is the
identity on the value: the resulting `i32` is exactly `UInt32.ofNat
(ctz64 64 v)` and the widened+masked shift count matches the form used
by the `CodeLib` Stein lemmas. -/

/-- The masked, narrowed `ctz` of a nonzero `v` is `ctz64 64 v` (in the exact
`i32`-level `63 &&& _` form the interpreter produces). -/
theorem ctz_wrap_and_toNat (v : UInt64) (hv : v ≠ 0) :
    ((63 : UInt32) &&& UInt32.ofNat ((UInt64.ofNat (ctz64 64 v)).toNat % 2 ^ 32)).toNat
      = ctz64 64 v := by
  have hlt : ctz64 64 v < 64 := UInt64.ctz64_lt v hv
  have hsz64 : UInt64.size = 2 ^ 64 := rfl
  have hsz32 : UInt32.size = 2 ^ 32 := rfl
  rw [UInt32.toNat_and]
  rw [UInt64.toNat_ofNat_of_lt' (show ctz64 64 v < UInt64.size by rw [hsz64]; omega)]
  rw [UInt32.toNat_ofNat_of_lt' (show ctz64 64 v % 2 ^ 32 < UInt32.size by
        rw [hsz32, Nat.mod_eq_of_lt (show ctz64 64 v < 2 ^ 32 by omega)]; omega)]
  rw [Nat.mod_eq_of_lt (show ctz64 64 v < 2 ^ 32 by omega)]
  show (63 : UInt32).toNat &&& ctz64 64 v = ctz64 64 v
  have h63 : (63 : UInt32).toNat = 63 := rfl
  rw [h63, Nat.and_comm, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod (ctz64 64 v) 6]
  exact Nat.mod_eq_of_lt (by simpa using hlt)

/-- The full narrow→reload→mask→widen pipeline applied to `v ≠ 0` lands on
the `CodeLib` shift count (interpreter `i32`-level `63 &&& _` form). -/
theorem shift_pipeline (v : UInt64) (hv : v ≠ 0) :
    UInt64.ofNat
        ((63 : UInt32) &&& UInt32.ofNat ((UInt64.ofNat (ctz64 64 v)).toNat % 2 ^ 32)).toNat % 64
      = UInt64.ofNat (ctz64 64 v) % 64 := by
  rw [ctz_wrap_and_toNat v hv]

/-! ## `func1`: the binary-GCD loop through memory -/

/-- ctz of `a ||| b` equals ctz of `b ||| a` (OR is commutative). -/
theorem ctz_or_comm (a b : UInt64) : ctz64 64 (a ||| b) = ctz64 64 (b ||| a) := by
  rw [UInt64.or_comm]

/-- The `UInt64` odd-part shift, as a `Nat` shift (the form the `CodeLib`
Stein step lemmas produce). -/
theorem oddPart_toNat (v : UInt64) :
    (v >>> (UInt64.ofNat (ctz64 64 v) % 64)).toNat
      = v.toNat >>> (ctz64 64 v % 64) := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_mod]
  congr 1
  rw [UInt64.toNat_ofNat', show UInt64.toNat 64 = 64 from rfl,
      Nat.mod_mod_of_dvd _ (by norm_num : (64 : Nat) ∣ 2 ^ 64), Nat.mod_mod]

/-- The OUTER-body program of `func1`: the Stein "meat" (compute the shift
count and both odd parts) followed by the subtract-and-halve `loop`. It is
factored out so its giant continuation never sits under a `simp` driving
the small zero-check blocks. -/
def meatLoopProg : Program :=
  [ .localGet 2, .localGet 2, .load64 8, .localGet 2, .load64 16, .orI64,
    .ctzI64, .wrapI64, .store32 44,
    .localGet 2, .load32 44, .localSet 3,
    .localGet 2, .localGet 2, .load64 8, .ctzI64, .wrapI64, .store32 40,
    .localGet 2, .load32 40, .localSet 4,
    .localGet 2, .localGet 2, .load64 8, .localGet 4, .const 63, .and,
    .extendUI32, .shrUI64, .store64 8,
    .localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 36,
    .localGet 2, .load32 36, .localSet 5,
    .localGet 2, .localGet 2, .load64 16, .localGet 5, .const 63, .and,
    .extendUI32, .shrUI64, .store64 16,
    .loop 0 0 [
      .block 0 0 [
        .localGet 2, .load64 8, .localGet 2, .load64 16, .neI64, .const 1, .and,
        .br_if 0,
        .localGet 2, .localGet 2, .load64 8, .localGet 3, .const 63, .and,
        .extendUI32, .shlI64, .store64 0,
        .br 2 ],
      .block 0 0 [
        .localGet 2, .load64 8, .localGet 2, .load64 16, .gtUI64, .const 1, .and,
        .br_if 0,
        .localGet 2, .load64 8, .localSet 6,
        .localGet 2, .localGet 2, .load64 16, .localGet 6, .subI64, .store64 16,
        .localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 32,
        .localGet 2, .load32 32, .localSet 7,
        .localGet 2, .localGet 2, .load64 16, .localGet 7, .const 63, .and,
        .extendUI32, .shrUI64, .store64 16,
        .br 1 ],
      .localGet 2, .load64 16, .localSet 8,
      .localGet 2, .localGet 2, .load64 8, .localGet 8, .subI64, .store64 8,
      .localGet 2, .localGet 2, .load64 8, .ctzI64, .wrapI64, .store32 28,
      .localGet 2, .load32 28, .localSet 9,
      .localGet 2, .localGet 2, .load64 8, .localGet 9, .const 63, .and,
      .extendUI32, .shrUI64, .store64 8,
      .br 0 ] ]

def sharedShiftWord (a b : UInt64) : UInt32 :=
  UInt32.ofNat
    ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)

def func1SharedShiftLocals (a b : UInt64) : List Value :=
  [.i32 1048512, .i32 (sharedShiftWord a b), .i32 0, .i32 0,
    .i64 0, .i32 0, .i64 0, .i32 0]

/-- First nonzero normalization slice: compute `ctz (a | b)`, narrow it,
store/reload it through scratch offset 44, and install it in local 3. -/
theorem func1_sharedShift_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b : UInt64) (oldShift : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ∗
        pointsTo_u32 1048556 (sharedShiftWord a b) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SharedShiftLocals a b, []⟩,
          meatLoopProg.drop 12, 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ∗
      pointsTo_u32 1048556 oldShift ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        meatLoopProg, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy, Hshift⟩
  simp only [meatLoopProg, func1SpilledLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) a $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) a =
          pointsTo_u64 1048520 a :=
      congrArg (fun address => pointsTo_u64 address a) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) b $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) b =
          pointsTo_u64 1048528 b :=
      congrArg (fun address => pointsTo_u64 address b) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_orI64
  inext
  iapply Wasm.SmallStep.wp_ctzI64
  inext
  iapply Wasm.SmallStep.wp_wrapI64
  inext
  ihave HshiftLater :
      ▷ pointsTo_u32 (1048512 + 44) oldShift $$ [Hshift]
  · inext
    have h :
        pointsTo_u32 ((1048512 : UInt32) + 44) oldShift =
          pointsTo_u32 1048556 oldShift :=
      congrArg (fun address => pointsTo_u32 address oldShift) (by decide)
    rw [h]
    iexact Hshift
  iapply Wasm.SmallStep.wp_store32 oldShift
      (by decide) (by decide) (by decide) (by decide) $$ HshiftLater
  inext
  iintro Hshift
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HshiftLater :
      ▷ pointsTo_u32 (1048512 + 44) (sharedShiftWord a b) $$ [Hshift]
  · inext
    rw [sharedShiftWord]
    iexact Hshift
  iapply Wasm.SmallStep.wp_load32 (sharedShiftWord a b)
      (by decide) (by decide) (by decide) (by decide) $$ HshiftLater
  inext
  iintro Hshift
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  simp only [func1SharedShiftLocals, meatLoopProg, List.drop]
    at hcontinue
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8) a = pointsTo_u64 1048520 a :=
    congrArg (fun address => pointsTo_u64 address a) (by decide)
  have hYProp :
      pointsTo_u64 ((1048512 : UInt32) + 16) b = pointsTo_u64 1048528 b :=
    congrArg (fun address => pointsTo_u64 address b) (by decide)
  have hShiftProp :
      pointsTo_u32 ((1048512 : UInt32) + 44) (sharedShiftWord a b) =
        pointsTo_u32 1048556 (sharedShiftWord a b) :=
    congrArg (fun address => pointsTo_u32 address (sharedShiftWord a b)) (by decide)
  ihave HxExact : pointsTo_u64 1048520 a $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 b $$ [Hy]
  · rw [← hYProp]
    iexact Hy
  ihave HshiftExact :
      pointsTo_u32 1048556 (sharedShiftWord a b) $$ [Hshift]
  · rw [← hShiftProp]
    iexact Hshift
  iapply hcontinue
  iframe

def operandShiftWord (v : UInt64) : UInt32 :=
  UInt32.ofNat ((UInt64.ofNat (ctz64 64 v)).toNat % 2 ^ 32)

def oddPart64 (v : UInt64) : UInt64 :=
  v >>> (UInt64.ofNat (ctz64 64 v) % 64)

def func1XShiftLocals (a b : UInt64) : List Value :=
  [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
    .i32 0, .i64 0, .i32 0, .i64 0, .i32 0]

/-- Normalize the first nonzero operand to its odd part through scratch offset
40, preserving the shared shift count installed by the preceding slice. -/
theorem func1_normalizeX_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b : UInt64) (ha : a ≠ 0) (oldShiftX : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 (oddPart64 a) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1XShiftLocals a b, []⟩,
          meatLoopProg.drop 30, 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u32 1048552 oldShiftX ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SharedShiftLocals a b, []⟩,
        meatLoopProg.drop 12, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, HshiftX⟩
  simp only [meatLoopProg, List.drop, func1SharedShiftLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) a $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) a =
          pointsTo_u64 1048520 a :=
      congrArg (fun address => pointsTo_u64 address a) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_ctzI64
  inext
  iapply Wasm.SmallStep.wp_wrapI64
  inext
  ihave HshiftXLater :
      ▷ pointsTo_u32 (1048512 + 40) oldShiftX $$ [HshiftX]
  · inext
    have h :
        pointsTo_u32 ((1048512 : UInt32) + 40) oldShiftX =
          pointsTo_u32 1048552 oldShiftX :=
      congrArg (fun address => pointsTo_u32 address oldShiftX) (by decide)
    rw [h]
    iexact HshiftX
  iapply Wasm.SmallStep.wp_store32 oldShiftX
      (by decide) (by decide) (by decide) (by decide) $$ HshiftXLater
  inext
  iintro HshiftX
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HshiftXLater :
      ▷ pointsTo_u32 (1048512 + 40) (operandShiftWord a) $$ [HshiftX]
  · inext
    rw [operandShiftWord]
    iexact HshiftX
  iapply Wasm.SmallStep.wp_load32 (operandShiftWord a)
      (by decide) (by decide) (by decide) (by decide) $$ HshiftXLater
  inext
  iintro HshiftX
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) a $$ [Hx]
  · inext
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  iapply Wasm.SmallStep.wp_extendUI32
  inext
  iapply Wasm.SmallStep.wp_shrUI64
  inext
  rw [UInt32.and_comm (operandShiftWord a) 63]
  unfold operandShiftWord
  rw [shift_pipeline a ha]
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) a $$ [Hx]
  · inext
    iexact Hx
  iapply Wasm.SmallStep.wp_store64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  simp only [func1XShiftLocals, operandShiftWord, oddPart64,
    meatLoopProg, List.drop] at hcontinue
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8)
          (a >>> (UInt64.ofNat (ctz64 64 a) % 64)) =
        pointsTo_u64 1048520
          (a >>> (UInt64.ofNat (ctz64 64 a) % 64)) :=
    congrArg
      (fun address =>
        pointsTo_u64 address (a >>> (UInt64.ofNat (ctz64 64 a) % 64)))
      (by decide)
  have hShiftProp :
      pointsTo_u32 ((1048512 : UInt32) + 40)
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 a)).toNat % 2 ^ 32)) =
        pointsTo_u32 1048552
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 a)).toNat % 2 ^ 32)) :=
    congrArg
      (fun address => pointsTo_u32 address
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 a)).toNat % 2 ^ 32)))
      (by decide)
  ihave HxExact :
      pointsTo_u64 1048520
        (a >>> (UInt64.ofNat (ctz64 64 a) % 64)) $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HshiftExact :
      pointsTo_u32 1048552
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 a)).toNat % 2 ^ 32)) $$ [HshiftX]
  · rw [← hShiftProp]
    iexact HshiftX
  iapply hcontinue
  iframe

def func1LoopHeaderLocals
    (a b c6 c8 : UInt64) (c7 c9 : UInt32) : List Value :=
  [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
    .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 c8, .i32 c9]

def func1NormalizedLocals (a b : UInt64) : List Value :=
  func1LoopHeaderLocals a b 0 0 0 0

/-- Normalize the second nonzero operand through scratch offset 36 and hand
off with both frame operands reduced to their odd parts. -/
theorem func1_normalizeY_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b : UInt64) (hb : b ≠ 0) (oldShiftY : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048528 (oddPart64 b) ∗
        pointsTo_u32 1048548 (operandShiftWord b) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1NormalizedLocals a b, []⟩,
          meatLoopProg.drop 48, 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048528 b ∗ pointsTo_u32 1048548 oldShiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1XShiftLocals a b, []⟩,
        meatLoopProg.drop 30, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hy, HshiftY⟩
  simp only [meatLoopProg, List.drop, func1XShiftLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) b $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) b =
          pointsTo_u64 1048528 b :=
      congrArg (fun address => pointsTo_u64 address b) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_ctzI64
  inext
  iapply Wasm.SmallStep.wp_wrapI64
  inext
  ihave HshiftYLater :
      ▷ pointsTo_u32 (1048512 + 36) oldShiftY $$ [HshiftY]
  · inext
    have h :
        pointsTo_u32 ((1048512 : UInt32) + 36) oldShiftY =
          pointsTo_u32 1048548 oldShiftY :=
      congrArg (fun address => pointsTo_u32 address oldShiftY) (by decide)
    rw [h]
    iexact HshiftY
  iapply Wasm.SmallStep.wp_store32 oldShiftY
      (by decide) (by decide) (by decide) (by decide) $$ HshiftYLater
  inext
  iintro HshiftY
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HshiftYLater :
      ▷ pointsTo_u32 (1048512 + 36) (operandShiftWord b) $$ [HshiftY]
  · inext
    rw [operandShiftWord]
    iexact HshiftY
  iapply Wasm.SmallStep.wp_load32 (operandShiftWord b)
      (by decide) (by decide) (by decide) (by decide) $$ HshiftYLater
  inext
  iintro HshiftY
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) b $$ [Hy]
  · inext
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  iapply Wasm.SmallStep.wp_extendUI32
  inext
  iapply Wasm.SmallStep.wp_shrUI64
  inext
  rw [UInt32.and_comm (operandShiftWord b) 63]
  unfold operandShiftWord
  rw [shift_pipeline b hb]
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) b $$ [Hy]
  · inext
    iexact Hy
  iapply Wasm.SmallStep.wp_store64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  simp only [func1NormalizedLocals, func1LoopHeaderLocals,
    operandShiftWord, oddPart64,
    meatLoopProg, List.drop] at hcontinue
  have hYProp :
      pointsTo_u64 ((1048512 : UInt32) + 16)
          (b >>> (UInt64.ofNat (ctz64 64 b) % 64)) =
        pointsTo_u64 1048528
          (b >>> (UInt64.ofNat (ctz64 64 b) % 64)) :=
    congrArg
      (fun address =>
        pointsTo_u64 address (b >>> (UInt64.ofNat (ctz64 64 b) % 64)))
      (by decide)
  have hShiftProp :
      pointsTo_u32 ((1048512 : UInt32) + 36)
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 b)).toNat % 2 ^ 32)) =
        pointsTo_u32 1048548
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 b)).toNat % 2 ^ 32)) :=
    congrArg
      (fun address => pointsTo_u32 address
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 b)).toNat % 2 ^ 32)))
      (by decide)
  ihave HyExact :
      pointsTo_u64 1048528
        (b >>> (UInt64.ofNat (ctz64 64 b) % 64)) $$ [Hy]
  · rw [← hYProp]
    iexact Hy
  ihave HshiftExact :
      pointsTo_u32 1048548
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 b)).toNat % 2 ^ 32)) $$ [HshiftY]
  · rw [← hShiftProp]
    iexact HshiftY
  iapply hcontinue
  iframe

/-- Complete nonzero normalization prefix, composed from the three physical
scratch-memory slices. The next instruction is the generated Stein loop. -/
theorem func1_normalization_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (oldShared oldShiftX oldShiftY : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 (oddPart64 a) ∗
        pointsTo_u64 1048528 (oddPart64 b) ∗
        pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ∗
        pointsTo_u32 1048548 (operandShiftWord b) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1NormalizedLocals a b, []⟩,
          meatLoopProg.drop 48, 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ∗
      pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldShiftX ∗ pointsTo_u32 1048548 oldShiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        meatLoopProg, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy, Hshared, HshiftX, HshiftY⟩
  iapply func1_sharedShift_smallStep_wp
    (R := iprop(R ∗ pointsTo_u32 1048552 oldShiftX ∗
      pointsTo_u32 1048548 oldShiftY))
    controls calls a b oldShared
  · iintro Hresources
    icases Hresources with ⟨HRshifts, Hx', Hy', Hshared'⟩
    icases HRshifts with ⟨HR', HshiftX', HshiftY'⟩
    iapply func1_normalizeX_smallStep_wp
      (R := iprop(R ∗ pointsTo_u64 1048528 b ∗
        pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048548 oldShiftY))
      controls calls a b ha oldShiftX
    · iintro Hresources
      icases Hresources with ⟨HRrest, HxOdd, HshiftXNew⟩
      icases HRrest with ⟨HR'', Hy'', Hshared'', HshiftY''⟩
      iapply func1_normalizeY_smallStep_wp
        (R := iprop(R ∗ pointsTo_u64 1048520 (oddPart64 a) ∗
          pointsTo_u32 1048556 (sharedShiftWord a b) ∗
          pointsTo_u32 1048552 (operandShiftWord a)))
        controls calls a b hb oldShiftY
      · iintro Hresources
        icases Hresources with ⟨HRfinal, HyOdd, HshiftYNew⟩
        icases HRfinal with ⟨HR''', HxOdd', Hshared''', HshiftXNew'⟩
        iapply hcontinue
        iframe
      · iframe
    · iframe
  · iframe

def equalRecombineProg : Program :=
  [.localGet 2, .localGet 2, .load64 8, .localGet 3, .const 63, .and,
    .extendUI32, .shlI64, .store64 0, .br 2]

def equalityBlockBody : Program :=
  [.localGet 2, .load64 8, .localGet 2, .load64 16, .neI64, .const 1, .and,
    .br_if 0] ++ equalRecombineProg

def recombinedWord (a b g : UInt64) : UInt64 :=
  g <<< (UInt64.ofNat ((sharedShiftWord a b &&& 63).toNat) % 64)

theorem recombinedWord_eq_gcd
    (a b g : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (hg :
      g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat) :
    recombinedWord a b g =
      UInt64.ofNat (Nat.gcd a.toNat b.toNat) := by
  have hab0 : a ||| b ≠ 0 :=
    fun h => ha (UInt64.or_eq_zero_iff.mp h).1
  have hshift :
      UInt64.ofNat ((sharedShiftWord a b &&& 63).toNat) % 64 =
        UInt64.ofNat (ctz64 64 (b ||| a)) % 64 := by
    rw [UInt32.and_comm, sharedShiftWord,
      ctz_wrap_and_toNat (a ||| b) hab0, ctz_or_comm]
  rw [recombinedWord, hshift]
  apply UInt64.recombine_loop a b g ha hb
  rw [Nat.gcd_self, hg]
  simp only [oddPart64, oddPart_toNat]

/-- Equality exit tail of the memory-backed Stein loop. The surviving odd
value is recombined with the shared power of two and written to result slot
zero; the administrative `br 2` is deliberately left to the surrounding
control-frame theorem. -/
theorem func1_equalRecombine_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b g oldResult : UInt64)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 g ∗
        pointsTo_u64 1048512 (recombinedWord a b g) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
          [.br 2], 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048512 oldResult ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        equalRecombineProg, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hresult⟩
  simp only [equalRecombineProg, func1LoopHeaderLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) g $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) g =
          pointsTo_u64 1048520 g :=
      congrArg (fun address => pointsTo_u64 address g) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 g
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  iapply Wasm.SmallStep.wp_extendUI32
  inext
  iapply Wasm.SmallStep.wp_shlI64
  inext
  ihave HresultLater :
      ▷ pointsTo_u64 (1048512 + 0) oldResult $$ [Hresult]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 0) oldResult =
          pointsTo_u64 1048512 oldResult :=
      congrArg (fun address => pointsTo_u64 address oldResult) (by decide)
    rw [h]
    iexact Hresult
  iapply Wasm.SmallStep.wp_store64 oldResult
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HresultLater
  inext
  iintro Hresult
  simp only [func1LoopHeaderLocals, recombinedWord] at hcontinue
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8) g = pointsTo_u64 1048520 g :=
    congrArg (fun address => pointsTo_u64 address g) (by decide)
  have hResultProp :
      pointsTo_u64 ((1048512 : UInt32) + 0)
          (g <<< (UInt64.ofNat ((sharedShiftWord a b &&& 63).toNat) % 64)) =
        pointsTo_u64 1048512
          (g <<< (UInt64.ofNat ((sharedShiftWord a b &&& 63).toNat) % 64)) :=
    congrArg
      (fun address => pointsTo_u64 address
        (g <<< (UInt64.ofNat ((sharedShiftWord a b &&& 63).toNat) % 64)))
      (by decide)
  ihave HxExact : pointsTo_u64 1048520 g $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HresultExact :
      pointsTo_u64 1048512
        (g <<< (UInt64.ofNat ((sharedShiftWord a b &&& 63).toNat) % 64)) $$
        [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  iapply hcontinue
  iframe

/-- Equality arm of the first generated loop block. When the two normalized
operands agree, the guard falls through to `func1_equalRecombine_smallStep_wp`.
The final `br 2` remains visible to the enclosing loop/control proof. -/
theorem func1_equalBlock_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b g oldResult : UInt64)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
        pointsTo_u64 1048512 (recombinedWord a b g) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
          [.br 2], 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
      pointsTo_u64 1048512 oldResult ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        equalityBlockBody, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy, Hresult⟩
  rw [show equalityBlockBody =
    [.localGet 2, .load64 8, .localGet 2, .load64 16, .neI64, .const 1, .and,
      .br_if 0, .localGet 2, .localGet 2, .load64 8, .localGet 3, .const 63,
      .and, .extendUI32, .shlI64, .store64 0, .br 2] from rfl]
  simp only [func1LoopHeaderLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) g $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) g =
          pointsTo_u64 1048520 g :=
      congrArg (fun address => pointsTo_u64 address g) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 g
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) g $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) g =
          pointsTo_u64 1048528 g :=
      congrArg (fun address => pointsTo_u64 address g) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 g
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_neI64 (result := 0) (by simp)
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply Wasm.SmallStep.wp_brIfZero
  inext
  rw [show
    [.localGet 2, .localGet 2, .load64 8, .localGet 3, .const 63, .and,
      .extendUI32, .shlI64, .store64 0, .br 2] = equalRecombineProg from rfl]
  rw [show
    [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
      .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 c8, .i32 c9] =
      func1LoopHeaderLocals a b c6 c8 c7 c9 from rfl]
  ihave HxExact : pointsTo_u64 1048520 g $$ [Hx]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) g =
          pointsTo_u64 1048520 g :=
      congrArg (fun address => pointsTo_u64 address g) (by decide)
    rw [← h]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 g $$ [Hy]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) g =
          pointsTo_u64 1048528 g :=
      congrArg (fun address => pointsTo_u64 address g) (by decide)
    rw [← h]
    iexact Hy
  iapply func1_equalRecombine_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048528 g))
    controls calls a b g oldResult c6 c8 c7 c9
  · iintro Hresources
    icases Hresources with ⟨⟨HR', Hy'⟩, Hx', Hresult'⟩
    iapply hcontinue
    iframe
  · iframe

def loopNormalizeYProg : Program :=
  [.localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 32,
    .localGet 2, .load32 32, .localSet 7,
    .localGet 2, .localGet 2, .load64 16, .localGet 7, .const 63, .and,
    .extendUI32, .shrUI64, .store64 16, .br 1]

def func1LoopYLocals
    (a b x c8 : UInt64) (c7 c9 : UInt32) : List Value :=
  [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
    .i32 (operandShiftWord b), .i64 x, .i32 c7, .i64 c8, .i32 c9]

def func1LoopYNormalizedLocals
    (a b x d c8 : UInt64) (c9 : UInt32) : List Value :=
  [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
    .i32 (operandShiftWord b), .i64 x, .i32 (operandShiftWord d),
    .i64 c8, .i32 c9]

/-- Normalize the newly subtracted right operand in the generated
`y := oddPart (y - x)` arm. This owns exactly the mutable operand and its
scratch shift-count slot and exposes the arm's `br 1` to its block proof. -/
theorem func1_loopNormalizeY_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b x d : UInt64) (hd : d ≠ 0) (oldShift : UInt32)
    (c8 : UInt64) (c7 c9 : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048528 (oddPart64 d) ∗
        pointsTo_u32 1048544 (operandShiftWord d) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopYNormalizedLocals a b x d c8 c9, []⟩,
          [.br 1], 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048528 d ∗ pointsTo_u32 1048544 oldShift ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopYLocals a b x c8 c7 c9, []⟩,
        loopNormalizeYProg, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hy, Hshift⟩
  simp only [loopNormalizeYProg, func1LoopYLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) d $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) d =
          pointsTo_u64 1048528 d :=
      congrArg (fun address => pointsTo_u64 address d) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 d
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_ctzI64
  inext
  iapply Wasm.SmallStep.wp_wrapI64
  inext
  ihave HshiftLater :
      ▷ pointsTo_u32 (1048512 + 32) oldShift $$ [Hshift]
  · inext
    have h :
        pointsTo_u32 ((1048512 : UInt32) + 32) oldShift =
          pointsTo_u32 1048544 oldShift :=
      congrArg (fun address => pointsTo_u32 address oldShift) (by decide)
    rw [h]
    iexact Hshift
  iapply Wasm.SmallStep.wp_store32 oldShift
      (by decide) (by decide) (by decide) (by decide) $$ HshiftLater
  inext
  iintro Hshift
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HshiftLater :
      ▷ pointsTo_u32 (1048512 + 32) (operandShiftWord d) $$ [Hshift]
  · inext
    rw [operandShiftWord]
    iexact Hshift
  iapply Wasm.SmallStep.wp_load32 (operandShiftWord d)
      (by decide) (by decide) (by decide) (by decide) $$ HshiftLater
  inext
  iintro Hshift
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) d $$ [Hy]
  · inext
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 d
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  iapply Wasm.SmallStep.wp_extendUI32
  inext
  iapply Wasm.SmallStep.wp_shrUI64
  inext
  rw [UInt32.and_comm (operandShiftWord d) 63]
  unfold operandShiftWord
  rw [shift_pipeline d hd]
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) d $$ [Hy]
  · inext
    iexact Hy
  iapply Wasm.SmallStep.wp_store64 d
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  simp only [func1LoopYNormalizedLocals, operandShiftWord, oddPart64] at hcontinue
  have hYProp :
      pointsTo_u64 ((1048512 : UInt32) + 16)
          (d >>> (UInt64.ofNat (ctz64 64 d) % 64)) =
        pointsTo_u64 1048528
          (d >>> (UInt64.ofNat (ctz64 64 d) % 64)) :=
    congrArg
      (fun address =>
        pointsTo_u64 address (d >>> (UInt64.ofNat (ctz64 64 d) % 64)))
      (by decide)
  have hShiftProp :
      pointsTo_u32 ((1048512 : UInt32) + 32)
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)) =
        pointsTo_u32 1048544
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)) :=
    congrArg
      (fun address => pointsTo_u32 address
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)))
      (by decide)
  ihave HyExact :
      pointsTo_u64 1048528
        (d >>> (UInt64.ofNat (ctz64 64 d) % 64)) $$ [Hy]
  · rw [← hYProp]
    iexact Hy
  ihave HshiftExact :
      pointsTo_u32 1048544
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)) $$
        [Hshift]
  · rw [← hShiftProp]
    iexact Hshift
  iapply hcontinue
  iframe

def loopDecreaseYProg : Program :=
  [.localGet 2, .load64 8, .localSet 6,
    .localGet 2, .localGet 2, .load64 16, .localGet 6, .subI64, .store64 16] ++
    loopNormalizeYProg

/-- Complete generated right-decreasing arm before administrative branch
handling. It computes `y - x` through the physical frame, then delegates its
odd-part normalization to `func1_loopNormalizeY_smallStep_wp`. -/
theorem func1_loopDecreaseY_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b x y : UInt64) (hsub : y - x ≠ 0)
    (oldShift : UInt32)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 x ∗
        pointsTo_u64 1048528 (oddPart64 (y - x)) ∗
        pointsTo_u32 1048544 (operandShiftWord (y - x)) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopYNormalizedLocals a b x (y - x) c8 c9, []⟩,
          [.br 1], 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048544 oldShift ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        loopDecreaseYProg, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy, Hshift⟩
  rw [show loopDecreaseYProg =
    [.localGet 2, .load64 8, .localSet 6,
      .localGet 2, .localGet 2, .load64 16, .localGet 6, .subI64, .store64 16,
      .localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 32,
      .localGet 2, .load32 32, .localSet 7,
      .localGet 2, .localGet 2, .load64 16, .localGet 7, .const 63, .and,
      .extendUI32, .shrUI64, .store64 16, .br 1] from rfl]
  simp only [func1LoopHeaderLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) x $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) x =
          pointsTo_u64 1048520 x :=
      congrArg (fun address => pointsTo_u64 address x) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 x
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) y $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) y =
          pointsTo_u64 1048528 y :=
      congrArg (fun address => pointsTo_u64 address y) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 y
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_subI64
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) y $$ [Hy]
  · inext
    iexact Hy
  iapply Wasm.SmallStep.wp_store64 y
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  rw [show
    [.localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 32,
      .localGet 2, .load32 32, .localSet 7,
      .localGet 2, .localGet 2, .load64 16, .localGet 7, .const 63, .and,
      .extendUI32, .shrUI64, .store64 16, .br 1] =
      loopNormalizeYProg from rfl]
  rw [show
    [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
      .i32 (operandShiftWord b), .i64 x, .i32 c7, .i64 c8, .i32 c9] =
      func1LoopYLocals a b x c8 c7 c9 from rfl]
  ihave HxExact : pointsTo_u64 1048520 x $$ [Hx]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) x =
          pointsTo_u64 1048520 x :=
      congrArg (fun address => pointsTo_u64 address x) (by decide)
    rw [← h]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 (y - x) $$ [Hy]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) (y - x) =
          pointsTo_u64 1048528 (y - x) :=
      congrArg (fun address => pointsTo_u64 address (y - x)) (by decide)
    rw [← h]
    iexact Hy
  iapply func1_loopNormalizeY_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048520 x))
    controls calls a b x (y - x) hsub oldShift c8 c7 c9
  · iintro Hresources
    icases Hresources with ⟨⟨HR', Hx'⟩, Hy', Hshift'⟩
    iapply hcontinue
    iframe
  · iframe

def loopNormalizeXProg : Program :=
  [.localGet 2, .localGet 2, .load64 8, .ctzI64, .wrapI64, .store32 28,
    .localGet 2, .load32 28, .localSet 9,
    .localGet 2, .localGet 2, .load64 8, .localGet 9, .const 63, .and,
    .extendUI32, .shrUI64, .store64 8, .br 0]

def func1LoopXLocals
    (a b y c6 : UInt64) (c7 c9 : UInt32) : List Value :=
  [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
    .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 y, .i32 c9]

def func1LoopXNormalizedLocals
    (a b y d c6 : UInt64) (c7 : UInt32) : List Value :=
  [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
    .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 y,
    .i32 (operandShiftWord d)]

/-- Normalize the newly subtracted left operand in the generated
`x := oddPart (x - y)` arm. The exact `fp+28` scratch word is kept distinct
from the right-arm scratch word at `fp+32`. -/
theorem func1_loopNormalizeX_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b y d : UInt64) (hd : d ≠ 0) (oldShift : UInt32)
    (c6 : UInt64) (c7 c9 : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 (oddPart64 d) ∗
        pointsTo_u32 1048540 (operandShiftWord d) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopXNormalizedLocals a b y d c6 c7, []⟩,
          [.br 0], 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 d ∗ pointsTo_u32 1048540 oldShift ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopXLocals a b y c6 c7 c9, []⟩,
        loopNormalizeXProg, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hshift⟩
  simp only [loopNormalizeXProg, func1LoopXLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) d $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) d =
          pointsTo_u64 1048520 d :=
      congrArg (fun address => pointsTo_u64 address d) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 d
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_ctzI64
  inext
  iapply Wasm.SmallStep.wp_wrapI64
  inext
  ihave HshiftLater :
      ▷ pointsTo_u32 (1048512 + 28) oldShift $$ [Hshift]
  · inext
    have h :
        pointsTo_u32 ((1048512 : UInt32) + 28) oldShift =
          pointsTo_u32 1048540 oldShift :=
      congrArg (fun address => pointsTo_u32 address oldShift) (by decide)
    rw [h]
    iexact Hshift
  iapply Wasm.SmallStep.wp_store32 oldShift
      (by decide) (by decide) (by decide) (by decide) $$ HshiftLater
  inext
  iintro Hshift
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HshiftLater :
      ▷ pointsTo_u32 (1048512 + 28) (operandShiftWord d) $$ [Hshift]
  · inext
    rw [operandShiftWord]
    iexact Hshift
  iapply Wasm.SmallStep.wp_load32 (operandShiftWord d)
      (by decide) (by decide) (by decide) (by decide) $$ HshiftLater
  inext
  iintro Hshift
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) d $$ [Hx]
  · inext
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 d
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  iapply Wasm.SmallStep.wp_extendUI32
  inext
  iapply Wasm.SmallStep.wp_shrUI64
  inext
  rw [UInt32.and_comm (operandShiftWord d) 63]
  unfold operandShiftWord
  rw [shift_pipeline d hd]
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) d $$ [Hx]
  · inext
    iexact Hx
  iapply Wasm.SmallStep.wp_store64 d
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  simp only [func1LoopXNormalizedLocals, operandShiftWord, oddPart64] at hcontinue
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8)
          (d >>> (UInt64.ofNat (ctz64 64 d) % 64)) =
        pointsTo_u64 1048520
          (d >>> (UInt64.ofNat (ctz64 64 d) % 64)) :=
    congrArg
      (fun address =>
        pointsTo_u64 address (d >>> (UInt64.ofNat (ctz64 64 d) % 64)))
      (by decide)
  have hShiftProp :
      pointsTo_u32 ((1048512 : UInt32) + 28)
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)) =
        pointsTo_u32 1048540
          (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)) :=
    congrArg
      (fun address => pointsTo_u32 address
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)))
      (by decide)
  ihave HxExact :
      pointsTo_u64 1048520
        (d >>> (UInt64.ofNat (ctz64 64 d) % 64)) $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HshiftExact :
      pointsTo_u32 1048540
        (UInt32.ofNat ((UInt64.ofNat (ctz64 64 d)).toNat % 2 ^ 32)) $$
        [Hshift]
  · rw [← hShiftProp]
    iexact Hshift
  iapply hcontinue
  iframe

def loopDecreaseXProg : Program :=
  [.localGet 2, .load64 16, .localSet 8,
    .localGet 2, .localGet 2, .load64 8, .localGet 8, .subI64, .store64 8] ++
    loopNormalizeXProg

/-- Complete generated left-decreasing arm before administrative branch
handling. It computes `x - y` through the physical frame and then normalizes
that result through the dedicated `fp+28` scratch word. -/
theorem func1_loopDecreaseX_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b x y : UInt64) (hsub : x - y ≠ 0)
    (oldShift : UInt32)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 (oddPart64 (x - y)) ∗
        pointsTo_u64 1048528 y ∗
        pointsTo_u32 1048540 (operandShiftWord (x - y)) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopXNormalizedLocals a b y (x - y) c6 c7, []⟩,
          [.br 0], 1, [], controls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048540 oldShift ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        loopDecreaseXProg, 1, [], controls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy, Hshift⟩
  rw [show loopDecreaseXProg =
    [.localGet 2, .load64 16, .localSet 8,
      .localGet 2, .localGet 2, .load64 8, .localGet 8, .subI64, .store64 8,
      .localGet 2, .localGet 2, .load64 8, .ctzI64, .wrapI64, .store32 28,
      .localGet 2, .load32 28, .localSet 9,
      .localGet 2, .localGet 2, .load64 8, .localGet 9, .const 63, .and,
      .extendUI32, .shrUI64, .store64 8, .br 0] from rfl]
  simp only [func1LoopHeaderLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) y $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) y =
          pointsTo_u64 1048528 y :=
      congrArg (fun address => pointsTo_u64 address y) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 y
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) x $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) x =
          pointsTo_u64 1048520 x :=
      congrArg (fun address => pointsTo_u64 address x) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 x
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_subI64
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) x $$ [Hx]
  · inext
    iexact Hx
  iapply Wasm.SmallStep.wp_store64 x
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  rw [show
    [.localGet 2, .localGet 2, .load64 8, .ctzI64, .wrapI64, .store32 28,
      .localGet 2, .load32 28, .localSet 9,
      .localGet 2, .localGet 2, .load64 8, .localGet 9, .const 63, .and,
      .extendUI32, .shrUI64, .store64 8, .br 0] =
      loopNormalizeXProg from rfl]
  rw [show
    [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
      .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 y, .i32 c9] =
      func1LoopXLocals a b y c6 c7 c9 from rfl]
  ihave HxExact : pointsTo_u64 1048520 (x - y) $$ [Hx]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) (x - y) =
          pointsTo_u64 1048520 (x - y) :=
      congrArg (fun address => pointsTo_u64 address (x - y)) (by decide)
    rw [← h]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 y $$ [Hy]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) y =
          pointsTo_u64 1048528 y :=
      congrArg (fun address => pointsTo_u64 address y) (by decide)
    rw [← h]
    iexact Hy
  iapply func1_loopNormalizeX_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048528 y))
    controls calls a b y (x - y) hsub oldShift c6 c7 c9
  · iintro Hresources
    icases Hresources with ⟨⟨HR', Hy'⟩, Hx', Hshift'⟩
    iapply hcontinue
    iframe
  · iframe

def loopDecreaseYBlockBody : Program :=
  [.localGet 2, .load64 8, .localGet 2, .load64 16, .gtUI64, .const 1, .and,
    .br_if 0] ++ loopDecreaseYProg

def func1LoopBody : Program :=
  [.block 0 0 equalityBlockBody, .block 0 0 loopDecreaseYBlockBody] ++
    loopDecreaseXProg

def func1LoopFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := func1LoopBody
    continuation := []
    belowStack := [] }

def func1DecreaseYFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := loopDecreaseYBlockBody
    continuation := loopDecreaseXProg
    belowStack := [] }

def func1AfterEqualityProg : Program :=
  [.block 0 0 loopDecreaseYBlockBody] ++ loopDecreaseXProg

def func1EqualityFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := equalityBlockBody
    continuation := func1AfterEqualityProg
    belowStack := [] }

/-- Dispatch for the first generated loop block. Equality falls through to
the recombination tail; inequality takes the block branch into the comparison
block's concrete continuation. -/
theorem func1_loopEqualityDispatch_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b x y oldResult : UInt64)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hfinish : ∀ (_ : x = y),
      R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 x ∗
        pointsTo_u64 1048512 (recombinedWord a b x) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
          [.br 2], 1, [],
          func1EqualityFrame :: func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }})
    (hnext : ∀ (_ : x ≠ y),
      R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
        pointsTo_u64 1048512 oldResult ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
          func1AfterEqualityProg, 1, [],
          func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u64 1048512 oldResult ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        equalityBlockBody, 1, [],
        func1EqualityFrame :: func1LoopFrame :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  by_cases hxy : x = y
  · subst y
    iapply func1_equalBlock_smallStep_wp R
      (func1EqualityFrame :: func1LoopFrame :: outerControls)
      calls a b x oldResult c6 c8 c7 c9 (hfinish rfl)
  · iintro ⟨HR, Hx, Hy, Hresult⟩
    rw [show equalityBlockBody =
      [.localGet 2, .load64 8, .localGet 2, .load64 16, .neI64, .const 1, .and,
        .br_if 0, .localGet 2, .localGet 2, .load64 8, .localGet 3, .const 63,
        .and, .extendUI32, .shlI64, .store64 0, .br 2] from rfl]
    simp only [func1LoopHeaderLocals]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) x $$ [Hx]
    · inext
      have h :
          pointsTo_u64 ((1048512 : UInt32) + 8) x =
            pointsTo_u64 1048520 x :=
        congrArg (fun address => pointsTo_u64 address x) (by decide)
      rw [h]
      iexact Hx
    iapply Wasm.SmallStep.wp_load64 x
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$ HxLater
    inext
    iintro Hx
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) y $$ [Hy]
    · inext
      have h :
          pointsTo_u64 ((1048512 : UInt32) + 16) y =
            pointsTo_u64 1048528 y :=
        congrArg (fun address => pointsTo_u64 address y) (by decide)
      rw [h]
      iexact Hy
    iapply Wasm.SmallStep.wp_load64 y
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$ HyLater
    inext
    iintro Hy
    iapply Wasm.SmallStep.wp_neI64 (result := 1) (by simp [hxy])
    inext
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_and
    inext
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply Wasm.SmallStep.wp_brIf (by decide) rfl
    inext
    simp only [func1EqualityFrame, List.take_nil, List.nil_append]
    rw [show
      [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
        .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 c8, .i32 c9] =
        func1LoopHeaderLocals a b c6 c8 c7 c9 from rfl]
    ihave HxExact : pointsTo_u64 1048520 x $$ [Hx]
    · have h :
          pointsTo_u64 ((1048512 : UInt32) + 8) x =
            pointsTo_u64 1048520 x :=
        congrArg (fun address => pointsTo_u64 address x) (by decide)
      rw [← h]
      iexact Hx
    ihave HyExact : pointsTo_u64 1048528 y $$ [Hy]
    · have h :
          pointsTo_u64 ((1048512 : UInt32) + 16) y =
            pointsTo_u64 1048528 y :=
        congrArg (fun address => pointsTo_u64 address y) (by decide)
      rw [← h]
      iexact Hy
    iapply hnext hxy
    iframe

/-- Comparison dispatch for the second generated loop block. A true
`x > y` exits the block into the left-decreasing arm; otherwise execution
falls through to the right-decreasing arm. Both paths retain the real loop
frame so their final branch is an actual back-edge. -/
theorem func1_loopDecreaseDispatch_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b x y : UInt64)
    (hxy : x ≠ y)
    (oldShiftX oldShiftY : UInt32)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hcontinueX : ∀ (_ : y < x),
      R ∗ pointsTo_u64 1048520 (oddPart64 (x - y)) ∗
        pointsTo_u64 1048528 y ∗
        pointsTo_u32 1048540 (operandShiftWord (x - y)) ∗
        pointsTo_u32 1048544 oldShiftY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopXNormalizedLocals a b y (x - y) c6 c7, []⟩,
          [.br 0], 1, [],
          func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }})
    (hcontinueY : ∀ (_ : ¬ y < x),
      R ∗ pointsTo_u64 1048520 x ∗
        pointsTo_u64 1048528 (oddPart64 (y - x)) ∗
        pointsTo_u32 1048540 oldShiftX ∗
        pointsTo_u32 1048544 (operandShiftWord (y - x)) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopYNormalizedLocals a b x (y - x) c8 c9, []⟩,
          [.br 1], 1, [],
          func1DecreaseYFrame :: func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048540 oldShiftX ∗ pointsTo_u32 1048544 oldShiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        loopDecreaseYBlockBody, 1, [],
        func1DecreaseYFrame :: func1LoopFrame :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy, HshiftX, HshiftY⟩
  rw [show loopDecreaseYBlockBody =
    [.localGet 2, .load64 8, .localGet 2, .load64 16, .gtUI64, .const 1, .and,
      .br_if 0,
      .localGet 2, .load64 8, .localSet 6,
      .localGet 2, .localGet 2, .load64 16, .localGet 6, .subI64, .store64 16,
      .localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 32,
      .localGet 2, .load32 32, .localSet 7,
      .localGet 2, .localGet 2, .load64 16, .localGet 7, .const 63, .and,
      .extendUI32, .shrUI64, .store64 16, .br 1] from rfl]
  simp only [func1LoopHeaderLocals]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) x $$ [Hx]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) x =
          pointsTo_u64 1048520 x :=
      congrArg (fun address => pointsTo_u64 address x) (by decide)
    rw [h]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 x
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) y $$ [Hy]
  · inext
    have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) y =
          pointsTo_u64 1048528 y :=
      congrArg (fun address => pointsTo_u64 address y) (by decide)
    rw [h]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 y
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  ihave HxExact : pointsTo_u64 1048520 x $$ [Hx]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 8) x =
          pointsTo_u64 1048520 x :=
      congrArg (fun address => pointsTo_u64 address x) (by decide)
    rw [← h]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 y $$ [Hy]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 16) y =
          pointsTo_u64 1048528 y :=
      congrArg (fun address => pointsTo_u64 address y) (by decide)
    rw [← h]
    iexact Hy
  by_cases hlt : y < x
  · have hsubX : x - y ≠ 0 := by
      intro h
      have hle : y ≤ x :=
        UInt64.le_iff_toNat_le.mpr
          (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt))
      have hto := UInt64.toNat_sub_of_le x y hle
      have hz : (x - y).toNat = 0 := by rw [h]; rfl
      rw [hto] at hz
      have hnat := UInt64.lt_iff_toNat_lt.mp hlt
      omega
    iapply Wasm.SmallStep.wp_gtUI64 (result := 1) (by simp [hlt])
    inext
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_and
    inext
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply Wasm.SmallStep.wp_brIf (by decide) rfl
    inext
    simp only [func1DecreaseYFrame, List.take_nil, List.nil_append]
    rw [show
      [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
        .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 c8, .i32 c9] =
        func1LoopHeaderLocals a b c6 c8 c7 c9 from rfl]
    iapply func1_loopDecreaseX_smallStep_wp
      (R := iprop(R ∗ pointsTo_u32 1048544 oldShiftY))
      (func1LoopFrame :: outerControls) calls a b x y hsubX oldShiftX
      c6 c8 c7 c9
    · iintro Hresources
      icases Hresources with
        ⟨⟨HR', HshiftY'⟩, Hx', Hy', HshiftX'⟩
      iapply hcontinueX hlt
      iframe
    · iframe
  · have hxylt : x < y := by
      rw [UInt64.lt_iff_toNat_lt]
      have hnot : ¬ y.toNat < x.toNat :=
        fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      have hne : x.toNat ≠ y.toNat :=
        fun h => hxy (UInt64.toNat.inj h)
      omega
    have hsubY : y - x ≠ 0 := by
      intro h
      have hle : x ≤ y :=
        UInt64.le_iff_toNat_le.mpr
          (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hxylt))
      have hto := UInt64.toNat_sub_of_le y x hle
      have hz : (y - x).toNat = 0 := by rw [h]; rfl
      rw [hto] at hz
      have hnat := UInt64.lt_iff_toNat_lt.mp hxylt
      omega
    iapply Wasm.SmallStep.wp_gtUI64 (result := 0) (by simp [hlt])
    inext
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_and
    inext
    rw [show (0 : UInt32) &&& 1 = 0 by decide]
    iapply Wasm.SmallStep.wp_brIfZero
    inext
    rw [show
      [.localGet 2, .load64 8, .localSet 6,
        .localGet 2, .localGet 2, .load64 16, .localGet 6, .subI64, .store64 16,
        .localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 32,
        .localGet 2, .load32 32, .localSet 7,
        .localGet 2, .localGet 2, .load64 16, .localGet 7, .const 63, .and,
        .extendUI32, .shrUI64, .store64 16, .br 1] =
        loopDecreaseYProg from rfl]
    rw [show
      [.i32 1048512, .i32 (sharedShiftWord a b), .i32 (operandShiftWord a),
        .i32 (operandShiftWord b), .i64 c6, .i32 c7, .i64 c8, .i32 c9] =
        func1LoopHeaderLocals a b c6 c8 c7 c9 from rfl]
    iapply func1_loopDecreaseY_smallStep_wp
      (R := iprop(R ∗ pointsTo_u32 1048540 oldShiftX))
      (func1DecreaseYFrame :: func1LoopFrame :: outerControls)
      calls a b x y hsubY oldShiftY c6 c8 c7 c9
    · iintro Hresources
      icases Hresources with
        ⟨⟨HR', HshiftX'⟩, Hx', Hy', HshiftY'⟩
      iapply hcontinueY hlt
      iframe
    · iframe

/-- One complete generated loop-body iteration, with structured-control
administration exposed only at its three semantic exits: final `br 2`, the
left-arm loop back-edge, and the right-arm loop back-edge. -/
theorem func1_loopBodyDispatch_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (K : IProp WasmHeapGF)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b x y oldResult : UInt64)
    (oldShiftX oldShiftY : UInt32)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hfinish : ∀ (_ : x = y),
      □ K ∗ R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 x ∗
        pointsTo_u64 1048512 (recombinedWord a b x) ∗
        pointsTo_u32 1048540 oldShiftX ∗ pointsTo_u32 1048544 oldShiftY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
          [.br 2], 1, [],
          func1EqualityFrame :: func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }})
    (hbackX : ∀ (_ : x ≠ y) (_ : y < x),
      □ K ∗ R ∗ pointsTo_u64 1048520 (oddPart64 (x - y)) ∗
        pointsTo_u64 1048528 y ∗ pointsTo_u64 1048512 oldResult ∗
        pointsTo_u32 1048540 (operandShiftWord (x - y)) ∗
        pointsTo_u32 1048544 oldShiftY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopXNormalizedLocals a b y (x - y) c6 c7, []⟩,
          [.br 0], 1, [], func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }})
    (hbackY : ∀ (_ : x ≠ y) (_ : ¬ y < x),
      □ K ∗ R ∗ pointsTo_u64 1048520 x ∗
        pointsTo_u64 1048528 (oddPart64 (y - x)) ∗
        pointsTo_u64 1048512 oldResult ∗ pointsTo_u32 1048540 oldShiftX ∗
        pointsTo_u32 1048544 (operandShiftWord (y - x)) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopYNormalizedLocals a b x (y - x) c8 c9, []⟩,
          [.br 1], 1, [],
          func1DecreaseYFrame :: func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    □ K ∗ R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u64 1048512 oldResult ∗ pointsTo_u32 1048540 oldShiftX ∗
      pointsTo_u32 1048544 oldShiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        func1LoopBody, 1, [], func1LoopFrame :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HK, HR, Hx, Hy, Hresult, HshiftX, HshiftY⟩
  rw [show func1LoopBody =
    .block 0 0 equalityBlockBody :: func1AfterEqualityProg from rfl]
  iapply Wasm.SmallStep.wp_block
  inext
  simp only [List.drop_zero]
  rw [show
    ({ kind := .block
       paramArity := 0
       resultArity := 0
       body := equalityBlockBody
       continuation := func1AfterEqualityProg
       belowStack := [] } : Wasm.SmallStep.ControlFrame) =
      func1EqualityFrame from rfl]
  iapply func1_loopEqualityDispatch_smallStep_wp
    (R := iprop(□ K ∗ R ∗ pointsTo_u32 1048540 oldShiftX ∗
      pointsTo_u32 1048544 oldShiftY))
    outerControls calls a b x y oldResult
    c6 c8 c7 c9
  · intro hxy
    iintro Hresources
    icases Hresources with
      ⟨⟨HK', HR', HshiftX', HshiftY'⟩, Hx', Hy', Hresult'⟩
    iapply hfinish hxy
    iframe
  · intro hxy
    iintro Hresources
    icases Hresources with
      ⟨⟨HK', HR', HshiftX', HshiftY'⟩, Hx', Hy', Hresult'⟩
    rw [show func1AfterEqualityProg =
      .block 0 0 loopDecreaseYBlockBody :: loopDecreaseXProg from rfl]
    iapply Wasm.SmallStep.wp_block
    inext
    simp only [List.drop_zero]
    rw [show
      ({ kind := .block
         paramArity := 0
         resultArity := 0
         body := loopDecreaseYBlockBody
         continuation := loopDecreaseXProg
         belowStack := [] } : Wasm.SmallStep.ControlFrame) =
        func1DecreaseYFrame from rfl]
    iapply func1_loopDecreaseDispatch_smallStep_wp
      (R := iprop(□ K ∗ R ∗ pointsTo_u64 1048512 oldResult))
      outerControls calls a b x y hxy oldShiftX oldShiftY
      c6 c8 c7 c9
    · intro hlt
      iintro Hresources
      icases Hresources with
        ⟨⟨HK'', HR'', Hresult''⟩, Hx'', Hy'', HshiftX'', HshiftY''⟩
      iapply hbackX hxy hlt
      iframe
    · intro hlt
      iintro Hresources
      icases Hresources with
        ⟨⟨HK'', HR'', Hresult''⟩, Hx'', Hy'', HshiftX'', HshiftY''⟩
      iapply hbackY hxy hlt
      iframe
    · iframe
  · iframe

/-- Partial-correctness invariant for the memory-backed Stein loop. Unlike the
legacy total proof, Iris Löb induction only needs preservation of nonzeroness,
oddness, and mathematical GCD at the two real loop back-edges. -/
theorem func1_loop_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b x y expected oldResult : UInt64)
    (oldShiftX oldShiftY : UInt32)
    (c6 c8 : UInt64) (c7 c9 : UInt32)
    (hxne : x ≠ 0) (hyne : y ≠ 0)
    (hxodd : x.toNat % 2 = 1) (hyodd : y.toNat % 2 = 1)
    (hgcd :
      Nat.gcd x.toNat y.toNat =
        Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat)
    (hrecombine : ∀ g : UInt64,
      g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat →
      recombinedWord a b g = expected)
    (hfinish : ∀ (g : UInt64) (shiftX shiftY : UInt32)
        (d6 d8 : UInt64) (d7 d9 : UInt32),
      g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat →
      R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
        pointsTo_u64 1048512 expected ∗ pointsTo_u32 1048540 shiftX ∗
        pointsTo_u32 1048544 shiftY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b d6 d8 d7 d9, []⟩,
          [.br 2], 1, [],
          func1EqualityFrame :: func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u64 1048512 oldResult ∗ pointsTo_u32 1048540 oldShiftX ∗
      pointsTo_u32 1048544 oldShiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
        func1LoopBody, 1, [], func1LoopFrame :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iloeb as IH generalizing
    %x %y %oldResult %oldShiftX %oldShiftY %c6 %c8 %c7 %c9
    %hxne %hyne %hxodd %hyodd %hgcd
  let Kloop : IProp WasmHeapGF := iprop(
    ▷ ∀ (x y oldResult : UInt64)
        (oldShiftX oldShiftY : UInt32)
        (c6 c8 : UInt64) (c7 c9 : UInt32),
      ⌜x ≠ 0⌝ -∗ ⌜y ≠ 0⌝ -∗
      ⌜x.toNat % 2 = 1⌝ -∗ ⌜y.toNat % 2 = 1⌝ -∗
      ⌜Nat.gcd x.toNat y.toNat =
        Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat⌝ -∗
      R ∗ pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
        pointsTo_u64 1048512 oldResult ∗
        pointsTo_u32 1048540 oldShiftX ∗ pointsTo_u32 1048544 oldShiftY -∗
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b c6 c8 c7 c9, []⟩,
          func1LoopBody, 1, [], func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }})
  ihave IHtyped : □ Kloop $$ [IH]
  · simp only [Kloop]
    iexact IH
  iintro ⟨HR, Hx, Hy, Hresult, HshiftX, HshiftY⟩
  by_cases hxy : x = y
  · iapply func1_loopBodyDispatch_smallStep_wp R Kloop outerControls calls
      a b x y oldResult oldShiftX oldShiftY c6 c8 c7 c9
    · intro _
      have hxGcd :
          x.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat := by
        rw [← hgcd, hxy, Nat.gcd_self]
      have hresultEq := hrecombine x hxGcd
      iintro Hresources
      icases Hresources with
        ⟨#IH', HR', Hx', Hy', Hresult', HshiftX', HshiftY'⟩
      ihave HresultExpected : pointsTo_u64 1048512 expected $$ [Hresult']
      · rw [← hresultEq]
        iexact Hresult'
      iapply hfinish x oldShiftX oldShiftY c6 c8 c7 c9 hxGcd
      iframe
    · intro hne
      exact (hne hxy).elim
    · intro hne
      exact (hne hxy).elim
    · iframe
  · by_cases hlt : y < x
    · iapply func1_loopBodyDispatch_smallStep_wp R Kloop outerControls calls
        a b x y oldResult oldShiftX oldShiftY c6 c8 c7 c9
      · intro heq
        exact (hxy heq).elim
      · intro _ _
        let x' := oddPart64 (x - y)
        obtain ⟨hx'ne, hx'odd, hgcd', _hdec⟩ :=
          UInt64.stein_step_x x y hxne hyne hxodd hyodd hlt
        iintro Hresources
        icases Hresources with
          ⟨#IH', HR', Hx', Hy', Hresult', HshiftX', HshiftY'⟩
        iapply Wasm.SmallStep.wp_br rfl
        inext
        simp only [func1LoopFrame, List.take_nil, List.nil_append]
        rw [show
          func1LoopXNormalizedLocals a b y (x - y) c6 c7 =
            func1LoopHeaderLocals a b c6 y c7
              (operandShiftWord (x - y)) from rfl]
        ispecialize IH' $$ %
          (oddPart64 (x - y)) %y %oldResult
          %(operandShiftWord (x - y)) %oldShiftY %c6 %y %c7
          %(operandShiftWord (x - y))
          %hx'ne %hyne
          %(by simpa [x', oddPart_toNat, oddPart64] using hx'odd)
          %hyodd
          %(by simpa [x', oddPart_toNat, oddPart64] using hgcd'.trans hgcd)
        iapply IH'
        iframe
      · intro _ hnlt
        exact (hnlt hlt).elim
      · iframe
    · iapply func1_loopBodyDispatch_smallStep_wp R Kloop outerControls calls
        a b x y oldResult oldShiftX oldShiftY c6 c8 c7 c9
      · intro heq
        exact (hxy heq).elim
      · intro _ hlt'
        exact (hlt hlt').elim
      · intro _ _
        let y' := oddPart64 (y - x)
        obtain ⟨hy'ne, hy'odd, hgcd', _hdec⟩ :=
          UInt64.stein_step_y x y hxne hyne hxodd hyodd hlt hxy
        iintro Hresources
        icases Hresources with
          ⟨#IH', HR', Hx', Hy', Hresult', HshiftX', HshiftY'⟩
        iapply Wasm.SmallStep.wp_br rfl
        inext
        simp only [func1LoopFrame, List.take_nil, List.nil_append]
        rw [show
          func1LoopYNormalizedLocals a b x (y - x) c8 c9 =
            func1LoopHeaderLocals a b x c8
              (operandShiftWord (y - x)) c9 from rfl]
        ispecialize IH' $$ %x %
          (oddPart64 (y - x)) %oldResult
          %oldShiftX %(operandShiftWord (y - x)) %x %c8
          %(operandShiftWord (y - x)) %c9
          %hxne %hy'ne %hxodd
          %(by simpa [y', oddPart_toNat, oddPart64] using hy'odd)
          %(by simpa [y', oddPart_toNat, oddPart64] using hgcd'.trans hgcd)
        iapply IH'
        iframe
      · iframe

def func1LoopEntryProg : Program :=
  [.loop 0 0 func1LoopBody]

/-- Enter the generated loop after nonzero normalization. The loop starts
with the two odd parts and returns the GCD of the original operands through
its `br 2` exit. -/
theorem func1_loopEntry_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b oldResult : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (oldShiftX oldShiftY : UInt32)
    (hfinish : ∀ (g : UInt64) (shiftX shiftY : UInt32)
        (d6 d8 : UInt64) (d7 d9 : UInt32),
      g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat →
      R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
        pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
        pointsTo_u32 1048540 shiftX ∗ pointsTo_u32 1048544 shiftY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b d6 d8 d7 d9, []⟩,
          [.br 2], 1, [],
          func1EqualityFrame :: func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 (oddPart64 a) ∗
      pointsTo_u64 1048528 (oddPart64 b) ∗
      pointsTo_u64 1048512 oldResult ∗ pointsTo_u32 1048540 oldShiftX ∗
      pointsTo_u32 1048544 oldShiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1NormalizedLocals a b, []⟩,
        func1LoopEntryProg, 1, [], outerControls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  have hxne : oddPart64 a ≠ 0 := by
    exact UInt64.shr_ctz_ne_zero a ha
  have hyne : oddPart64 b ≠ 0 := by
    exact UInt64.shr_ctz_ne_zero b hb
  have hxodd : (oddPart64 a).toNat % 2 = 1 := by
    simpa [oddPart64, oddPart_toNat] using
      UInt64.shr_ctz_toNat_odd a ha
  have hyodd : (oddPart64 b).toNat % 2 = 1 := by
    simpa [oddPart64, oddPart_toNat] using
      UInt64.shr_ctz_toNat_odd b hb
  iintro ⟨HR, Hx, Hy, Hresult, HshiftX, HshiftY⟩
  simp only [func1LoopEntryProg]
  iapply Wasm.SmallStep.wp_loop
  inext
  simp only [List.drop_zero]
  rw [show
    ({ kind := .loop
       paramArity := 0
       resultArity := 0
       body := func1LoopBody
       continuation := []
       belowStack := [] } : Wasm.SmallStep.ControlFrame) =
      func1LoopFrame from rfl]
  rw [show func1NormalizedLocals a b =
    func1LoopHeaderLocals a b 0 0 0 0 from rfl]
  iapply func1_loop_smallStep_wp R outerControls calls
    a b (oddPart64 a) (oddPart64 b)
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) oldResult
    oldShiftX oldShiftY 0 0 0 0
    hxne hyne hxodd hyodd rfl
    (fun g hg => recombinedWord_eq_gcd a b g ha hb hg)
    hfinish
  iframe

/-- Complete nonzero generated core: normalize both operands through the
physical scratch frame, enter the real loop, and expose only the final
`br 2` control transfer. -/
theorem func1_nonzeroCore_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b oldResult : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (oldShared oldNormX oldNormY oldLoopX oldLoopY : UInt32)
    (hfinish : ∀ (g : UInt64) (loopX loopY : UInt32)
        (d6 d8 : UInt64) (d7 d9 : UInt32),
      g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat →
      R ∗ pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ∗
        pointsTo_u32 1048548 (operandShiftWord b) ∗
        pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
        pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
        pointsTo_u32 1048540 loopX ∗ pointsTo_u32 1048544 loopY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b d6 d8 d7 d9, []⟩,
          [.br 2], 1, [],
          func1EqualityFrame :: func1LoopFrame :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ∗
      pointsTo_u64 1048512 oldResult ∗ pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldNormX ∗ pointsTo_u32 1048548 oldNormY ∗
      pointsTo_u32 1048540 oldLoopX ∗ pointsTo_u32 1048544 oldLoopY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        meatLoopProg, 1, [], outerControls, calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro
    ⟨HR, Hx, Hy, Hresult, Hshared, HnormX, HnormY, HloopX, HloopY⟩
  iapply func1_normalization_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048512 oldResult ∗
      pointsTo_u32 1048540 oldLoopX ∗ pointsTo_u32 1048544 oldLoopY))
    outerControls calls a b ha hb oldShared oldNormX oldNormY
  · iintro Hresources
    icases Hresources with
      ⟨⟨HR', Hresult', HloopX', HloopY'⟩, Hx', Hy',
        Hshared', HnormX', HnormY'⟩
    rw [show meatLoopProg.drop 48 = func1LoopEntryProg from rfl]
    iapply func1_loopEntry_smallStep_wp
      (R := iprop(R ∗ pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ∗
        pointsTo_u32 1048548 (operandShiftWord b)))
      outerControls calls a b oldResult ha hb oldLoopX oldLoopY
    · intro g loopX loopY d6 d8 d7 d9 hg
      iintro Hresources
      icases Hresources with
        ⟨⟨HR'', Hshared'', HnormX'', HnormY''⟩,
          Hx'', Hy'', Hresult'', HloopX'', HloopY''⟩
      iapply hfinish g loopX loopY d6 d8 d7 d9 hg
      iframe
    · iframe
  · iframe

def func1EpilogueProg : Program :=
  [.localGet 2, .load64 0, .ret]

def func1InnerGuardProg : Program :=
  [.localGet 2, .load64 8, .constI64 0, .eqI64, .const 1, .and, .br_if 0,
    .localGet 2, .load64 16, .constI64 0, .eqI64, .const 1, .and, .eqz,
    .br_if 1]

def func1ZeroJoinProg : Program :=
  [.localGet 2, .localGet 2, .load64 8, .localGet 2, .load64 16, .orI64,
    .store64 0, .br 1]

def func1MiddleBody : Program :=
  .block 0 0 func1InnerGuardProg :: func1ZeroJoinProg

def func1OuterBody : Program :=
  .block 0 0 func1MiddleBody :: meatLoopProg

def func1OuterFrame (body : Program) : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := body
    continuation := func1EpilogueProg
    belowStack := [] }

theorem func1_afterSpill_shape :
    func1.drop 12 =
      [.block 0 0 func1OuterBody] ++ func1EpilogueProg := by
  rfl

/-- With both operands nonzero, the generated nested guards leave their inner
and middle blocks and transfer control to `meatLoopProg` under the one
remaining outer frame. -/
theorem func1_nonzeroGuards_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcontinue :
      R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
          meatLoopProg, 1, [], [func1OuterFrame func1OuterBody], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        func1.drop 12, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy⟩
  rw [func1_afterSpill_shape]
  simp only [func1OuterBody, func1MiddleBody, func1InnerGuardProg,
    func1ZeroJoinProg, func1EpilogueProg, func1SpilledLocals,
    List.cons_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HxLater : ▷ pointsTo_u64 (1048512 + 8) a $$ [Hx]
  · inext
    rw [show (1048512 : UInt32) + 8 = 1048520 from rfl]
    iexact Hx
  iapply Wasm.SmallStep.wp_load64 a
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HxLater
  inext
  iintro Hx
  iapply Wasm.SmallStep.wp_constI64
  inext
  iapply Wasm.SmallStep.wp_eqI64 (result := 0) (by simp [ha])
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  rw [show (0 &&& 1 : UInt32) = 0 by decide]
  iapply Wasm.SmallStep.wp_brIfZero
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HyLater : ▷ pointsTo_u64 (1048512 + 16) b $$ [Hy]
  · inext
    rw [show (1048512 : UInt32) + 16 = 1048528 from rfl]
    iexact Hy
  iapply Wasm.SmallStep.wp_load64 b
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HyLater
  inext
  iintro Hy
  iapply Wasm.SmallStep.wp_constI64
  inext
  iapply Wasm.SmallStep.wp_eqI64 (result := 0) (by simp [hb])
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  rw [show (0 &&& 1 : UInt32) = 0 by decide]
  iapply Wasm.SmallStep.wp_eqz (result := 1) (by decide)
  inext
  iapply Wasm.SmallStep.wp_brIf (by decide) rfl
  inext
  simp only [List.take_nil, List.nil_append]
  have hXProp :
      pointsTo_u64 ((1048512 : UInt32) + 8) a =
        pointsTo_u64 1048520 a :=
    congrArg (fun address => pointsTo_u64 address a) (by decide)
  have hYProp :
      pointsTo_u64 ((1048512 : UInt32) + 16) b =
        pointsTo_u64 1048528 b :=
    congrArg (fun address => pointsTo_u64 address b) (by decide)
  ihave HxExact : pointsTo_u64 1048520 a $$ [Hx]
  · rw [← hXProp]
    iexact Hx
  ihave HyExact : pointsTo_u64 1048528 b $$ [Hy]
  · rw [← hYProp]
    iexact Hy
  simp only [List.drop_nil]
  simp only [func1OuterFrame, func1OuterBody, func1MiddleBody,
    func1InnerGuardProg, func1ZeroJoinProg, func1EpilogueProg,
    func1SpilledLocals] at hcontinue
  iapply hcontinue
  iframe

/-- The equality exit from the Stein loop targets the generated outer block.
That branch exposes the epilogue, which reloads the result slot and returns it
from a top-level invocation of `func1`. -/
theorem func1_nonzeroFinish_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (outerBody : Program)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b g d6 d8 : UInt64) (shiftX shiftY d7 d9 : UInt32)
    (_hgcd : g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat)
    (hreturn :
      R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
        pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
        pointsTo_u32 1048540 shiftX ∗ pointsTo_u32 1048544 shiftY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b d6 d8 d7 d9,
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
      pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
      pointsTo_u32 1048540 shiftX ∗ pointsTo_u32 1048544 shiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b d6 d8 d7 d9, []⟩,
        [.br 2], 1, [],
        func1EqualityFrame :: func1LoopFrame :: [func1OuterFrame outerBody],
        calls⟩ : Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hx, Hy, Hresult, HshiftX, HshiftY⟩
  iapply Wasm.SmallStep.wp_br rfl
  inext
  simp only [func1OuterFrame, func1EpilogueProg, List.take_nil,
    List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HresultLater :
      ▷ pointsTo_u64 ((1048512 : UInt32) + 0)
        (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) $$ [Hresult]
  · inext
    rw [show (1048512 : UInt32) + 0 = 1048512 from rfl]
    iexact Hresult
  iapply Wasm.SmallStep.wp_load64
      (UInt64.ofNat (Nat.gcd a.toNat b.toNat))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HresultLater
  inext
  iintro Hresult
  ihave HresultExact :
      pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))
      $$ [Hresult]
  · have h :
        pointsTo_u64 ((1048512 : UInt32) + 0)
            (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) =
          pointsTo_u64 1048512
            (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) :=
      congrArg
        (fun address => pointsTo_u64 address
          (UInt64.ofNat (Nat.gcd a.toNat b.toNat))) (by decide)
    rw [← h]
    iexact Hresult
  iapply hreturn
  iframe

/-- Closed top-level corollary of the contextual nonzero finish rule. -/
theorem func1_nonzeroFinish_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (outerBody : Program)
    (a b g d6 d8 : UInt64) (shiftX shiftY d7 d9 : UInt32)
    (hgcd : g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat) :
    R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
      pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
      pointsTo_u32 1048540 shiftX ∗ pointsTo_u32 1048544 shiftY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568],
          func1LoopHeaderLocals a b d6 d8 d7 d9, []⟩,
        [.br 2], 1, [],
        func1EqualityFrame :: func1LoopFrame :: [func1OuterFrame outerBody],
        []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
          R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
          pointsTo_u64 1048512
            (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
          pointsTo_u32 1048540 shiftX ∗ pointsTo_u32 1048544 shiftY }} := by
  iintro Hresources
  iapply func1_nonzeroFinish_smallStep_wp_to_return
    R outerBody [] a b g d6 d8 shiftX shiftY d7 d9 hgcd
  · iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromFunction
    inext
    simp only [List.take]
    iapply wp_value'
    isplit
    · ipureintro
      rfl
    · iexact Hresources
  · iexact Hresources

/-- Contextual form of the complete nonzero core. Its final explicit return is
left to the caller, so the same proof can be used beneath a Wasm call frame. -/
theorem func1_nonzeroOuterCore_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (outerBody : Program)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b oldResult : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (oldShared oldNormX oldNormY oldLoopX oldLoopY : UInt32)
    (hreturn : ∀ (g : UInt64) (loopX loopY : UInt32)
        (d6 d8 : UInt64) (d7 d9 : UInt32),
      g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat →
      (R ∗ pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ∗
        pointsTo_u32 1048548 (operandShiftWord b)) ∗
        pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
        pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
        pointsTo_u32 1048540 loopX ∗ pointsTo_u32 1048544 loopY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b d6 d8 d7 d9,
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ∗
      pointsTo_u64 1048512 oldResult ∗ pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldNormX ∗ pointsTo_u32 1048548 oldNormY ∗
      pointsTo_u32 1048540 oldLoopX ∗ pointsTo_u32 1048544 oldLoopY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        meatLoopProg, 1, [], [func1OuterFrame outerBody], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro Hresources
  iapply func1_nonzeroCore_smallStep_wp
    R [func1OuterFrame outerBody] calls
    a b oldResult ha hb oldShared oldNormX oldNormY oldLoopX oldLoopY
  · intro g loopX loopY d6 d8 d7 d9 hg
    iintro Hresources
    icases Hresources with
      ⟨HR, Hshared, HnormX, HnormY, Hx, Hy, Hresult, HloopX, HloopY⟩
    iapply func1_nonzeroFinish_smallStep_wp_to_return
      (R := iprop(R ∗ pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ∗
        pointsTo_u32 1048548 (operandShiftWord b)))
      outerBody calls a b g d6 d8 loopX loopY d7 d9 hg
    · iintro Hresources
      iapply hreturn g loopX loopY d6 d8 d7 d9 hg
      iexact Hresources
    · iframe
  · iexact Hresources

/-- Run the complete nonzero Stein core underneath the generated outer block
and discharge its equality exit through `func1`'s epilogue. -/
theorem func1_nonzeroOuterCore_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (outerBody : Program)
    (a b oldResult : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (oldShared oldNormX oldNormY oldLoopX oldLoopY : UInt32) :
    R ∗ pointsTo_u64 1048520 a ∗ pointsTo_u64 1048528 b ∗
      pointsTo_u64 1048512 oldResult ∗ pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldNormX ∗ pointsTo_u32 1048548 oldNormY ∗
      pointsTo_u32 1048540 oldLoopX ∗ pointsTo_u32 1048544 oldLoopY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩,
        meatLoopProg, 1, [], [func1OuterFrame outerBody], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
          ∃ g : UInt64, ∃ loopX loopY : UInt32,
            ⌜g.toNat =
              Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat⌝ ∗
            R ∗ pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
            pointsTo_u64 1048512
              (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
            pointsTo_u32 1048556 (sharedShiftWord a b) ∗
            pointsTo_u32 1048552 (operandShiftWord a) ∗
            pointsTo_u32 1048548 (operandShiftWord b) ∗
            pointsTo_u32 1048540 loopX ∗
            pointsTo_u32 1048544 loopY }} := by
  iintro Hresources
  iapply func1_nonzeroCore_smallStep_wp R [func1OuterFrame outerBody] []
    a b oldResult ha hb oldShared oldNormX oldNormY oldLoopX oldLoopY
  · intro g loopX loopY d6 d8 d7 d9 hg
    iintro Hresources
    icases Hresources with
      ⟨HR, Hshared, HnormX, HnormY, Hx, Hy, Hresult, HloopX, HloopY⟩
    have hpost : ∀ rs : List Value,
        (iprop(
          ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
            (R ∗ pointsTo_u32 1048556 (sharedShiftWord a b) ∗
              pointsTo_u32 1048552 (operandShiftWord a) ∗
              pointsTo_u32 1048548 (operandShiftWord b)) ∗
            pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
            pointsTo_u64 1048512
              (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
            pointsTo_u32 1048540 loopX ∗ pointsTo_u32 1048544 loopY)) ⊢
        (iprop(
          ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
            ∃ g' : UInt64, ∃ loopX' loopY' : UInt32,
              ⌜g'.toNat =
                Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat⌝ ∗
              R ∗ pointsTo_u64 1048520 g' ∗ pointsTo_u64 1048528 g' ∗
              pointsTo_u64 1048512
                (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
              pointsTo_u32 1048556 (sharedShiftWord a b) ∗
              pointsTo_u32 1048552 (operandShiftWord a) ∗
              pointsTo_u32 1048548 (operandShiftWord b) ∗
              pointsTo_u32 1048540 loopX' ∗
              pointsTo_u32 1048544 loopY')) := by
      intro rs
      iintro ⟨%hrs, HR, Hx, Hy, Hresult, HloopX, HloopY⟩
      icases HR with ⟨HR, Hshared, HnormX, HnormY⟩
      isplit
      · ipureintro
        exact hrs
      · iexists g
        iexists loopX
        iexists loopY
        isplit
        · ipureintro
          exact hg
        · iframe
    iapply wp_mono hpost
    iapply func1_nonzeroFinish_smallStep_wp
      (R := iprop(R ∗ pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ∗
        pointsTo_u32 1048548 (operandShiftWord b)))
      outerBody a b g d6 d8 loopX loopY d7 d9 hg
    iframe
  · iexact Hresources

/-- Contextual end-to-end nonzero `func1` rule, stopping immediately before
the explicit return so a caller-provided call frame can resume. -/
theorem func1_nonzero_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (result oldX oldY a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (oldShared oldNormX oldNormY oldLoopX oldLoopY : UInt32)
    (hreturn : ∀ (g : UInt64) (loopX loopY : UInt32)
        (d6 d8 : UInt64) (d7 d9 : UInt32),
      g.toNat = Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat →
      ((R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b) ∗
        pointsTo_u32 1048556 (sharedShiftWord a b) ∗
        pointsTo_u32 1048552 (operandShiftWord a) ∗
        pointsTo_u32 1048548 (operandShiftWord b)) ∗
        pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
        pointsTo_u64 1048512 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
        pointsTo_u32 1048540 loopX ∗ pointsTo_u32 1048544 loopY ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048560, .i32 1048568],
            func1LoopHeaderLocals a b d6 d8 d7 d9,
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ∗
      pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldNormX ∗ pointsTo_u32 1048548 oldNormY ∗
      pointsTo_u32 1048540 oldLoopX ∗ pointsTo_u32 1048544 oldLoopY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro
    ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy,
      Hshared, HnormX, HnormY, HloopX, HloopY⟩
  iapply func1_spillPrefix_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048512 result ∗
      pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldNormX ∗
      pointsTo_u32 1048548 oldNormY ∗
      pointsTo_u32 1048540 oldLoopX ∗
      pointsTo_u32 1048544 oldLoopY))
    (calls := calls) (a := a) (b := b) (oldX := oldX) (oldY := oldY)
  · iintro Hresources
    icases Hresources with
      ⟨HRscratch, Hglobal', HouterA', HouterB', Hx', Hy'⟩
    icases HRscratch with
      ⟨HR', Hresult', Hshared', HnormX', HnormY', HloopX', HloopY'⟩
    iapply func1_nonzeroGuards_smallStep_wp
      (R := iprop(
        (R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b) ∗
        pointsTo_u64 1048512 result ∗
        pointsTo_u32 1048556 oldShared ∗
        pointsTo_u32 1048552 oldNormX ∗
        pointsTo_u32 1048548 oldNormY ∗
        pointsTo_u32 1048540 oldLoopX ∗
        pointsTo_u32 1048544 oldLoopY))
      calls a b ha hb
    · iintro Hresources
      icases Hresources with ⟨HRouterScratch, Hx'', Hy''⟩
      icases HRouterScratch with
        ⟨HRouter, Hresult'', Hshared'', HnormX'', HnormY'',
          HloopX'', HloopY''⟩
      iapply func1_nonzeroOuterCore_smallStep_wp_to_return
        (R := iprop(R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b))
        func1OuterBody calls a b result ha hb
        oldShared oldNormX oldNormY oldLoopX oldLoopY
      · intro g loopX loopY d6 d8 d7 d9 hg
        iintro Hresources
        iapply hreturn g loopX loopY d6 d8 d7 d9 hg
        iexact Hresources
      · iframe
    · iframe
  · iframe

/-- End-to-end nonzero `func1`: spill pointer arguments, traverse the generated
guards, run the Stein loop, leave the outer block, reload the result, and
return. -/
theorem func1_nonzero_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (result oldX oldY a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (oldShared oldNormX oldNormY oldLoopX oldLoopY : UInt32) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ∗
      pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldNormX ∗ pointsTo_u32 1048548 oldNormY ∗
      pointsTo_u32 1048540 oldLoopX ∗ pointsTo_u32 1048544 oldLoopY ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
          ∃ g : UInt64, ∃ loopX loopY : UInt32,
            ⌜g.toNat =
              Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat⌝ ∗
            (R ∗ globalPointsTo 0 (.i32 1048560) ∗
              pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b) ∗
            pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
            pointsTo_u64 1048512
              (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
            pointsTo_u32 1048556 (sharedShiftWord a b) ∗
            pointsTo_u32 1048552 (operandShiftWord a) ∗
            pointsTo_u32 1048548 (operandShiftWord b) ∗
            pointsTo_u32 1048540 loopX ∗
            pointsTo_u32 1048544 loopY }} := by
  iintro
    ⟨HR, Hglobal, HouterA, HouterB, Hresult, Hx, Hy,
      Hshared, HnormX, HnormY, HloopX, HloopY⟩
  iapply func1_spillPrefix_smallStep_wp
    (R := iprop(R ∗ pointsTo_u64 1048512 result ∗
      pointsTo_u32 1048556 oldShared ∗
      pointsTo_u32 1048552 oldNormX ∗
      pointsTo_u32 1048548 oldNormY ∗
      pointsTo_u32 1048540 oldLoopX ∗
      pointsTo_u32 1048544 oldLoopY))
    (calls := []) (a := a) (b := b) (oldX := oldX) (oldY := oldY)
  · iintro Hresources
    icases Hresources with
      ⟨HRscratch, Hglobal', HouterA', HouterB', Hx', Hy'⟩
    icases HRscratch with
      ⟨HR', Hresult', Hshared', HnormX', HnormY', HloopX', HloopY'⟩
    iapply func1_nonzeroGuards_smallStep_wp
      (R := iprop(
        (R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b) ∗
        pointsTo_u64 1048512 result ∗
        pointsTo_u32 1048556 oldShared ∗
        pointsTo_u32 1048552 oldNormX ∗
        pointsTo_u32 1048548 oldNormY ∗
        pointsTo_u32 1048540 oldLoopX ∗
        pointsTo_u32 1048544 oldLoopY))
      [] a b ha hb
    · iintro Hresources
      icases Hresources with ⟨HRouterScratch, Hx'', Hy''⟩
      icases HRouterScratch with
        ⟨HRouter, Hresult'', Hshared'', HnormX'', HnormY'',
          HloopX'', HloopY''⟩
      iapply func1_nonzeroOuterCore_smallStep_wp
        (R := iprop(R ∗ globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b))
        func1OuterBody a b result ha hb
        oldShared oldNormX oldNormY oldLoopX oldLoopY
      iframe
    · iframe
  · iframe

/-- Finite authoritative-frame form of the complete nonzero `func1` rule. -/
theorem func1_nonzero_frame_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (result oldX oldY : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0) :
    globalPointsTo 0 (.i32 1048560) ∗
      ([∗map] address ↦ byte ∈
        gcdFrameHeap result oldX oldY shiftXY shiftX shiftY nextY nextX a b,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) byte) ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048560, .i32 1048568], func1InitialLocals, []⟩,
        func1, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
          ∃ g : UInt64, ∃ loopX loopY : UInt32,
            ⌜g.toNat =
              Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat⌝ ∗
            (⌜True⌝ ∗ globalPointsTo 0 (.i32 1048560) ∗
              pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b) ∗
            pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
            pointsTo_u64 1048512
              (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
            pointsTo_u32 1048556 (sharedShiftWord a b) ∗
            pointsTo_u32 1048552 (operandShiftWord a) ∗
            pointsTo_u32 1048548 (operandShiftWord b) ∗
            pointsTo_u32 1048540 loopX ∗
            pointsTo_u32 1048544 loopY }} := by
  iintro ⟨Hglobal, Hframe⟩
  ihave Hslots := gcdFrameHeap_pointsTo
    result oldX oldY shiftXY shiftX shiftY nextY nextX a b $$ Hframe
  icases Hslots with
    ⟨Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY, HnextY, HnextX,
      HouterA, HouterB⟩
  iapply func1_nonzero_smallStep_wp
    (R := iprop(⌜True⌝))
    result oldX oldY a b ha hb shiftXY shiftX shiftY nextX nextY
  isplitl []
  · ipureintro
    trivial
  · iframe

/-- Closed operational partial correctness for the nonzero opt0 `func1`,
obtained from iris-lean adequacy over the authoritative physical frame. -/
theorem func1_nonzero_smallStep_partiallyMeets
    (result oldX oldY : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0) :
    Wasm.SmallStep.PartiallyMeets
      (func1ZeroConfig result oldX oldY shiftXY shiftX shiftY nextY nextX a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
    (α := Unit)
    (σ := gcdFrameHeap result oldX oldY
      shiftXY shiftX shiftY nextY nextX a b)
    (globalσ := func1GlobalHeap)
    (φ := fun rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])
  · exact gcdFrameHeap_agrees («module».initialStore : Store Unit).mem
      result oldX oldY shiftXY shiftX shiftY nextY nextX a b
  · apply gcdFrameHeap_inBounds
    rfl
  · exact func1GlobalHeap_agrees
  · intro gs
    iintro ⟨Hframe, Hglobals, Hruntime⟩
    ihave Hglobal := func1GlobalHeap_pointsTo $$ Hglobals
    have hpost : ∀ rs : List Value,
        (iprop(
          ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
            ∃ g : UInt64, ∃ loopX loopY : UInt32,
              ⌜g.toNat =
                Nat.gcd (oddPart64 a).toNat (oddPart64 b).toNat⌝ ∗
              (⌜True⌝ ∗ globalPointsTo 0 (.i32 1048560) ∗
                pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b) ∗
              pointsTo_u64 1048520 g ∗ pointsTo_u64 1048528 g ∗
              pointsTo_u64 1048512
                (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ∗
              pointsTo_u32 1048556 (sharedShiftWord a b) ∗
              pointsTo_u32 1048552 (operandShiftWord a) ∗
              pointsTo_u32 1048548 (operandShiftWord b) ∗
              pointsTo_u32 1048540 loopX ∗
              pointsTo_u32 1048544 loopY)) ⊢
          (iprop(⌜rs =
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝)) := by
      intro rs
      iintro ⟨%hrs, _Hresources⟩
      ipureintro
      exact hrs
    simp only [func1ZeroConfig]
    iclear Hruntime
    iapply wp_mono hpost
    iapply func1_nonzero_frame_smallStep_wp
      result oldX oldY shiftXY shiftX shiftY nextY nextX a b ha hb
    iframe

/-- Complete opt0 `func1` partial correctness, covering zero and nonzero
operands with the same physical configuration and mathematical postcondition. -/
theorem func1_smallStep_partiallyMeets
    (result oldX oldY : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (a b : UInt64) :
    Wasm.SmallStep.PartiallyMeets
      (func1ZeroConfig result oldX oldY shiftXY shiftX shiftY nextY nextX a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  by_cases ha : a = 0
  · exact func1_zero_smallStep_partiallyMeets
      result oldX oldY shiftXY shiftX shiftY nextY nextX a b (Or.inl ha)
  · by_cases hb : b = 0
    · exact func1_zero_smallStep_partiallyMeets
        result oldX oldY shiftXY shiftX shiftY nextY nextX a b (Or.inr hb)
    · exact func1_nonzero_smallStep_partiallyMeets
        result oldX oldY shiftXY shiftX shiftY nextY nextX a b ha hb

/- Driving the OUTER-body program when both operands are nonzero. The
final result `gcd a b` is left at slot `1048512` (`fp + 0`); the loop
exits via `br 2`, surfacing as a `.Break 0` to the supplied continuation
`Q`. The continuation hypothesis `hQ` only needs the result slot and the
fact that the frame pointer (local 2) is unchanged, which is all the
OUTER continuation reads. -/
set_option maxHeartbeats 4000000 in
theorem meatLoop_wp (env : HostEnv Unit) (stm : Store Unit) (a b : UInt64)
    (p0 p1 l1 l2 l3 l4 l5 l6 l7 : Value) (vals : List Value) (Q : Assertion Unit)
    (hpg : stm.mem.pages = 16)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : stm.mem.read64 1048520 = a)
    (hb : stm.mem.read64 1048528 = b)
    (hQ : ∀ (stf : Store Unit) (sf : Locals),
            stf.mem.read64 1048512 = UInt64.ofNat (a.toNat.gcd b.toNat) →
            stf.mem.pages = 16 →
            stf.globals = stm.globals →
            sf.get 2 = some (.i32 1048512) →
            Q (.Break 0 stf sf)) :
    wp «module» meatLoopProg Q stm
      { params := [p0, p1],
        locals := [.i32 1048512, l1, l2, l3, l4, l5, l6, l7], values := vals } env := by
  show wp «module» meatLoopProg Q stm _ env
  unfold meatLoopProg
  simp only []
  simp (config := { maxSteps := 4000000, decide := true }) only [wp_simp, Locals.get, Locals.set?,
    List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
    Nat.reduceLeDiff,
    UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt,
    Mem.read64_write64_disjoint, Mem.read64_write32_disjoint,
    Mem.read32_write32_same,
    hpg, ha, hb,
    Mem.write64_pages, Mem.write32_pages]
  -- Rewrite the two odd-part shift amounts into the `CodeLib` form.
  rw [shift_pipeline a ha0, shift_pipeline b hb0]
  -- Abbreviations for the odd parts and the recombination shift.
  set ao : UInt64 := a >>> (UInt64.ofNat (ctz64 64 a) % 64) with hao
  set bo : UInt64 := b >>> (UInt64.ofNat (ctz64 64 b) % 64) with hbo
  have hab0 : a ||| b ≠ 0 := fun h => ha0 (UInt64.or_eq_zero_iff.mp h).1
  have haone : ao ≠ 0 := UInt64.shr_ctz_ne_zero a ha0
  have hbone : bo ≠ 0 := UInt64.shr_ctz_ne_zero b hb0
  have haodd : ao.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd a ha0
  have hbodd : bo.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd b hb0
  -- Generalize the cluttered scratch-only memory into a single store whose
  -- slots `1048520`/`1048528` carry `ao`/`bo`.
  set stL : Store Unit :=
    { globals := stm.globals,
      mem :=
        ((((stm.mem.write32 1048556 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32))).write32 1048552
                      (UInt32.ofNat ((UInt64.ofNat (ctz64 64 a)).toNat % 2 ^ 32))).write64
                  1048520 ao).write32
              1048548 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 b)).toNat % 2 ^ 32))).write64
          1048528 bo,
      extraMems := stm.extraMems, dataSegments := stm.dataSegments, tables := stm.tables,
      elementSegments := stm.elementSegments, exns := stm.exns, host := stm.host } with hstL
  have hLpg : stL.mem.pages = 16 := by rw [hstL]; simp [hpg]
  have hLa : stL.mem.read64 1048520 = ao := by
    rw [hstL]
    rw [Mem.read64_write64_disjoint _ _ _ _ (by decide),
        Mem.read64_write32_disjoint _ _ _ _ (by decide),
        Mem.read64_write64_same]
  have hLb : stL.mem.read64 1048528 = bo := by
    rw [hstL]; rw [Mem.read64_write64_same]
  -- The shift amount used by the final `shl` recombine.
  have hsh : UInt64.ofNat ((63 : UInt32) &&&
      UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)).toNat % 64
      = UInt64.ofNat (ctz64 64 (b ||| a)) % 64 := by
    rw [ctz_wrap_and_toNat (a ||| b) hab0, ctz_or_comm]
  -- The constant shift value sitting in local 3 throughout the loop.
  set sh3 : UInt32 := UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32) with hsh3
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 16 ∧ st'.globals = stm.globals ∧ s'.values = vals ∧
      (∃ c4 c5 c6 c7 c8 c9 : Value,
        s' = { params := [p0, p1],
               locals := [.i32 1048512, .i32 sh3, c4, c5, c6, c7, c8, c9], values := vals }) ∧
      ∃ x y : UInt64,
        st'.mem.read64 1048520 = x ∧ st'.mem.read64 1048528 = y ∧
        x ≠ 0 ∧ y ≠ 0 ∧ x.toNat % 2 = 1 ∧ y.toNat % 2 = 1 ∧
        Nat.gcd x.toNat y.toNat = Nat.gcd ao.toNat bo.toNat)
    (μ := fun st' _ => (st'.mem.read64 1048520).toNat + (st'.mem.read64 1048528).toNat)
  · -- Initial invariant.
    exact ⟨hLpg, rfl, rfl, ⟨_, _, _, _, _, _, rfl⟩, ao, bo, hLa, hLb, haone, hbone, haodd, hbodd, rfl⟩
  · -- One iteration.
    rintro st' s' ⟨hpg', hglob', hvals, ⟨c4, c5, c6, c7, c8, c9, rfl⟩, x, y, hxr, hyr, hxne, hyne, hxodd, hyodd, hgcd⟩
    -- Enter block A.
    apply wp_block_cons
    simp only [wp_simp, Locals.get, List.length_cons, List.length_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
      UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt, hpg', hxr, hyr]
    by_cases hxy : x = y
    · -- x = y: loop exits with the recombined gcd.
      subst hxy
      simp only [ne_eq, not_true_eq_false, if_false]
      -- The break stores `x <<< shift` at slot 1048512.
      refine hQ _ _ ?_ ?_ hglob' rfl
      · -- result slot holds the gcd.
        rw [Mem.read64_write64_same, hsh]
        have hrec := UInt64.recombine_loop a b x ha0 hb0 ?_
        · simpa [ao, bo, UInt64.toNat_shiftRight] using hrec
        · rw [Nat.gcd_self]
          have hgcd' := hgcd
          rw [hao, hbo] at hgcd'
          simpa [UInt64.toNat_shiftRight] using hgcd'
      · rw [Mem.write64_pages]; exact hpg'
    · -- x ≠ y: fall into block B.
      rw [if_pos hxy]
      simp only [show (1 : UInt32) &&& 1 = 1 from rfl]
      apply wp_block_cons
      simp (config := { maxSteps := 4000000, decide := true }) only [wp_simp,
        Locals.get, Locals.set?, List.length_cons, List.length_nil,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
        Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
        UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt, hpg', hxr, hyr,
        Mem.read64_write64_same, Mem.read64_write64_disjoint, Mem.read64_write32_disjoint,
        Mem.read32_write32_same,
        Mem.write64_pages, Mem.write32_pages]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      by_cases hlt : y < x
      · -- y < x: subtract y from x, halve x.  (x-branch.)
        rw [if_pos hlt]
        obtain ⟨hne', hodd', hgcd', hdec⟩ := UInt64.stein_step_x x y hxne hyne hxodd hyodd hlt
        have hxsub0 : x - y ≠ 0 := by
          intro h
          have hsub := UInt64.toNat_sub_of_le x y
            (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt)))
          have h0 : (x - y).toNat = 0 := by rw [h]; rfl
          rw [hsub] at h0
          have := UInt64.lt_iff_toNat_lt.mp hlt
          omega
        have hshx := ctz_wrap_and_toNat (x - y) hxsub0
        have hx1 := oddPart_toNat (x - y)
        split
        · rename_i h; simp at h
        · rw [hshx]
          refine ⟨⟨trivial, hglob', by simp, ⟨c4, c5, _, _, _, _, rfl⟩,
            (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64), y,
            rfl, rfl, hne', hyne, ?_, hyodd, ?_⟩, ?_⟩
          · rw [hx1]; exact hodd'
          · rw [hx1]; exact hgcd'.trans hgcd
          · rw [hx1]; have := hdec; omega
        · rename_i h; exact (h 1 vals rfl).elim
      · -- ¬(y < x): subtract x from y, halve y.  (y-branch.)
        rw [if_neg hlt]
        obtain ⟨hne', hodd', hgcd', hdec⟩ :=
          UInt64.stein_step_y x y hxne hyne hxodd hyodd hlt hxy
        have hysub0 : y - x ≠ 0 := by
          intro h
          have hxlt : x < y := by
            rw [UInt64.lt_iff_toNat_lt]
            have h1 : ¬ y.toNat < x.toNat := fun hh => hlt (UInt64.lt_iff_toNat_lt.mpr hh)
            have h2 : x.toNat ≠ y.toNat := fun hh => hxy (UInt64.toNat.inj hh)
            omega
          have hsub := UInt64.toNat_sub_of_le y x
            (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hxlt)))
          have h0 : (y - x).toNat = 0 := by rw [h]; rfl
          rw [hsub] at h0
          have := UInt64.lt_iff_toNat_lt.mp hxlt
          omega
        have hshy := ctz_wrap_and_toNat (y - x) hysub0
        have hy1 := oddPart_toNat (y - x)
        split
        · rw [hshy]
          refine ⟨⟨trivial, hglob', trivial, ⟨c4, c5, _, _, c8, c9, rfl⟩,
            x, (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64),
            rfl, rfl, hxne, hne', hxodd, ?_, ?_⟩, ?_⟩
          · rw [hy1]; exact hodd'
          · rw [hy1]; exact hgcd'.trans hgcd
          · rw [hy1]; have := hdec; omega
        · rename_i h0 h; simp only [List.cons.injEq, Value.i32.injEq,
            show (1 : UInt32) &&& 0 = 0 from rfl] at h; exact (h0 h.1.symm).elim
        · rename_i h; exact (h 0 vals rfl).elim

set_option maxHeartbeats 4000000 in
theorem func1_terminates (env : HostEnv Unit) (st1 : Store Unit) (a b : UInt64)
    (tail : List Value)
    (hpg : st1.mem.pages = 16)
    (hg0 : st1.globals.globals[0]? = some (.i32 1048560))
    (ha : st1.mem.read64 1048560 = a)
    (hb : st1.mem.read64 1048568 = b) :
    TerminatesWith env «module» 1 st1 ([.i32 1048568, .i32 1048560] ++ tail)
      (fun st' vs => st'.globals = st1.globals ∧
        vs = .i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) :: tail) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32, .i32, .i64, .i32, .i64, .i32], func1, [.i64], none⟩) rfl
  unfold func1
  wp_run
  rw [hg0]
  -- After frame setup + the two argument copies the memory is
  -- `(st1.mem.write64 1048520 a).write64 1048528 b`, the frame pointer is
  -- `local2 = 1048512`, and the bound checks are discharged by `hpg`.
  simp [ha, hb, Mem.read64_write64_disjoint, hpg]
  -- Memory now holds `a` at slot 1048520 and `b` at slot 1048528; frame
  -- pointer (local 2) is 1048512. Abbreviate the in-frame store.
  set M0 : Mem := (st1.mem.write64 1048520 a).write64 1048528 b with hM0
  have hM0a : M0.read64 1048520 = a := by
    rw [hM0, Mem.read64_write64_disjoint _ _ _ _ (by decide), Mem.read64_write64_same]
  have hM0b : M0.read64 1048528 = b := by
    rw [hM0, Mem.read64_write64_same]
  have hM0pg : M0.pages = 16 := by rw [hM0]; simp [hpg]
  -- Recognize the OUTER block body as `MIDDLE_block :: meatLoopProg` (defeq),
  -- keeping the giant meat opaque to `simp` during the zero-checks.
  show wp «module»
    (.block 0 0
      (.block 0 0
        (.block 0 0
          [.localGet 2, .load64 8, .constI64 0, .eqI64, .const 1, .and, .br_if 0,
           .localGet 2, .load64 16, .constI64 0, .eqI64, .const 1, .and, .eqz, .br_if 1]
         :: .localGet 2 :: .localGet 2 :: .load64 8 :: .localGet 2 :: .load64 16
            :: .orI64 :: .store64 0 :: .br 1 :: [])
       :: meatLoopProg)
     :: .localGet 2 :: .load64 0 :: .ret :: [])
    _ _ _ env
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  -- INNER body: the two zero-checks.
  simp only [wp_simp, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
    UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt, hM0a, hM0b, hM0pg]
  -- The result slot read after the recombine-as-OR store.
  have horRead : (M0.write64 1048512 (a ||| b)).read64 1048512 = a ||| b :=
    Mem.read64_write64_same _ _ _
  have horPg : (M0.write64 1048512 (a ||| b)).pages = 16 := by rw [Mem.write64_pages]; exact hM0pg
  by_cases ha0 : a = 0
  · -- a = 0: result is `0 ||| b = b = gcd 0 b`.
    subst ha0
    simp only [if_true,
      show (1 : UInt32) &&& 1 = 1 from rfl]
    simp only [horRead, horPg, Nat.reduceMul]
    rw [show (0 : UInt64) ||| b = b from by
          apply UInt64.toNat.inj; rw [UInt64.toNat_or]; simp]
    refine ⟨trivial, ?_⟩
    simp [Nat.gcd_zero_left]
  · by_cases hb0 : b = 0
    · -- b = 0: result is `a ||| 0 = a = gcd a 0`.
      subst hb0
      simp only [ha0, if_false, if_true,
        show (1 : UInt32) &&& 0 = 0 from rfl, show (1 : UInt32) &&& 1 = 1 from rfl]
      simp only [horRead, horPg, Nat.reduceMul]
      rw [show a ||| (0 : UInt64) = a from by
            apply UInt64.toNat.inj; rw [UInt64.toNat_or]; simp]
      refine ⟨trivial, ?_⟩
      simp [Nat.gcd_zero_right]
    · -- both nonzero: run the Stein meat+loop.
      simp only [ha0, hb0, if_false, show (1 : UInt32) &&& 0 = 0 from rfl,
        if_true]
      apply meatLoop_wp (a := a) (b := b)
      · exact hM0pg
      · exact ha0
      · exact hb0
      · exact hM0a
      · exact hM0b
      · rintro stf sf hfr hfpg hfglob hfl2
        have hg2 : (if 2 < sf.params.length then sf.params[2]?
            else if 2 < sf.params.length + sf.locals.length then sf.locals[2 - sf.params.length]?
            else none) = some (.i32 1048512) := hfl2
        simp only [hg2, hfpg, List.take, List.nil_append,
          Nat.reduceMul, List.cons_append]
        rw [show (1048512 : UInt32) + 0 = 1048512 from rfl, hfr,
          show UInt32.toNat 1048512 = 1048512 from rfl]
        refine ⟨hfglob, ?_⟩
        norm_num

/-! ## `func0`: the wrapper that spills the operands and calls `func1` -/

def func0InitialLocals : List Value :=
  [.i32 0, .i64 0]

def func0CallLocals : List Value :=
  [.i32 1048560, .i64 0]

def func0AfterCallProg : Program :=
  [.localSet 3, .localGet 2, .const 16, .add, .globalSet 0,
    .localGet 3, .ret]

def func0CallerFrame (a b : UInt64) : Wasm.SmallStep.CallFrame :=
  { locals := ⟨[.i64 a, .i64 b], func0CallLocals, []⟩
    continuation := func0AfterCallProg
    resultArity := 1
    callerRemainder := []
    control := [] }

/-- Execute the generated `func0` stack-frame prologue up to its direct call
of `func1`. The stack-pointer global and both caller-frame words are updated
through authoritative physical ownership. -/
theorem func0_callPrefix_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b oldOuterA oldOuterB : UInt64)
    (hcontinue :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048560 a ∗ pointsTo_u64 1048568 b ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i64 a, .i64 b], func0CallLocals,
            [.i32 1048568, .i32 1048560]⟩,
          .call 1 :: func0AfterCallProg, 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048560 oldOuterA ∗
      pointsTo_u64 1048568 oldOuterB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], func0InitialLocals, []⟩,
        func0, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, HouterA, HouterB⟩
  simp only [func0, func0InitialLocals]
  iapply Wasm.SmallStep.wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_sub
  inext
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_globalSet $$ Hglobal
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HouterALater :
      ▷ pointsTo_u64 ((1048560 : UInt32) + 0) oldOuterA $$ [HouterA]
  · inext
    rw [show (1048560 : UInt32) + 0 = 1048560 from rfl]
    iexact HouterA
  iapply Wasm.SmallStep.wp_store64 oldOuterA
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HouterALater
  inext
  iintro HouterA
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HouterBLater :
      ▷ pointsTo_u64 ((1048560 : UInt32) + 8) oldOuterB $$ [HouterB]
  · inext
    rw [show (1048560 : UInt32) + 8 = 1048568 from rfl]
    iexact HouterB
  iapply Wasm.SmallStep.wp_store64 oldOuterB
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HouterBLater
  inext
  iintro HouterB
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  rw [show (8 : UInt32) + 1048560 = 1048568 from rfl]
  simp only [func0CallLocals, func0AfterCallProg] at hcontinue
  have hOuterAProp :
      pointsTo_u64 ((1048560 : UInt32) + 0) a =
        pointsTo_u64 1048560 a :=
    congrArg (fun address => pointsTo_u64 address a) (by decide)
  have hOuterBProp :
      pointsTo_u64 ((1048560 : UInt32) + 8) b =
        pointsTo_u64 1048568 b :=
    congrArg (fun address => pointsTo_u64 address b) (by decide)
  ihave HouterAExact : pointsTo_u64 1048560 a $$ [HouterA]
  · rw [← hOuterAProp]
    iexact HouterA
  ihave HouterBExact : pointsTo_u64 1048568 b $$ [HouterB]
  · rw [← hOuterBProp]
    iexact HouterB
  iapply hcontinue
  iframe

/-- Resume `func0` after `func1` returns: save the result, restore the stack
pointer global, and return the GCD from the top-level invocation. -/
theorem func0_afterCall_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b : UInt64)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048576) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i64 a, .i64 b],
            [.i32 1048560,
              .i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))],
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], func0CallLocals,
          [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
        func0AfterCallProg, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal⟩
  simp only [func0AfterCallProg, func0CallLocals]
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  rw [show (16 : UInt32) + 1048560 = 1048576 from rfl]
  iapply Wasm.SmallStep.wp_globalSet $$ Hglobal
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply hreturn
  iframe

/-- Closed top-level corollary of the contextual `func0` epilogue. -/
theorem func0_afterCall_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (a b : UInt64) :
    R ∗ globalPointsTo 0 (.i32 1048560) ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], func0CallLocals,
          [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
        func0AfterCallProg, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs,
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
          R ∗ globalPointsTo 0 (.i32 1048576) }} := by
  iintro Hresources
  iapply func0_afterCall_smallStep_wp_to_return R [] a b
  · iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromFunction
    inext
    simp only [List.take]
    iapply wp_value'
    isplit
    · ipureintro
      rfl
    · iexact Hresources
  · iexact Hresources

def func0FramePost
    [WasmHeapGS] [WasmGlobalGS]
    (R : IProp WasmHeapGF) (a b : UInt64) (rs : List Value) :
    IProp WasmHeapGF :=
  iprop(
    ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
    ∃ result x y outerA outerB : UInt64,
    ∃ shiftXY shiftX shiftY nextY nextX : UInt32,
      R ∗ globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 outerA ∗ pointsTo_u64 1048568 outerB)

/-- Package one exact physical frame into the branch-independent existential
postcondition used by callers of `func0`. -/
theorem func0_exactFrame_entails_post
    [WasmHeapGS] [WasmGlobalGS]
    (R : IProp WasmHeapGF)
    (a b result x y outerA outerB : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32) :
    R ∗ globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 outerA ∗ pointsTo_u64 1048568 outerB ⊢
    func0FramePost R a b
      [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] := by
  iintro
    ⟨HR, Hglobal, Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY,
      HnextY, HnextX, HouterA, HouterB⟩
  unfold func0FramePost
  isplit
  · ipureintro
    rfl
  · iexists result
    iexists x
    iexists y
    iexists outerA
    iexists outerB
    iexists shiftXY
    iexists shiftX
    iexists shiftY
    iexists nextY
    iexists nextX
    iframe

/-- Branch-independent `func0` epilogue: all exact frame contents are retained
under existential ownership in the shared caller postcondition. -/
theorem func0_afterCall_frame_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (a b returned result x y outerA outerB : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (hreturned :
      returned = UInt64.ofNat (Nat.gcd a.toNat b.toNat)) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 outerA ∗ pointsTo_u64 1048568 outerB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], [.i32 1048560, .i64 0],
          [.i64 returned]⟩,
        [.localSet 3, .localGet 2, .const 16, .add, .globalSet 0,
          .localGet 3, .ret],
        1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs, func0FramePost R a b rs }} := by
  subst returned
  iintro Hresources
  have hpost : ∀ rs : List Value,
      (iprop(
        ⌜rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝ ∗
        (R ∗ pointsTo_u64 1048512 result ∗
          pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
          pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
          pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
          pointsTo_u32 1048540 nextX ∗
          pointsTo_u64 1048560 outerA ∗ pointsTo_u64 1048568 outerB) ∗
        globalPointsTo 0 (.i32 1048576))) ⊢
      func0FramePost R a b rs := by
    intro rs
    iintro ⟨%hrs, Hframe, Hglobal⟩
    icases Hframe with
      ⟨HR, Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY,
        HnextY, HnextX, HouterA, HouterB⟩
    unfold func0FramePost
    isplit
    · ipureintro
      exact hrs
    · iexists result
      iexists x
      iexists y
      iexists outerA
      iexists outerB
      iexists shiftXY
      iexists shiftX
      iexists shiftY
      iexists nextY
      iexists nextX
      iframe
  iapply wp_mono hpost
  have hafter := func0_afterCall_smallStep_wp
    (s := s) (E := E)
    (R := iprop(R ∗ pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 outerA ∗ pointsTo_u64 1048568 outerB))
    a b
  simp only [func0CallLocals, func0AfterCallProg] at hafter
  iapply hafter
  icases Hresources with
    ⟨HR, Hglobal, Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY,
      HnextY, HnextX, HouterA, HouterB⟩
  iframe

/-- Resume the suspended `func0` caller from any completed `func1` local
state, run the contextual epilogue, and package the exact frame for the outer
caller. -/
theorem func0_resumeCaller_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (calleeLocals : Locals)
    (a b returned result x y outerA outerB : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (hreturned :
      returned = UInt64.ofNat (Nat.gcd a.toNat b.toNat))
    (hreturn :
      func0FramePost R a b
          [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i64 a, .i64 b],
            [.i32 1048560,
              .i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))],
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 outerA ∗ pointsTo_u64 1048568 outerB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨{ calleeLocals with
          values := [.i64 returned] },
        [.ret], 1, [], [],
        func0CallerFrame a b :: calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  subst returned
  iintro Hresources
  iapply Wasm.SmallStep.wp_returnFromCallExplicit
  inext
  simp only [func0CallerFrame, func0CallLocals, func0AfterCallProg,
    List.take, List.append_nil]
  have hafter := func0_afterCall_smallStep_wp_to_return
    (s := s) (E := E) (Φ := Φ)
    (R := iprop(R ∗ pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 x ∗ pointsTo_u64 1048528 y ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 outerA ∗ pointsTo_u64 1048568 outerB))
    calls a b
  simp only [func0CallLocals, func0AfterCallProg] at hafter
  iapply hafter
  · iintro Hresources
    iapply hreturn
    iapply func0_exactFrame_entails_post
      R a b result x y outerA outerB
      shiftXY shiftX shiftY nextY nextX
    icases Hresources with ⟨Hframe, Hglobal⟩
    icases Hframe with
      ⟨HR, Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY,
        HnextY, HnextX, HouterA, HouterB⟩
    iframe
  · icases Hresources with
      ⟨HR, Hglobal, Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY,
        HnextY, HnextX, HouterA, HouterB⟩
    iframe

/-- Contextual `func0` rule. It executes the complete wrapper but leaves its
final explicit return to an arbitrary outer call stack. -/
theorem func0_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (calls : List Wasm.SmallStep.CallFrame)
    (a b result oldX oldY oldOuterA oldOuterB : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32)
    (hreturn :
      func0FramePost (iprop(R ∗ runtimeModuleOwn «module»)) a b
          [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i64 a, .i64 b],
            [.i32 1048560,
              .i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))],
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 oldOuterA ∗
      pointsTo_u64 1048568 oldOuterB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], func0InitialLocals, []⟩,
        func0, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro
    ⟨HR, Hruntime, Hglobal, Hresult, Hx, Hy, HshiftXY, HshiftX,
      HshiftY, HnextY, HnextX, HouterA, HouterB⟩
  iapply func0_callPrefix_smallStep_wp
    (R := iprop(R ∗ runtimeModuleOwn «module» ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX))
    calls a b oldOuterA oldOuterB
  · iintro Hresources
    icases Hresources with
      ⟨HRouter, Hglobal', HouterA', HouterB'⟩
    icases HRouter with
      ⟨HR', Hruntime', Hresult', Hx', Hy', HshiftXY', HshiftX',
        HshiftY', HnextY', HnextX'⟩
    iapply Wasm.SmallStep.wp_call
      «module» 1 func1Def (by simp [«module»]) rfl $$ Hruntime'
    inext
    iintro Hruntime
    simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
    rw [show
      ([.i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0,
        .i32 0] : List Value) = func1InitialLocals from rfl]
    rw [show
      ({ locals := ⟨[.i64 a, .i64 b], func0CallLocals, []⟩
         continuation := func0AfterCallProg
         resultArity := 1
         callerRemainder := []
         control := [] } : Wasm.SmallStep.CallFrame) =
        func0CallerFrame a b from rfl]
    by_cases ha : a = 0
    · subst a
      iapply func1_leftZero_smallStep_wp_to_return
        (R := iprop(R ∗ runtimeModuleOwn «module» ∗
          pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
          pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
          pointsTo_u32 1048540 nextX))
        (func0CallerFrame 0 b :: calls) result oldX oldY b
      · iintro Hresources
        icases Hresources with
          ⟨HRscratch, Hglobal'', HouterA'', HouterB'', Hresult'', Hx'', Hy''⟩
        icases HRscratch with
          ⟨HR'', Hruntime'', HshiftXY'', HshiftX'', HshiftY'',
            HnextY'', HnextX''⟩
        iapply func0_resumeCaller_smallStep_wp
          (R := iprop(R ∗ runtimeModuleOwn «module»))
          calls
          ⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩
          0 b b b 0 b 0 b shiftXY shiftX shiftY nextY nextX
          (by simp) hreturn
        iframe
      · iframe
    · by_cases hb : b = 0
      · subst b
        iapply func1_rightZero_smallStep_wp_to_return
          (R := iprop(R ∗ runtimeModuleOwn «module» ∗
            pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
            pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
            pointsTo_u32 1048540 nextX))
          (func0CallerFrame a 0 :: calls) result oldX oldY a ha
        · iintro Hresources
          icases Hresources with
            ⟨HRscratch, Hglobal'', HouterA'', HouterB'', Hresult'', Hx'', Hy''⟩
          icases HRscratch with
            ⟨HR'', Hruntime'', HshiftXY'', HshiftX'', HshiftY'',
              HnextY'', HnextX''⟩
          iapply func0_resumeCaller_smallStep_wp
            (R := iprop(R ∗ runtimeModuleOwn «module»))
            calls
            ⟨[.i32 1048560, .i32 1048568], func1SpilledLocals, []⟩
            a 0 a a a 0 a 0 shiftXY shiftX shiftY nextY nextX
            (by simp) hreturn
          iframe
        · iframe
      · iapply func1_nonzero_smallStep_wp_to_return
          (R := iprop(R ∗ runtimeModuleOwn «module»))
          (func0CallerFrame a b :: calls)
          result oldX oldY a b ha hb
          shiftXY shiftX shiftY nextX nextY
        · intro g loopX loopY d6 d8 d7 d9 hg
          iintro Hresources
          icases Hresources with
            ⟨HRscratch, Hx'', Hy'', Hresult'', HloopX'', HloopY''⟩
          icases HRscratch with
            ⟨HRouter, Hshared'', HnormX'', HnormY''⟩
          icases HRouter with
            ⟨HRruntime, Hglobal'', HouterA'', HouterB''⟩
          icases HRruntime with ⟨HR'', Hruntime''⟩
          iapply func0_resumeCaller_smallStep_wp
            (R := iprop(R ∗ runtimeModuleOwn «module»))
            calls
            ⟨[.i32 1048560, .i32 1048568],
              func1LoopHeaderLocals a b d6 d8 d7 d9, []⟩
            a b (UInt64.ofNat (Nat.gcd a.toNat b.toNat))
            (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) g g a b
            (sharedShiftWord a b) (operandShiftWord a) (operandShiftWord b)
            loopY loopX rfl hreturn
          iframe
        · iframe
  · iframe

/-- Complete small-step Iris rule for `func0`, including its direct call to
`func1`, contextual callee return, stack-pointer restoration, and final
top-level return. -/
theorem func0_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (a b result oldX oldY oldOuterA oldOuterB : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 oldOuterA ∗
      pointsTo_u64 1048568 oldOuterB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], func0InitialLocals, []⟩,
        func0, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs, func0FramePost (iprop(R ∗ runtimeModuleOwn «module»)) a b rs }} := by
  iintro
    ⟨HR, Hruntime, Hglobal, Hresult, Hx, Hy, HshiftXY, HshiftX,
      HshiftY, HnextY, HnextX, HouterA, HouterB⟩
  iapply func0_callPrefix_smallStep_wp
    (R := iprop(R ∗ runtimeModuleOwn «module» ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX))
    [] a b oldOuterA oldOuterB
  · iintro Hresources
    icases Hresources with
      ⟨HRouter, Hglobal', HouterA', HouterB'⟩
    icases HRouter with
      ⟨HR', Hruntime', Hresult', Hx', Hy', HshiftXY', HshiftX',
        HshiftY', HnextY', HnextX'⟩
    iapply Wasm.SmallStep.wp_call
      «module» 1 func1Def (by simp [«module»]) rfl $$ Hruntime'
    inext
    iintro Hruntime
    simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
    rw [show
      ([.i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0,
        .i32 0] : List Value) = func1InitialLocals from rfl]
    rw [show
      ({ locals := ⟨[.i64 a, .i64 b], func0CallLocals, []⟩
         continuation := func0AfterCallProg
         resultArity := 1
         callerRemainder := []
         control := [] } : Wasm.SmallStep.CallFrame) =
        func0CallerFrame a b from rfl]
    by_cases ha : a = 0
    · subst a
      iapply func1_leftZero_smallStep_wp_to_return
        (R := iprop(R ∗ runtimeModuleOwn «module» ∗
          pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
          pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
          pointsTo_u32 1048540 nextX))
        [func0CallerFrame 0 b] result oldX oldY b
      · iintro Hresources
        icases Hresources with
          ⟨HRscratch, Hglobal'', HouterA'', HouterB'', Hresult'', Hx'', Hy''⟩
        icases HRscratch with
          ⟨HR'', Hruntime'', HshiftXY'', HshiftX'', HshiftY'',
            HnextY'', HnextX''⟩
        iapply Wasm.SmallStep.wp_returnFromCallExplicit
        inext
        simp [func0CallerFrame, func0CallLocals, func0AfterCallProg]
        iapply func0_afterCall_frame_smallStep_wp
          (R := iprop(R ∗ runtimeModuleOwn «module»))
          0 b b b 0 b 0 b shiftXY shiftX shiftY nextY nextX
          (by simp [Nat.gcd_zero_left])
        iframe
      · iframe
    · by_cases hb : b = 0
      · subst b
        iapply func1_rightZero_smallStep_wp_to_return
          (R := iprop(R ∗ runtimeModuleOwn «module» ∗
            pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
            pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
            pointsTo_u32 1048540 nextX))
          [func0CallerFrame a 0] result oldX oldY a ha
        · iintro Hresources
          icases Hresources with
            ⟨HRscratch, Hglobal'', HouterA'', HouterB'', Hresult'', Hx'', Hy''⟩
          icases HRscratch with
            ⟨HR'', Hruntime'', HshiftXY'', HshiftX'', HshiftY'',
              HnextY'', HnextX''⟩
          iapply Wasm.SmallStep.wp_returnFromCallExplicit
          inext
          simp [func0CallerFrame, func0CallLocals, func0AfterCallProg]
          iapply func0_afterCall_frame_smallStep_wp
            (R := iprop(R ∗ runtimeModuleOwn «module»))
            a 0 a a a 0 a 0 shiftXY shiftX shiftY nextY nextX
            (by simp [Nat.gcd_zero_right])
          iframe
        · iframe
      · iapply func1_nonzero_smallStep_wp_to_return
          (R := iprop(R ∗ runtimeModuleOwn «module»))
          [func0CallerFrame a b]
          result oldX oldY a b ha hb
          shiftXY shiftX shiftY nextX nextY
        · intro g loopX loopY d6 d8 d7 d9 hg
          iintro Hresources
          icases Hresources with
            ⟨HRscratch, Hx'', Hy'', Hresult'', HloopX'', HloopY''⟩
          icases HRscratch with
            ⟨HRouter, Hshared'', HnormX'', HnormY''⟩
          icases HRouter with
            ⟨HRruntime, Hglobal'', HouterA'', HouterB''⟩
          icases HRruntime with ⟨HR'', Hruntime''⟩
          iapply Wasm.SmallStep.wp_returnFromCallExplicit
          inext
          simp only [func0CallerFrame, func0CallLocals, func0AfterCallProg,
            List.take, List.append_nil]
          iapply func0_afterCall_frame_smallStep_wp
            (R := iprop(R ∗ runtimeModuleOwn «module»))
            a b (UInt64.ofNat (Nat.gcd a.toNat b.toNat))
            (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) g g a b
            (sharedShiftWord a b) (operandShiftWord a) (operandShiftWord b)
            loopY loopX rfl
          iframe
        · iframe
  · iframe

def func2CallerFrame (a b : UInt64) : Wasm.SmallStep.CallFrame :=
  { locals := ⟨[.i64 a, .i64 b], [], []⟩
    continuation := [.ret]
    resultArity := 1
    callerRemainder := []
    control := [] }

/-- Complete small-step Iris rule for the exported `func2` wrapper. -/
theorem func2_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF)
    (a b result oldX oldY oldOuterA oldOuterB : UInt64)
    (shiftXY shiftX shiftY nextY nextX : UInt32) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048512 result ∗
      pointsTo_u64 1048520 oldX ∗ pointsTo_u64 1048528 oldY ∗
      pointsTo_u32 1048556 shiftXY ∗ pointsTo_u32 1048552 shiftX ∗
      pointsTo_u32 1048548 shiftY ∗ pointsTo_u32 1048544 nextY ∗
      pointsTo_u32 1048540 nextX ∗
      pointsTo_u64 1048560 oldOuterA ∗
      pointsTo_u64 1048568 oldOuterB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], [], []⟩,
        func2, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ rs, func0FramePost (iprop(R ∗ runtimeModuleOwn «module»)) a b rs }} := by
  iintro Hresources
  simp only [func2]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  icases Hresources with
    ⟨HR, Hruntime, Hglobal, Hresult, Hx, Hy, HshiftXY, HshiftX,
      HshiftY, HnextY, HnextX, HouterA, HouterB⟩
  iapply Wasm.SmallStep.wp_call
    «module» 0 func0Def (by simp [«module»]) rfl $$ Hruntime
  inext
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  rw [show ([.i32 0, .i64 0] : List Value) = func0InitialLocals from rfl]
  rw [show
    ({ locals := ⟨[.i64 a, .i64 b], [], []⟩
       continuation := [.ret]
       resultArity := 1
       callerRemainder := []
       control := [] } : Wasm.SmallStep.CallFrame) =
      func2CallerFrame a b from rfl]
  iapply func0_smallStep_wp_to_return
    R [func2CallerFrame a b]
    a b result oldX oldY oldOuterA oldOuterB
    shiftXY shiftX shiftY nextY nextX
  · iintro Hpost
    iapply Wasm.SmallStep.wp_returnFromCallExplicit
    inext
    simp only [func2CallerFrame, List.take, List.append_nil]
    iapply Wasm.SmallStep.wp_returnFromFunction
    inext
    simp only [List.take, List.append_nil]
    iapply wp_value'
    iexact Hpost
  · iframe

def func0InitialHeap : WasmHeapMap (Option UInt8) :=
  gcdFrameHeap 0 0 0 0 0 0 0 0 0 0

theorem func0_initialFrameMem_eq :
    gcdFrameMem («module».initialStore : Store Unit).mem
      0 0 0 0 0 0 0 0 0 0 =
    («module».initialStore : Store Unit).mem := by
  simp [gcdFrameMem, «module», Module.initialStore, Mem.write64,
    Mem.write32, Mem.empty]

theorem func0InitialHeap_agrees :
    heapAgreesWithMem func0InitialHeap
      («module».initialStore : Store Unit).mem := by
  rw [← func0_initialFrameMem_eq]
  exact gcdFrameHeap_agrees
    («module».initialStore : Store Unit).mem 0 0 0 0 0 0 0 0 0 0

theorem func0InitialHeap_inBounds :
    heapAddressesInBounds func0InitialHeap
      («module».initialStore : Store Unit).mem := by
  rw [← func0_initialFrameMem_eq]
  apply gcdFrameHeap_inBounds
  rfl

def func0GlobalHeap : WasmGlobalMap Value :=
  insert ∅ 0 (.i32 1048576)

theorem func0GlobalHeap_agrees :
    globalHeapAgrees func0GlobalHeap
      («module».initialStore : Store Unit).globals := by
  intro index value hget
  unfold func0GlobalHeap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (Ne.symm hindex), get?_empty] at hget
    contradiction

theorem func0GlobalHeap_pointsTo [WasmGlobalGS] :
    ([∗map] index ↦ value ∈ func0GlobalHeap,
      globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576) := by
  unfold func0GlobalHeap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty 0)).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  exact .rfl

def func0Config (a b : UInt64) : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i64 a, .i64 b], func0InitialLocals, []⟩,
        func0, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := initial } }

def func2Config (a b : UInt64) : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i64 a, .i64 b], [], []⟩,
        func2, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := initial } }

/-- Closed operational partial correctness of opt0 `func0` from the canonical
module store. -/
theorem func0_smallStep_partiallyMeets (a b : UInt64) :
    Wasm.SmallStep.PartiallyMeets
      (func0Config a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
    (α := Unit)
    (σ := func0InitialHeap)
    (globalσ := func0GlobalHeap)
    (φ := fun rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])
  · exact func0InitialHeap_agrees
  · exact func0InitialHeap_inBounds
  · exact func0GlobalHeap_agrees
  · intro gs
    unfold func0InitialHeap
    iintro ⟨Hframe, Hglobals, Hruntime⟩
    ihave Hglobal := func0GlobalHeap_pointsTo $$ Hglobals
    ihave Hslots := gcdFrameHeap_pointsTo
      0 0 0 0 0 0 0 0 0 0 $$ Hframe
    icases Hslots with
      ⟨Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY, HnextY, HnextX,
        HouterA, HouterB⟩
    have hpost : ∀ rs : List Value,
        func0FramePost (iprop(⌜True⌝ ∗ runtimeModuleOwn «module»))
            a b rs ⊢
          (iprop(⌜rs =
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝)) := by
      intro rs
      unfold func0FramePost
      iintro ⟨%hrs, _Hresources⟩
      ipureintro
      exact hrs
    simp only [func0Config]
    iapply wp_mono hpost
    iapply func0_smallStep_wp
      (R := iprop(⌜True⌝))
      a b 0 0 0 0 0 0 0 0 0 0
    isplitl []
    · ipureintro
      trivial
    · iframe

/-- Closed operational partial correctness of the exported opt0 `func2`
wrapper from the canonical module store. -/
theorem func2_smallStep_partiallyMeets (a b : UInt64) :
    Wasm.SmallStep.PartiallyMeets
      (func2Config a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
    (α := Unit)
    (σ := func0InitialHeap)
    (globalσ := func0GlobalHeap)
    (φ := fun rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])
  · exact func0InitialHeap_agrees
  · exact func0InitialHeap_inBounds
  · exact func0GlobalHeap_agrees
  · intro gs
    unfold func0InitialHeap
    iintro ⟨Hframe, Hglobals, Hruntime⟩
    ihave Hglobal := func0GlobalHeap_pointsTo $$ Hglobals
    ihave Hslots := gcdFrameHeap_pointsTo
      0 0 0 0 0 0 0 0 0 0 $$ Hframe
    icases Hslots with
      ⟨Hresult, Hx, Hy, HshiftXY, HshiftX, HshiftY, HnextY, HnextX,
        HouterA, HouterB⟩
    have hpost : ∀ rs : List Value,
        func0FramePost (iprop(⌜True⌝ ∗ runtimeModuleOwn «module»))
            a b rs ⊢
          (iprop(⌜rs =
            [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]⌝)) := by
      intro rs
      unfold func0FramePost
      iintro ⟨%hrs, _Hresources⟩
      ipureintro
      exact hrs
    simp only [func2Config]
    iapply wp_mono hpost
    iapply func2_smallStep_wp
      (R := iprop(⌜True⌝))
      a b 0 0 0 0 0 0 0 0 0 0
    isplitl []
    · ipureintro
      trivial
    · iframe

/- `func0` allocates a 16-byte frame at `global0 − 16 = 1048560`, spills
`a` to `[1048560]` and `b` to `[1048568]`, calls `func1` with those two
pointers, restores the stack pointer and returns `gcd a b`. -/
set_option maxHeartbeats 1000000 in
theorem func0_terminates (env : HostEnv Unit) (a b : UInt64) :
    TerminatesWith env «module» 0 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := by rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 16 := by rfl
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64], [.i32, .i64], func0, [.i64], none⟩) rfl
  unfold func0
  wp_run
  rw [hg]
  simp [hp]
  -- At the call point: memory holds `a` at 1048560, `b` at 1048568, global0
  -- is 1048560.  Discharge `func1` via its `TerminatesWith`.
  apply wp_call_tw
    (func1_terminates env _ a b []
      (by rw [Mem.write64_pages, Mem.write64_pages]; exact hp)
      (by rfl)
      (by rw [Mem.read64_write64_disjoint _ _ _ _ (by decide), Mem.read64_write64_same])
      (by rw [Mem.read64_write64_same]))
  -- The call returns `gcd a b`; restore the stack pointer and `ret`.
  rintro stA vsA ⟨hAglob, rfl⟩
  wp_run
  -- `globalSet 0` is in-bounds because `func1` preserved the globals.
  rw [hAglob]
  rfl

/-! ## Public small-step specification -/

/-- The exported `gcd_u64` returns the greatest common divisor of two
`u64` operands from the canonical instantiated store. The contract uses the
authoritative small-step machine and Iris partial correctness; fuel and the
legacy interpreter are absent from its public surface. -/
@[spec_of "rust-exported" "num_integer::gcd_u64"]
def GcdU64Spec : Prop :=
  ∀ (a b : UInt64),
    Wasm.SmallStep.PartiallyMeets
      (func2Config a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

@[proves Project.NumInteger.Spec.GcdU64Spec]
theorem gcd_u64_correct : GcdU64Spec :=
  func2_smallStep_partiallyMeets

/-! ## Legacy total-correctness compatibility -/

/-- Fuel-abstracted big-step statement retained for the old equivalence API
until its opt0 termination proof is ported to finite `SmallStep.Steps`. -/
def LegacyGcdU64Spec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 2 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

theorem gcd_u64_legacy_correct : LegacyGcdU64Spec := by
  intro env initial a b hinit
  subst hinit
  -- `func2` is the exported wrapper: pushes both args and calls `func0`.
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64], [], func2, [.i64], none⟩) rfl
  unfold func2
  wp_run
  apply wp_call_tw (func0_terminates env a b)
  rintro st' vs rfl
  wp_run
  rfl

end Project.NumInteger.Spec
