import Project.FloatRound.Program
import CodeLib.IEEE32.Exec

/-!
# Specification for `float_round`

The exported `check_round` function tests whether the naive round
(trunc + compare frac) and optimized round (f32.nearest) agree.
They intentionally disagree on half-integers, so we only prove termination.
-/

namespace Project.FloatRound.Spec

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SmallStep
open Wasm.SepLogic

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000

/-! ## Authoritative exported footprint -/

def roundHeap : WasmHeapMap (Option UInt8) :=
  store32Heap
    (store32Heap (store32Heap ∅ 0 1048540 0) 0 1048556 0)
    0 1048572 0

def roundMem (memory : Mem) : Mem :=
  ((memory.write32 1048540 0).write32 1048556 0).write32 1048572 0

theorem round_initialMem_eq :
    roundMem («module».initialStore : Store Unit).mem =
      («module».initialStore : Store Unit).mem := by
  simp [roundMem, «module», Module.initialStore, Mem.write32, Mem.empty]

def checkRoundConfig (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func6, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

theorem roundHeap_agrees :
    heapAgreesWithMem roundHeap (storeResolve (checkRoundConfig 0).store) := by
  unfold roundHeap
  have h := store32_sound0 (store32Heap (store32Heap ∅ 0 1048540 0) 0 1048556 0)
      ((«module».initialStore : Store Unit).mem.write32 1048540 0 |>.write32 1048556 0)
      1048572 0 (by decide) (by decide) (by decide)
      (store32_sound0 (store32Heap ∅ 0 1048540 0)
          ((«module».initialStore : Store Unit).mem.write32 1048540 0)
          1048556 0 (by decide) (by decide) (by decide)
          (store32_sound0 ∅
              («module».initialStore : Store Unit).mem
              1048540 0 (by decide) (by decide) (by decide)
              (heapAgreesWithMem_empty _)))
  rw [show (((«module».initialStore : Store Unit).mem.write32 1048540 0).write32 1048556 0).write32 1048572 0
      = («module».initialStore : Store Unit).mem from by
    have hrm := round_initialMem_eq
    unfold roundMem at hrm
    exact hrm] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (checkRoundConfig 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, checkRoundConfig]
    · simp [h0, storeResolve, checkRoundConfig,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

theorem roundHeap_inBounds :
    heapAddressesInBounds roundHeap (storeResolve (checkRoundConfig 0).store) := by
  unfold roundHeap
  have h := store32_inBounds0 (store32Heap (store32Heap ∅ 0 1048540 0) 0 1048556 0)
      ((«module».initialStore : Store Unit).mem.write32 1048540 0 |>.write32 1048556 0)
      1048572 0 (by decide) (by decide) (by decide) (by decide)
      (store32_inBounds0 (store32Heap ∅ 0 1048540 0)
          ((«module».initialStore : Store Unit).mem.write32 1048540 0)
          1048556 0 (by decide) (by decide) (by decide) (by decide)
          (store32_inBounds0 ∅
              («module».initialStore : Store Unit).mem
              1048540 0 (by decide) (by decide) (by decide) (by decide)
              (heapAddressesInBounds_empty _)))
  rw [show (((«module».initialStore : Store Unit).mem.write32 1048540 0).write32 1048556 0).write32 1048572 0
      = («module».initialStore : Store Unit).mem from by
    have hrm := round_initialMem_eq
    unfold roundMem at hrm
    exact hrm] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (checkRoundConfig 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, checkRoundConfig]
    · simp [h0, storeResolve, checkRoundConfig,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

def roundGlobals : WasmGlobalMap Value :=
  insert ∅ ⟨0, 0⟩ (.i32 1048576)

theorem roundGlobals_agree :
    globalHeapAgrees roundGlobals
      («module».initialStore : Store Unit).globals := by
  intro index value hget
  simp only [roundGlobals] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (show (⟨0, 0⟩ : GlobalKey) ≠ ⟨0, index⟩ from fun h => hindex (congrArg GlobalKey.index h).symm), get?_empty] at hget
    contradiction

theorem roundHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ roundHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 1048540 0 ∗
        pointsTo_u32 0 1048556 0 ∗ pointsTo_u32 0 1048572 0 := by
  unfold roundHeap
  iintro Hheap
  ihave Houter := store32Heap_pointsTo
    (store32Heap (store32Heap ∅ 0 1048540 0) 0 1048556 0)
    0 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Houter with ⟨Houter, Hheap⟩
  ihave Hmiddle := store32Heap_pointsTo
    (store32Heap ∅ 0 1048540 0) 0 1048556 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hmiddle with ⟨Hmiddle, Hheap⟩
  ihave Hinner := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 1048540 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hinner with ⟨Hinner, Hempty⟩
  iframe

theorem roundGlobals_pointsTo [WasmGlobalGS Unit] :
    ([∗map] index ↦ value ∈ roundGlobals,
      globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576) := by
  unfold roundGlobals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  simp only [globalPointsToAt_eq]
  rfl

/-! ## Small-step optimized-round path -/

theorem func5_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Nearest x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048544], [.f32 (f32Nearest x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func5, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func5]
  iapply wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply wp_const
  inext
  iapply wp_sub
  inext
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  iapply wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · inext
    rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Nearest x) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load (f32Nearest x)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Nearest x) =
        pointsTo_u32 0 1048556 (f32Nearest x) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Nearest x)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Nearest x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func4_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Nearest x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (f32Nearest x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func4, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func4]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func5_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»)) x oldWord _ _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit' $$ Hruntime
    inext
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    iapply hreturn
    iframe
  · iframe

theorem deepFrameFloat_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (instruction : Instruction) (result : UInt32)
    (hzero : evalScalarFloat0? instruction = none)
    (heval :
      evalScalarFloat1? instruction (.f32 x) = some (.f32 result))
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 result ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 1,
          .localGet 1, .localGet 0, instruction, .f32Store 12,
          .localGet 1, .f32Load 12, .ret ],
        1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  iapply wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply wp_const
  inext
  iapply wp_sub
  inext
  rw [show (1048544 : UInt32) - 16 = 1048528 by decide]
  iapply wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 hzero heval
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048528 : UInt32) + 12) oldWord $$ [Hword]
  · inext
    rw [show (1048528 : UInt32) + 12 = 1048540 by decide]
    iexact Hword
  iapply wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048528 : UInt32) + 12) result $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load result
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048528 : UInt32) + 12) result =
        pointsTo_u32 0 1048540 result :=
    congrArg (fun address => pointsTo_u32 0 address result) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048540 result $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func1_deep_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Trunc x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simpa only [func1] using
    (deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Trunc (f32Trunc x) rfl rfl calls hreturn)

theorem func2_deep_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Ceil x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Ceil x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func2, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simpa only [func2] using
    (deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Ceil (f32Ceil x) rfl rfl calls hreturn)

theorem func3_deep_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Floor x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Floor x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func3, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simpa only [func3] using
    (deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Floor (f32Floor x) rfl rfl calls hreturn)

/-! ## Small-step naive-round control machine -/

def naiveTailProg : Program :=
  [ .localGet 1, .f32Load 12, .localSet 4,
    .localGet 1, .const 16, .add, .globalSet 0,
    .localGet 4, .ret ]

def naiveFloorProg : Program :=
  [ .localGet 1, .localGet 2, .call 3, .f32Store 12 ]

def naiveStoreTruncProg : Program :=
  [.localGet 1, .localGet 2, .f32Store 12, .br 1]

def naiveCeilProg : Program :=
  [ .localGet 1, .localGet 2, .call 2, .f32Store 12, .br 2 ]

def naiveCompareProg : Program :=
  [ .localGet 3, .f32Const 1056964608, .f32Ge,
    .const 1, .and, .br_if 0,
    .localGet 3, .f32Const 3204448256, .f32Le,
    .const 1, .and, .br_if 2, .br 1 ]

def naiveRoundResult (x : UInt32) : UInt32 :=
  let truncated := f32Trunc x
  let fraction := f32Sub x truncated
  if f32Ge fraction 1056964608 then
    f32Ceil truncated
  else if f32Le fraction 3204448256 then
    f32Floor truncated
  else
    truncated

def naiveCBody : Program :=
  [.block 0 0 naiveCompareProg] ++ naiveCeilProg

def naiveBBody : Program :=
  [.block 0 0 naiveCBody] ++ naiveStoreTruncProg

def naiveABody : Program :=
  [.block 0 0 naiveBBody] ++ naiveFloorProg

def naiveAFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := naiveABody
    continuation := naiveTailProg
    belowStack := [] }

def naiveBFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := naiveBBody
    continuation := naiveFloorProg
    belowStack := [] }

def naiveCFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := naiveCBody
    continuation := naiveStoreTruncProg
    belowStack := [] }

def naiveDFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := naiveCompareProg
    continuation := naiveCeilProg
    belowStack := [] }

theorem naive_tail_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 result ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 result],
            [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048556 result ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveTailProg, 1, [], [], calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [naiveTailProg]
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) result $$ [Hword]
  · inext
    rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply wp_f32Load result
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_add
  inext
  rw [show (16 : UInt32) + 1048544 = 1048560 by decide]
  ihave HglobalLater :
      ▷ globalPointsToAt 0 0 (.i32 1048544) $$ [Hglobal]
  · inext
    iexact Hglobal
  iapply wp_globalSet $$ HglobalLater
  inext
  iintro Hglobal
  iapply wp_localGet rfl
  inext
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) result =
        pointsTo_u32 0 1048556 result :=
    congrArg (fun address => pointsTo_u32 0 address result) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 result $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem naive_storeTrunc_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048556 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveStoreTruncProg, 1, [],
        [naiveBFrame, naiveAFrame], calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [naiveStoreTruncProg]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · inext
    rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_br rfl
  inext
  simp only [naiveAFrame, List.take, List.nil_append]
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Trunc x) =
        pointsTo_u32 0 1048556 (f32Trunc x) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Trunc x)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Trunc x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hnext
  iframe

theorem naive_ceil_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Ceil (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveCeilProg, 1, [],
        [naiveCFrame, naiveBFrame, naiveAFrame], calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [naiveCeilProg]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 2 func2Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func2Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func2_deep_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 1048556 oldWord))
    (f32Trunc x) oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply wp_returnFromCallExplicit' $$ Hruntime
    inext
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    ihave HwordLater :
        ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
    · inext
      rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
      iexact Hword
    iapply wp_f32Store oldWord
      (by decide) (by decide) (by decide) (by decide) $$ HwordLater
    inext
    iintro Hword
    iapply wp_br rfl
    inext
    simp only [naiveAFrame, List.take, List.nil_append]
    have hWordProp :
        pointsTo_u32 0 ((1048544 : UInt32) + 12)
            (f32Ceil (f32Trunc x)) =
          pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) :=
      congrArg
        (fun address => pointsTo_u32 0 address (f32Ceil (f32Trunc x)))
        (by decide)
    ihave HwordExact :
        pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) $$ [Hword]
    · rw [← hWordProp]
      iexact Hword
    iapply hnext
    iframe
  · iframe

theorem naive_floor_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Floor (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveFloorProg, 1, [], [naiveAFrame], calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [naiveFloorProg]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func3_deep_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 1048556 oldWord))
    (f32Trunc x) oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply wp_returnFromCallExplicit' $$ Hruntime
    inext
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    ihave HwordLater :
        ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
    · inext
      rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
      iexact Hword
    iapply wp_f32Store oldWord
      (by decide) (by decide) (by decide) (by decide) $$ HwordLater
    inext
    iintro Hword
    iapply wp_exitControl rfl
    inext
    simp only [naiveAFrame, List.take, List.nil_append]
    have hWordProp :
        pointsTo_u32 0 ((1048544 : UInt32) + 12)
            (f32Floor (f32Trunc x)) =
          pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) :=
      congrArg
        (fun address => pointsTo_u32 0 address (f32Floor (f32Trunc x)))
        (by decide)
    ihave HwordExact :
        pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) $$ [Hword]
    · rw [← hWordProp]
      iexact Hword
    iapply hnext
    iframe
  · iframe

theorem naive_compare_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hceil :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Ceil (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hfloor :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Floor (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (htrunc :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        pointsTo_u32 0 1048540 oldDeep ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048556 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveCompareProg, 1, [],
        [naiveDFrame, naiveCFrame, naiveBFrame, naiveAFrame], calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [naiveCompareProg]
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat0 rfl
  inext
  by_cases hge :
      f32Ge (f32Sub x (f32Trunc x)) 1056964608 = true
  · iapply wp_scalarFloat2 (value := .i32 1) rfl rfl
      (by simp [evalScalarFloat2?, hge])
    inext
    iapply wp_const
    inext
    iapply wp_and
    inext
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    iapply wp_brIf (by decide) rfl
    inext
    simp only [naiveDFrame, List.take, List.nil_append]
    iapply naive_ceil_smallStep_wp R x oldDeep oldWord calls _
    · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
      iapply hceil
      iframe
    · iframe
  · have hgeFalse :
        f32Ge (f32Sub x (f32Trunc x)) 1056964608 = false := by
      cases h : f32Ge (f32Sub x (f32Trunc x)) 1056964608 <;> simp_all
    iapply wp_scalarFloat2 (value := .i32 0) rfl rfl
      (by simp [evalScalarFloat2?, hgeFalse])
    inext
    iapply wp_const
    inext
    iapply wp_and
    inext
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    iapply wp_brIfZero
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_scalarFloat0 rfl
    inext
    by_cases hle :
        f32Le (f32Sub x (f32Trunc x)) 3204448256 = true
    · iapply wp_scalarFloat2 (value := .i32 1) rfl rfl
        (by simp [evalScalarFloat2?, hle])
      inext
      iapply wp_const
      inext
      iapply wp_and
      inext
      rw [show (1 &&& 1 : UInt32) = 1 by decide]
      iapply wp_brIf (by decide) rfl
      inext
      simp only [naiveBFrame, List.take, List.nil_append]
      iapply naive_floor_smallStep_wp R x oldDeep oldWord calls _
      · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
        iapply hfloor
        iframe
      · iframe
    · have hleFalse :
          f32Le (f32Sub x (f32Trunc x)) 3204448256 = false := by
        cases h : f32Le (f32Sub x (f32Trunc x)) 3204448256 <;> simp_all
      iapply wp_scalarFloat2 (value := .i32 0) rfl rfl
        (by simp [evalScalarFloat2?, hleFalse])
      inext
      iapply wp_const
      inext
      iapply wp_and
      inext
      rw [show (0 &&& 1 : UInt32) = 0 by decide]
      iapply wp_brIfZero
      inext
      iapply wp_br rfl
      inext
      simp only [naiveCFrame, List.take, List.nil_append]
      iapply naive_storeTrunc_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 oldDeep))
        x oldWord calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply htrunc
        iframe
      · iframe

theorem func0_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn : ∀ result : UInt32,
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048540 result ∗
        pointsTo_u32 0 1048556 result ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)),
              .f32 result],
            [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0, .f32 0, .f32 0, .f32 0], []⟩,
        func0, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [func0]
  iapply wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply wp_const
  inext
  iapply wp_sub
  inext
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  iapply wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply wp_localGet rfl
  inext
  ihave HglobalLater : ▷ globalPointsToAt 0 0 (.i32 1048560) $$ [Hglobal]
  · inext
    iexact Hglobal
  iapply wp_globalSet $$ HglobalLater
  inext
  iintro Hglobal
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func1_deep_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 1048556 oldWord))
    x oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply wp_returnFromCallExplicit' $$ Hruntime
    inext
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    iapply wp_localSet rfl
    inext
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.set]
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_scalarFloat2 rfl rfl rfl
    inext
    iapply wp_localSet rfl
    inext
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.set]
    rw [← show naiveCompareProg =
      [ .localGet 3, .f32Const 1056964608, .f32Ge,
        .const 1, .and, .br_if 0,
        .localGet 3, .f32Const 3204448256, .f32Le,
        .const 1, .and, .br_if 2, .br 1 ] by rfl]
    rw [← show naiveCeilProg =
      [ .localGet 1, .localGet 2, .call 2, .f32Store 12, .br 2 ] by rfl]
    rw [← show naiveCBody =
      .block 0 0 naiveCompareProg :: naiveCeilProg by rfl]
    rw [← show naiveStoreTruncProg =
      [.localGet 1, .localGet 2, .f32Store 12, .br 1] by rfl]
    rw [← show naiveBBody =
      .block 0 0 naiveCBody :: naiveStoreTruncProg by rfl]
    rw [← show naiveFloorProg =
      [.localGet 1, .localGet 2, .call 3, .f32Store 12] by rfl]
    rw [← show naiveABody =
      .block 0 0 naiveBBody :: naiveFloorProg by rfl]
    rw [← show naiveTailProg =
      [ .localGet 1, .f32Load 12, .localSet 4,
        .localGet 1, .const 16, .add, .globalSet 0,
        .localGet 4, .ret ] by rfl]
    iapply wp_block
    inext
    rw (occs := .pos [1]) [show naiveABody =
      (.block 0 0 naiveBBody :: naiveFloorProg) by rfl]
    iapply wp_block
    inext
    rw (occs := .pos [1]) [show naiveBBody =
      (.block 0 0 naiveCBody :: naiveStoreTruncProg) by rfl]
    iapply wp_block
    inext
    rw (occs := .pos [1]) [show naiveCBody =
      (.block 0 0 naiveCompareProg :: naiveCeilProg) by rfl]
    iapply wp_block
    inext
    simp only [List.drop_zero]
    rw [← show naiveDFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveCompareProg, continuation := naiveCeilProg
        belowStack := [] } by rfl]
    rw [← show naiveCFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveCBody, continuation := naiveStoreTruncProg
        belowStack := [] } by rfl]
    rw [← show naiveBFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveBBody, continuation := naiveFloorProg
        belowStack := [] } by rfl]
    rw [← show naiveAFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveABody, continuation := naiveTailProg
        belowStack := [] } by rfl]
    iapply naive_compare_smallStep_wp
      R x (f32Trunc x) oldWord calls _ _ _
    · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
      iapply naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 (f32Ceil (f32Trunc x))))
        x (f32Ceil (f32Trunc x)) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Ceil (f32Trunc x))
        iframe
      · iframe
    · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
      iapply naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 (f32Floor (f32Trunc x))))
        x (f32Floor (f32Trunc x)) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Floor (f32Trunc x))
        iframe
      · iframe
    · iintro ⟨HR, Hruntime, Hdeep, Hglobal, Hword⟩
      iapply naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 (f32Trunc x)))
        x (f32Trunc x) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Trunc x)
        iframe
      · iframe
    · iframe
  · iframe

/-! ## Exported agreement check -/

def roundCheckTailProg : Program :=
  [ .localGet 1, .load32 12, .localSet 2,
    .localGet 1, .const 16, .add, .globalSet 0,
    .localGet 2, .ret ]

def roundCheckInnerBody : Program :=
  [ .localGet 0, .call 0, .localGet 0, .call 4,
    .f32Eq, .const 1, .and, .br_if 0,
    .localGet 1, .const 0, .store32 12, .br 1 ]

def roundCheckOneProg : Program :=
  [.localGet 1, .const 1, .store32 12]

def roundCheckOuterBody : Program :=
  [.block 0 0 roundCheckInnerBody] ++ roundCheckOneProg

def roundCheckOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := roundCheckOuterBody
    continuation := roundCheckTailProg
    belowStack := [] }

def roundCheckInnerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := roundCheckInnerBody
    continuation := roundCheckOneProg
    belowStack := [] }

theorem roundCheck_tail_result_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        roundCheckTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [roundCheckTailProg]
  iapply wp_localGet rfl
  inext
  ihave HresultLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) result $$ [Hresult]
  · inext
    rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hresult
  iapply wp_load32 result
    (by decide) (by decide) (by decide) (by decide) $$ HresultLater
  inext
  iintro Hresult
  iapply wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_add
  inext
  rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
  ihave HglobalLater :
      ▷ globalPointsToAt 0 0 (.i32 1048560) $$ [Hglobal]
  · inext
    iexact Hglobal
  iapply wp_globalSet $$ HglobalLater
  inext
  iintro Hglobal
  iapply wp_localGet rfl
  inext
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  iclear HR Hglobal Hresult
  ipureintro
  exact ⟨result, rfl⟩

theorem roundCheck_comparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x oldDeep oldWord oldResult : UInt32)
    (hzero : ∀ deep word : UInt32,
      pointsTo_u32 0 1048540 deep ∗ pointsTo_u32 0 1048556 word ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          roundCheckTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone : ∀ deep word : UInt32,
      pointsTo_u32 0 1048540 deep ∗ pointsTo_u32 0 1048556 word ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          roundCheckTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        roundCheckInnerBody, 1, [],
        [roundCheckInnerFrame, roundCheckOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hdeep, Hword, Hruntime, Hglobal, Hresult⟩
  simp only [roundCheckInnerBody]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048572 oldResult))
    x oldDeep oldWord _ _
  · intro naive
    iintro ⟨Hresult, Hruntime, Hglobal, Hdeep, Hword⟩
    iapply wp_returnFromCallExplicit' $$ Hruntime
    inext
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    iapply wp_localGet rfl
    inext
    iapply wp_call «module» 4 func4Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func4Def, Function.toLocals, Function.numParams]
    iapply func4_lowered_smallStep_wp
      (iprop(pointsTo_u32 0 1048540 naive ∗
        pointsTo_u32 0 1048572 oldResult))
      x naive _ _
    · iintro ⟨⟨Hdeep, Hresult⟩, Hruntime, Hglobal, Hword⟩
      iapply wp_returnFromCallExplicit' $$ Hruntime
      inext
      iintro Hruntime
      simp only [List.take, List.singleton_append]
      by_cases heq : f32Eq naive (f32Nearest x) = true
      · iapply wp_scalarFloat2 (value := .i32 1) rfl rfl
          (by simp [evalScalarFloat2?, heq])
        inext
        iapply wp_const
        inext
        iapply wp_and
        inext
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        iapply wp_brIf (by decide) rfl
        inext
        simp only [roundCheckInnerFrame, List.take, List.nil_append]
        simp only [roundCheckOneProg]
        iapply wp_localGet rfl
        inext
        iapply wp_const
        inext
        ihave HresultLater :
            ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · inext
          rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
          iexact Hresult
        iapply wp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ HresultLater
        inext
        iintro Hresult
        iapply wp_exitControl rfl
        inext
        simp only [roundCheckOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 1 =
              pointsTo_u32 0 1048572 1 :=
          congrArg (fun address => pointsTo_u32 0 address 1) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 1 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply hone naive (f32Nearest x)
        iframe
      · have heqFalse : f32Eq naive (f32Nearest x) = false := by
          cases h : f32Eq naive (f32Nearest x) <;> simp_all
        iapply wp_scalarFloat2 (value := .i32 0) rfl rfl
          (by simp [evalScalarFloat2?, heqFalse])
        inext
        iapply wp_const
        inext
        iapply wp_and
        inext
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        iapply wp_brIfZero
        inext
        iapply wp_localGet rfl
        inext
        iapply wp_const
        inext
        ihave HresultLater :
            ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · inext
          rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
          iexact Hresult
        iapply wp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ HresultLater
        inext
        iintro Hresult
        iapply wp_br rfl
        inext
        simp only [roundCheckOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 0 =
              pointsTo_u32 0 1048572 0 :=
          congrArg (fun address => pointsTo_u32 0 address 0) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 0 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply hzero naive (f32Nearest x)
        iframe
    · iframe
  · iframe

theorem func6_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u32 0 1048540 0 ∗ pointsTo_u32 0 1048556 0 ∗
      pointsTo_u32 0 1048572 0 ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func6, 1, [], [], []⟩ : Expr Unit) @ s; E
      {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨Hdeep, Hword, Hresult, Hruntime, Hglobal⟩
  simp only [func6]
  iapply wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply wp_const
  inext
  iapply wp_sub
  inext
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  iapply wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply wp_localGet rfl
  inext
  ihave HglobalLater : ▷ globalPointsToAt 0 0 (.i32 1048576) $$ [Hglobal]
  · inext
    iexact Hglobal
  iapply wp_globalSet $$ HglobalLater
  inext
  iintro Hglobal
  rw [← show roundCheckInnerBody =
    [ .localGet 0, .call 0, .localGet 0, .call 4,
      .f32Eq, .const 1, .and, .br_if 0,
      .localGet 1, .const 0, .store32 12, .br 1 ] by rfl]
  rw [← show roundCheckOneProg =
    [.localGet 1, .const 1, .store32 12] by rfl]
  rw [← show roundCheckOuterBody =
    .block 0 0 roundCheckInnerBody :: roundCheckOneProg by rfl]
  rw [← show roundCheckTailProg =
    [ .localGet 1, .load32 12, .localSet 2,
      .localGet 1, .const 16, .add, .globalSet 0,
      .localGet 2, .ret ] by rfl]
  iapply wp_block
  inext
  rw (occs := .pos [1]) [show roundCheckOuterBody =
    (.block 0 0 roundCheckInnerBody :: roundCheckOneProg) by rfl]
  iapply wp_block
  inext
  simp only [List.drop_zero]
  rw [← show roundCheckInnerFrame =
    { kind := .block, paramArity := 0, resultArity := 0
      body := roundCheckInnerBody, continuation := roundCheckOneProg
      belowStack := [] } by rfl]
  rw [← show roundCheckOuterFrame =
    { kind := .block, paramArity := 0, resultArity := 0
      body := roundCheckOuterBody, continuation := roundCheckTailProg
      belowStack := [] } by rfl]
  iapply roundCheck_comparison_smallStep_wp
    (s := s) (E := E) x 0 0 0 _ _
  · intro deep word
    iintro ⟨Hdeep, Hword, Hruntime, Hglobal, Hresult⟩
    iapply roundCheck_tail_result_smallStep_wp
      (iprop(pointsTo_u32 0 1048540 deep ∗
        pointsTo_u32 0 1048556 word ∗ runtimeModuleOwn ⟨0⟩ «module»))
      x 0
    iframe
  · intro deep word
    iintro ⟨Hdeep, Hword, Hruntime, Hglobal, Hresult⟩
    iapply roundCheck_tail_result_smallStep_wp
      (iprop(pointsTo_u32 0 1048540 deep ∗
        pointsTo_u32 0 1048556 word ∗ runtimeModuleOwn ⟨0⟩ «module»))
      x 1
    iframe
  · iframe

theorem checkRound_smallStep (x : UInt32) :
    PartiallyMeets (checkRoundConfig x)
      (fun values _store => ∃ b : UInt32, values = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
      (α := Unit) (σ := roundHeap) (globalσ := roundGlobals)
      (φ := fun values => ∃ b : UInt32, values = [.i32 b])
  · simpa [checkRoundConfig] using roundHeap_agrees
  · simpa [checkRoundConfig] using roundHeap_inBounds
  · simpa [checkRoundConfig] using roundGlobals_agree
  · simp only [checkRoundConfig]; decide
  · intro gs
    simp only [checkRoundConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := roundHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hdeep, Hword, Hresult⟩
    ihave Hglobal := roundGlobals_pointsTo $$ Hglobals
    iapply func6_body_smallStep_wp
    iframe

/-! ## Total WP helpers (no `▷` on continuations) -/

theorem twp_func5_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Nearest x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048544], [.f32 (f32Nearest x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func5, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func5]
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_scalarFloat1 rfl rfl
  ihave Hword' : pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply twp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword
  iapply twp_localGet rfl
  iapply twp_f32Load (f32Nearest x)
    (by decide) (by decide) (by decide) (by decide) $$ Hword
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Nearest x) =
        pointsTo_u32 0 1048556 (f32Nearest x) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Nearest x)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Nearest x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem twp_func4_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Nearest x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (f32Nearest x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func4, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func4]
  iapply twp_localGet rfl
  iapply twp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func5_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»)) x oldWord _ _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    iapply twp_returnFromCallExplicit $$ Hruntime
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    iapply hreturn
    iframe
  · iframe

theorem twp_deepFrameFloat_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (instruction : Instruction) (result : UInt32)
    (hzero : evalScalarFloat0? instruction = none)
    (heval : evalScalarFloat1? instruction (.f32 x) = some (.f32 result))
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 result ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 1,
          .localGet 1, .localGet 0, instruction, .f32Store 12,
          .localGet 1, .f32Load 12, .ret ],
        1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  rw [show (1048544 : UInt32) - 16 = 1048528 by decide]
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_scalarFloat1 hzero heval
  ihave Hword' : pointsTo_u32 0 ((1048528 : UInt32) + 12) oldWord $$ [Hword]
  · rw [show (1048528 : UInt32) + 12 = 1048540 by decide]
    iexact Hword
  iapply twp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword
  iapply twp_localGet rfl
  iapply twp_f32Load result
    (by decide) (by decide) (by decide) (by decide) $$ Hword
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048528 : UInt32) + 12) result =
        pointsTo_u32 0 1048540 result :=
    congrArg (fun address => pointsTo_u32 0 address result) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048540 result $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem twp_func1_deep_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Trunc x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  simpa only [func1] using
    (twp_deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Trunc (f32Trunc x) rfl rfl calls hreturn)

theorem twp_func2_deep_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Ceil x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Ceil x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func2, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  simpa only [func2] using
    (twp_deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Ceil (f32Ceil x) rfl rfl calls hreturn)

theorem twp_func3_deep_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Floor x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Floor x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func3, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  simpa only [func3] using
    (twp_deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Floor (f32Floor x) rfl rfl calls hreturn)

theorem twp_naive_tail_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 result ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 result],
            [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048556 result ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveTailProg, 1, [], [], calls⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [naiveTailProg]
  iapply twp_localGet rfl
  ihave Hword' : pointsTo_u32 0 ((1048544 : UInt32) + 12) result $$ [Hword]
  · rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply twp_f32Load result
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (16 : UInt32) + 1048544 = 1048560 by decide]
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) result =
        pointsTo_u32 0 1048556 result :=
    congrArg (fun address => pointsTo_u32 0 address result) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 result $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem twp_naive_storeTrunc_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048556 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveStoreTruncProg, 1, [],
        [naiveBFrame, naiveAFrame], calls⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [naiveStoreTruncProg]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hword' : pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply twp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword
  iapply twp_br rfl
  simp only [naiveAFrame, List.take, List.nil_append]
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Trunc x) =
        pointsTo_u32 0 1048556 (f32Trunc x) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Trunc x)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Trunc x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hnext
  iframe

theorem twp_naive_ceil_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Ceil (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveCeilProg, 1, [],
        [naiveCFrame, naiveBFrame, naiveAFrame], calls⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [naiveCeilProg]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_call «module» 2 func2Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func2Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func2_deep_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 1048556 oldWord))
    (f32Trunc x) oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply twp_returnFromCallExplicit $$ Hruntime
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    ihave Hword' : pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
    · rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
      iexact Hword
    iapply twp_f32Store oldWord
      (by decide) (by decide) (by decide) (by decide) $$ Hword'
    iintro Hword
    iapply twp_br rfl
    simp only [naiveAFrame, List.take, List.nil_append]
    have hWordProp :
        pointsTo_u32 0 ((1048544 : UInt32) + 12)
            (f32Ceil (f32Trunc x)) =
          pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) :=
      congrArg
        (fun address => pointsTo_u32 0 address (f32Ceil (f32Trunc x)))
        (by decide)
    ihave HwordExact :
        pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) $$ [Hword]
    · rw [← hWordProp]
      iexact Hword
    iapply hnext
    iframe
  · iframe

theorem twp_naive_floor_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Floor (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveFloorProg, 1, [], [naiveAFrame], calls⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [naiveFloorProg]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func3_deep_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 1048556 oldWord))
    (f32Trunc x) oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply twp_returnFromCallExplicit $$ Hruntime
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    ihave Hword' : pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
    · rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
      iexact Hword
    iapply twp_f32Store oldWord
      (by decide) (by decide) (by decide) (by decide) $$ Hword'
    iintro Hword
    iapply twp_exitControl rfl
    simp only [naiveAFrame, List.take, List.nil_append]
    have hWordProp :
        pointsTo_u32 0 ((1048544 : UInt32) + 12)
            (f32Floor (f32Trunc x)) =
          pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) :=
      congrArg
        (fun address => pointsTo_u32 0 address (f32Floor (f32Trunc x)))
        (by decide)
    ihave HwordExact :
        pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) $$ [Hword]
    · rw [← hWordProp]
      iexact Hword
    iapply hnext
    iframe
  · iframe

theorem twp_naive_compare_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hceil :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Ceil (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Ceil (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hfloor :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048540 (f32Floor (f32Trunc x)) ∗
        pointsTo_u32 0 1048556 (f32Floor (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (htrunc :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        pointsTo_u32 0 1048540 oldDeep ∗
        globalPointsToAt 0 0 (.i32 1048544) ∗
        pointsTo_u32 0 1048556 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x],
          [.i32 1048544, .f32 (f32Trunc x),
            .f32 (f32Sub x (f32Trunc x)), .f32 0],
          []⟩,
        naiveCompareProg, 1, [],
        [naiveDFrame, naiveCFrame, naiveBFrame, naiveAFrame], calls⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [naiveCompareProg]
  iapply twp_localGet rfl
  iapply twp_scalarFloat0 rfl
  by_cases hge :
      f32Ge (f32Sub x (f32Trunc x)) 1056964608 = true
  · iapply twp_scalarFloat2 (value := .i32 1) rfl rfl
      (by simp [evalScalarFloat2?, hge])
    iapply twp_const
    iapply twp_and
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    iapply twp_brIf (by decide) rfl
    simp only [naiveDFrame, List.take, List.nil_append]
    iapply twp_naive_ceil_smallStep_wp R x oldDeep oldWord calls _
    · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
      iapply hceil
      iframe
    · iframe
  · have hgeFalse :
        f32Ge (f32Sub x (f32Trunc x)) 1056964608 = false := by
      cases h : f32Ge (f32Sub x (f32Trunc x)) 1056964608 <;> simp_all
    iapply twp_scalarFloat2 (value := .i32 0) rfl rfl
      (by simp [evalScalarFloat2?, hgeFalse])
    iapply twp_const
    iapply twp_and
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    iapply twp_brIfZero
    iapply twp_localGet rfl
    iapply twp_scalarFloat0 rfl
    by_cases hle :
        f32Le (f32Sub x (f32Trunc x)) 3204448256 = true
    · iapply twp_scalarFloat2 (value := .i32 1) rfl rfl
        (by simp [evalScalarFloat2?, hle])
      iapply twp_const
      iapply twp_and
      rw [show (1 &&& 1 : UInt32) = 1 by decide]
      iapply twp_brIf (by decide) rfl
      simp only [naiveBFrame, List.take, List.nil_append]
      iapply twp_naive_floor_smallStep_wp R x oldDeep oldWord calls _
      · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
        iapply hfloor
        iframe
      · iframe
    · have hleFalse :
          f32Le (f32Sub x (f32Trunc x)) 3204448256 = false := by
        cases h : f32Le (f32Sub x (f32Trunc x)) 3204448256 <;> simp_all
      iapply twp_scalarFloat2 (value := .i32 0) rfl rfl
        (by simp [evalScalarFloat2?, hleFalse])
      iapply twp_const
      iapply twp_and
      rw [show (0 &&& 1 : UInt32) = 0 by decide]
      iapply twp_brIfZero
      iapply twp_br rfl
      simp only [naiveCFrame, List.take, List.nil_append]
      iapply twp_naive_storeTrunc_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 oldDeep))
        x oldWord calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply htrunc
        iframe
      · iframe

theorem twp_func0_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn : ∀ result : UInt32,
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048540 result ∗
        pointsTo_u32 0 1048556 result ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)),
              .f32 result],
            [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0, .f32 0, .f32 0, .f32 0], []⟩,
        func0, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
  simp only [func0]
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func1_deep_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsTo_u32 0 1048556 oldWord))
    x oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply twp_returnFromCallExplicit $$ Hruntime
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    iapply twp_localSet rfl
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_scalarFloat2 rfl rfl rfl
    iapply twp_localSet rfl
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
    rw [← show naiveCompareProg =
      [ .localGet 3, .f32Const 1056964608, .f32Ge,
        .const 1, .and, .br_if 0,
        .localGet 3, .f32Const 3204448256, .f32Le,
        .const 1, .and, .br_if 2, .br 1 ] by rfl]
    rw [← show naiveCeilProg =
      [ .localGet 1, .localGet 2, .call 2, .f32Store 12, .br 2 ] by rfl]
    rw [← show naiveCBody =
      .block 0 0 naiveCompareProg :: naiveCeilProg by rfl]
    rw [← show naiveStoreTruncProg =
      [.localGet 1, .localGet 2, .f32Store 12, .br 1] by rfl]
    rw [← show naiveBBody =
      .block 0 0 naiveCBody :: naiveStoreTruncProg by rfl]
    rw [← show naiveFloorProg =
      [.localGet 1, .localGet 2, .call 3, .f32Store 12] by rfl]
    rw [← show naiveABody =
      .block 0 0 naiveBBody :: naiveFloorProg by rfl]
    rw [← show naiveTailProg =
      [ .localGet 1, .f32Load 12, .localSet 4,
        .localGet 1, .const 16, .add, .globalSet 0,
        .localGet 4, .ret ] by rfl]
    iapply twp_block
    rw (occs := .pos [1]) [show naiveABody =
      (.block 0 0 naiveBBody :: naiveFloorProg) by rfl]
    iapply twp_block
    rw (occs := .pos [1]) [show naiveBBody =
      (.block 0 0 naiveCBody :: naiveStoreTruncProg) by rfl]
    iapply twp_block
    rw (occs := .pos [1]) [show naiveCBody =
      (.block 0 0 naiveCompareProg :: naiveCeilProg) by rfl]
    iapply twp_block
    simp only [List.drop_zero]
    rw [← show naiveDFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveCompareProg, continuation := naiveCeilProg
        belowStack := [] } by rfl]
    rw [← show naiveCFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveCBody, continuation := naiveStoreTruncProg
        belowStack := [] } by rfl]
    rw [← show naiveBFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveBBody, continuation := naiveFloorProg
        belowStack := [] } by rfl]
    rw [← show naiveAFrame =
      { kind := .block, paramArity := 0, resultArity := 0
        body := naiveABody, continuation := naiveTailProg
        belowStack := [] } by rfl]
    iapply twp_naive_compare_smallStep_wp
      R x (f32Trunc x) oldWord calls _ _ _
    · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
      iapply twp_naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 (f32Ceil (f32Trunc x))))
        x (f32Ceil (f32Trunc x)) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Ceil (f32Trunc x))
        iframe
      · iframe
    · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
      iapply twp_naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 (f32Floor (f32Trunc x))))
        x (f32Floor (f32Trunc x)) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Floor (f32Trunc x))
        iframe
      · iframe
    · iintro ⟨HR, Hruntime, Hdeep, Hglobal, Hword⟩
      iapply twp_naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
          pointsTo_u32 0 1048540 (f32Trunc x)))
        x (f32Trunc x) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Trunc x)
        iframe
      · iframe
    · iframe
  · iframe

theorem twp_roundCheck_tail_result_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        roundCheckTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      [{ values, ∀ (store : MachineStore Unit) (_obs : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜∃ b : UInt32, values = [.i32 b]⌝ }] := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [roundCheckTailProg]
  iapply twp_localGet rfl
  ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) result $$ [Hresult]
  · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hresult
  iapply twp_load32 result
    (by decide) (by decide) (by decide) (by decide) $$ Hresult'
  iintro Hresult
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_returnFromFunction
  iapply twp.value rfl
  iintro %store %obs _Hstate
  iclear HR Hglobal Hresult
  ipureintro
  exact ⟨result, rfl⟩

theorem twp_roundCheck_comparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x oldDeep oldWord oldResult : UInt32)
    (hzero : ∀ deep word : UInt32,
      pointsTo_u32 0 1048540 deep ∗ pointsTo_u32 0 1048556 word ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          roundCheckTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hone : ∀ deep word : UInt32,
      pointsTo_u32 0 1048540 deep ∗ pointsTo_u32 0 1048556 word ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          roundCheckTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    pointsTo_u32 0 1048540 oldDeep ∗ pointsTo_u32 0 1048556 oldWord ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        roundCheckInnerBody, 1, [],
        [roundCheckInnerFrame, roundCheckOuterFrame], []⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨Hdeep, Hword, Hruntime, Hglobal, Hresult⟩
  simp only [roundCheckInnerBody]
  iapply twp_localGet rfl
  iapply twp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048572 oldResult))
    x oldDeep oldWord _ _
  · intro naive
    iintro ⟨Hresult, Hruntime, Hglobal, Hdeep, Hword⟩
    iapply twp_returnFromCallExplicit $$ Hruntime
    iintro Hruntime
    simp only [List.take, List.singleton_append]
    iapply twp_localGet rfl
    iapply twp_call «module» 4 func4Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    iintro Hruntime
    simp [func4Def, Function.toLocals, Function.numParams]
    iapply twp_func4_lowered_smallStep_wp
      (iprop(pointsTo_u32 0 1048540 naive ∗
        pointsTo_u32 0 1048572 oldResult))
      x naive _ _
    · iintro ⟨⟨Hdeep, Hresult⟩, Hruntime, Hglobal, Hword⟩
      iapply twp_returnFromCallExplicit $$ Hruntime
      iintro Hruntime
      simp only [List.take, List.singleton_append]
      by_cases heq : f32Eq naive (f32Nearest x) = true
      · iapply twp_scalarFloat2 (value := .i32 1) rfl rfl
          (by simp [evalScalarFloat2?, heq])
        iapply twp_const
        iapply twp_and
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        iapply twp_brIf (by decide) rfl
        simp only [roundCheckInnerFrame, List.take, List.nil_append]
        simp only [roundCheckOneProg]
        iapply twp_localGet rfl
        iapply twp_const
        ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
          iexact Hresult
        iapply twp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ Hresult'
        iintro Hresult
        iapply twp_exitControl rfl
        simp only [roundCheckOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 1 =
              pointsTo_u32 0 1048572 1 :=
          congrArg (fun address => pointsTo_u32 0 address 1) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 1 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply hone naive (f32Nearest x)
        iframe
      · have heqFalse : f32Eq naive (f32Nearest x) = false := by
          cases h : f32Eq naive (f32Nearest x) <;> simp_all
        iapply twp_scalarFloat2 (value := .i32 0) rfl rfl
          (by simp [evalScalarFloat2?, heqFalse])
        iapply twp_const
        iapply twp_and
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        iapply twp_brIfZero
        iapply twp_localGet rfl
        iapply twp_const
        ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
          iexact Hresult
        iapply twp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ Hresult'
        iintro Hresult
        iapply twp_br rfl
        simp only [roundCheckOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 0 =
              pointsTo_u32 0 1048572 0 :=
          congrArg (fun address => pointsTo_u32 0 address 0) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 0 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply hzero naive (f32Nearest x)
        iframe
    · iframe
  · iframe

theorem twp_func6_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u32 0 1048540 0 ∗ pointsTo_u32 0 1048556 0 ∗
      pointsTo_u32 0 1048572 0 ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func6, 1, [], [], []⟩ : Expr Unit) @ s; E
      [{ values, ∀ (store : MachineStore Unit) (_obs : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜∃ b : UInt32, values = [.i32 b]⌝ }] := by
  iintro ⟨Hdeep, Hword, Hresult, Hruntime, Hglobal⟩
  simp only [func6]
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  rw [← show roundCheckInnerBody =
    [ .localGet 0, .call 0, .localGet 0, .call 4,
      .f32Eq, .const 1, .and, .br_if 0,
      .localGet 1, .const 0, .store32 12, .br 1 ] by rfl]
  rw [← show roundCheckOneProg =
    [.localGet 1, .const 1, .store32 12] by rfl]
  rw [← show roundCheckOuterBody =
    .block 0 0 roundCheckInnerBody :: roundCheckOneProg by rfl]
  rw [← show roundCheckTailProg =
    [ .localGet 1, .load32 12, .localSet 2,
      .localGet 1, .const 16, .add, .globalSet 0,
      .localGet 2, .ret ] by rfl]
  iapply twp_block
  rw (occs := .pos [1]) [show roundCheckOuterBody =
    (.block 0 0 roundCheckInnerBody :: roundCheckOneProg) by rfl]
  iapply twp_block
  simp only [List.drop_zero]
  rw [← show roundCheckInnerFrame =
    { kind := .block, paramArity := 0, resultArity := 0
      body := roundCheckInnerBody, continuation := roundCheckOneProg
      belowStack := [] } by rfl]
  rw [← show roundCheckOuterFrame =
    { kind := .block, paramArity := 0, resultArity := 0
      body := roundCheckOuterBody, continuation := roundCheckTailProg
      belowStack := [] } by rfl]
  iapply twp_roundCheck_comparison_smallStep_wp
    (s := s) (E := E) x 0 0 0 _ _
  · intro deep word
    iintro ⟨Hdeep, Hword, Hruntime, Hglobal, Hresult⟩
    iapply twp_roundCheck_tail_result_smallStep_wp
      (iprop(pointsTo_u32 0 1048540 deep ∗
        pointsTo_u32 0 1048556 word ∗ runtimeModuleOwn ⟨0⟩ «module»))
      x 0
    iframe
  · intro deep word
    iintro ⟨Hdeep, Hword, Hruntime, Hglobal, Hresult⟩
    iapply twp_roundCheck_tail_result_smallStep_wp
      (iprop(pointsTo_u32 0 1048540 deep ∗
        pointsTo_u32 0 1048556 word ∗ runtimeModuleOwn ⟨0⟩ «module»))
      x 1
    iframe
  · iframe

theorem check_round_terminatesWith (x : UInt32) :
    Wasm.SmallStep.TerminatesWith (checkRoundConfig x)
      (fun rs _store => ∃ b : UInt32, rs = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_store_terminates
    (α := Unit)
    (σ := roundHeap) (globalσ := roundGlobals)
    (post := fun rs _store => ∃ b : UInt32, rs = [.i32 b])
  · simpa [checkRoundConfig] using roundHeap_agrees
  · simpa [checkRoundConfig] using roundHeap_inBounds
  · simpa [checkRoundConfig] using roundGlobals_agree
  · simp only [checkRoundConfig]; decide
  · intro _hlc _gs
    simp only [checkRoundConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := roundHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hdeep, Hword, Hresult⟩
    ihave Hglobal := roundGlobals_pointsTo $$ Hglobals
    iapply twp_func6_body_smallStep_wp
    iframe

/-! ## FloatRoundSpec -/

@[spec_of "rust-exported" "float_round::check_round"]
def FloatRoundSpec : Prop :=
  ∀ (x : UInt32),
    SmallStep.TerminatesWith (checkRoundConfig x)
      (fun rs _store => ∃ b : UInt32, rs = [.i32 b])

@[proves Project.FloatRound.Spec.FloatRoundSpec]
theorem check_round_correct : FloatRoundSpec := check_round_terminatesWith

end Project.FloatRound.Spec
