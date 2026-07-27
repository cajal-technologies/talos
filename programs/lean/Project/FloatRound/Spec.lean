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

private theorem emptyHeap_agrees (memory : Mem) :
    heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) memory := by
  intro address value hget
  rw [get?_empty] at hget
  contradiction

private theorem emptyHeap_inBounds (memory : Mem) :
    heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8)) memory := by
  intro address value hget
  rw [get?_empty] at hget
  contradiction

def roundHeap : WasmHeapMap (Option UInt8) :=
  store32Heap
    (store32Heap (store32Heap ∅ 1048540 0) 1048556 0)
    1048572 0

def roundMem (memory : Mem) : Mem :=
  ((memory.write32 1048540 0).write32 1048556 0).write32 1048572 0

theorem round_initialMem_eq :
    roundMem («module».initialStore : Store Unit).mem =
      («module».initialStore : Store Unit).mem := by
  simp [roundMem, «module», Module.initialStore, Mem.write32, Mem.empty]

theorem roundHeap_agrees :
    heapAgreesWithMem roundHeap
      («module».initialStore : Store Unit).mem := by
  rw [← round_initialMem_eq]
  unfold roundHeap roundMem
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  exact emptyHeap_agrees _

theorem roundHeap_inBounds :
    heapAddressesInBounds roundHeap
      («module».initialStore : Store Unit).mem := by
  rw [← round_initialMem_eq]
  unfold roundHeap roundMem
  apply store32_inBounds <;> try rfl
  · apply store32_inBounds <;> try rfl
    · apply store32_inBounds <;> try rfl
      · exact emptyHeap_inBounds _
      · decide
    · decide

def roundGlobals : WasmGlobalMap Value :=
  insert ∅ 0 (.i32 1048576)

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
  · rw [get?_insert_ne (Ne.symm hindex), get?_empty] at hget
    contradiction

theorem roundHeap_pointsTo [WasmHeapGS] :
    ([∗map] address ↦ value ∈ roundHeap,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 1048540 0 ∗
        pointsTo_u32 1048556 0 ∗ pointsTo_u32 1048572 0 := by
  unfold roundHeap
  iintro Hheap
  ihave Houter := store32Heap_pointsTo
    (store32Heap (store32Heap ∅ 1048540 0) 1048556 0)
    1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Houter with ⟨Houter, Hheap⟩
  ihave Hmiddle := store32Heap_pointsTo
    (store32Heap ∅ 1048540 0) 1048556 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hmiddle with ⟨Hmiddle, Hheap⟩
  ihave Hinner := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 1048540 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hinner with ⟨Hinner, Hempty⟩
  iframe

theorem roundGlobals_pointsTo [WasmGlobalGS] :
    ([∗map] index ↦ value ∈ roundGlobals,
      globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576) := by
  unfold roundGlobals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty 0)).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  exact .rfl

/-! ## Small-step optimized-round path -/

theorem func5_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048556 (f32Nearest x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048544], [.f32 (f32Nearest x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048556 oldWord ⊢
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
      ▷ pointsTo_u32 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
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
      ▷ pointsTo_u32 ((1048544 : UInt32) + 12) (f32Nearest x) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load (f32Nearest x)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 ((1048544 : UInt32) + 12) (f32Nearest x) =
        pointsTo_u32 1048556 (f32Nearest x) :=
    congrArg (fun address => pointsTo_u32 address (f32Nearest x)) (by decide)
  ihave HwordExact : pointsTo_u32 1048556 (f32Nearest x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func4_lowered_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048556 (f32Nearest x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (f32Nearest x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048556 oldWord ⊢
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
    (iprop(R ∗ runtimeModuleOwn «module»)) x oldWord _ _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply hreturn
    iframe
  · iframe

theorem deepFrameFloat_body_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldWord : UInt32)
    (instruction : Instruction) (result : UInt32)
    (hzero : evalScalarFloat0? instruction = none)
    (heval :
      evalScalarFloat1? instruction (.f32 x) = some (.f32 result))
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 result ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048540 oldWord ⊢
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
      ▷ pointsTo_u32 ((1048528 : UInt32) + 12) oldWord $$ [Hword]
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
      ▷ pointsTo_u32 ((1048528 : UInt32) + 12) result $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load result
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 ((1048528 : UInt32) + 12) result =
        pointsTo_u32 1048540 result :=
    congrArg (fun address => pointsTo_u32 address result) (by decide)
  ihave HwordExact : pointsTo_u32 1048540 result $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func1_deep_body_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Trunc x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simpa only [func1] using
    (deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Trunc (f32Trunc x) rfl rfl calls hreturn)

theorem func2_deep_body_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 (f32Ceil x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Ceil x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048540 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func2, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simpa only [func2] using
    (deepFrameFloat_body_smallStep_wp R x oldWord
      .f32Ceil (f32Ceil x) rfl rfl calls hreturn)

theorem func3_deep_body_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 (f32Floor x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048528], [.f32 (f32Floor x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048540 oldWord ⊢
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
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x result : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048556 result ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 result],
            [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048556 result ⊢
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
      ▷ pointsTo_u32 ((1048544 : UInt32) + 12) result $$ [Hword]
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
      ▷ globalPointsTo 0 (.i32 1048544) $$ [Hglobal]
  · inext
    iexact Hglobal
  iapply wp_globalSet $$ HglobalLater
  inext
  iintro Hglobal
  iapply wp_localGet rfl
  inext
  have hWordProp :
      pointsTo_u32 ((1048544 : UInt32) + 12) result =
        pointsTo_u32 1048556 result :=
    congrArg (fun address => pointsTo_u32 address result) (by decide)
  ihave HwordExact : pointsTo_u32 1048556 result $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem naive_storeTrunc_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048556 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048556 oldWord ⊢
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
      ▷ pointsTo_u32 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
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
      pointsTo_u32 ((1048544 : UInt32) + 12) (f32Trunc x) =
        pointsTo_u32 1048556 (f32Trunc x) :=
    congrArg (fun address => pointsTo_u32 address (f32Trunc x)) (by decide)
  ihave HwordExact : pointsTo_u32 1048556 (f32Trunc x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hnext
  iframe

theorem naive_ceil_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 (f32Ceil (f32Trunc x)) ∗
        pointsTo_u32 1048556 (f32Ceil (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048540 oldDeep ∗ pointsTo_u32 1048556 oldWord ⊢
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
    (iprop(R ∗ runtimeModuleOwn «module» ∗
      pointsTo_u32 1048556 oldWord))
    (f32Trunc x) oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    ihave HwordLater :
        ▷ pointsTo_u32 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
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
        pointsTo_u32 ((1048544 : UInt32) + 12)
            (f32Ceil (f32Trunc x)) =
          pointsTo_u32 1048556 (f32Ceil (f32Trunc x)) :=
      congrArg
        (fun address => pointsTo_u32 address (f32Ceil (f32Trunc x)))
        (by decide)
    ihave HwordExact :
        pointsTo_u32 1048556 (f32Ceil (f32Trunc x)) $$ [Hword]
    · rw [← hWordProp]
      iexact Hword
    iapply hnext
    iframe
  · iframe

theorem naive_floor_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hnext :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 (f32Floor (f32Trunc x)) ∗
        pointsTo_u32 1048556 (f32Floor (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048540 oldDeep ∗ pointsTo_u32 1048556 oldWord ⊢
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
    (iprop(R ∗ runtimeModuleOwn «module» ∗
      pointsTo_u32 1048556 oldWord))
    (f32Trunc x) oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    ihave HwordLater :
        ▷ pointsTo_u32 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
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
        pointsTo_u32 ((1048544 : UInt32) + 12)
            (f32Floor (f32Trunc x)) =
          pointsTo_u32 1048556 (f32Floor (f32Trunc x)) :=
      congrArg
        (fun address => pointsTo_u32 address (f32Floor (f32Trunc x)))
        (by decide)
    ihave HwordExact :
        pointsTo_u32 1048556 (f32Floor (f32Trunc x)) $$ [Hword]
    · rw [← hWordProp]
      iexact Hword
    iapply hnext
    iframe
  · iframe

theorem naive_compare_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hceil :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 (f32Ceil (f32Trunc x)) ∗
        pointsTo_u32 1048556 (f32Ceil (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hfloor :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048540 (f32Floor (f32Trunc x)) ∗
        pointsTo_u32 1048556 (f32Floor (f32Trunc x)) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (htrunc :
      R ∗ runtimeModuleOwn «module» ∗
        pointsTo_u32 1048540 oldDeep ∗
        globalPointsTo 0 (.i32 1048544) ∗
        pointsTo_u32 1048556 (f32Trunc x) ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)), .f32 0],
            []⟩,
          naiveTailProg, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048544) ∗
      pointsTo_u32 1048540 oldDeep ∗ pointsTo_u32 1048556 oldWord ⊢
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
        (iprop(R ∗ runtimeModuleOwn «module» ∗
          pointsTo_u32 1048540 oldDeep))
        x oldWord calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply htrunc
        iframe
      · iframe

theorem func0_lowered_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (x oldDeep oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn : ∀ result : UInt32,
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048540 result ∗
        pointsTo_u32 1048556 result ⊢
      WP (.running
        ⟨⟨[.f32 x],
            [.i32 1048544, .f32 (f32Trunc x),
              .f32 (f32Sub x (f32Trunc x)),
              .f32 result],
            [.f32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048540 oldDeep ∗ pointsTo_u32 1048556 oldWord ⊢
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
  ihave HglobalLater : ▷ globalPointsTo 0 (.i32 1048560) $$ [Hglobal]
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
    (iprop(R ∗ runtimeModuleOwn «module» ∗
      pointsTo_u32 1048556 oldWord))
    x oldDeep _ _
  · iintro ⟨⟨HR, Hruntime, Hword⟩, Hglobal, Hdeep⟩
    iapply wp_returnFromCallExplicit
    inext
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
        (iprop(R ∗ runtimeModuleOwn «module» ∗
          pointsTo_u32 1048540 (f32Ceil (f32Trunc x))))
        x (f32Ceil (f32Trunc x)) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Ceil (f32Trunc x))
        iframe
      · iframe
    · iintro ⟨HR, Hruntime, Hglobal, Hdeep, Hword⟩
      iapply naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn «module» ∗
          pointsTo_u32 1048540 (f32Floor (f32Trunc x))))
        x (f32Floor (f32Trunc x)) calls _
      · iintro ⟨⟨HR, Hruntime, Hdeep⟩, Hglobal, Hword⟩
        iapply hreturn (f32Floor (f32Trunc x))
        iframe
      · iframe
    · iintro ⟨HR, Hruntime, Hdeep, Hglobal, Hword⟩
      iapply naive_tail_smallStep_wp
        (iprop(R ∗ runtimeModuleOwn «module» ∗
          pointsTo_u32 1048540 (f32Trunc x)))
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
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    (R : IProp WasmHeapGF) (x result : UInt32) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        roundCheckTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [roundCheckTailProg]
  iapply wp_localGet rfl
  inext
  ihave HresultLater :
      ▷ pointsTo_u32 ((1048560 : UInt32) + 12) result $$ [Hresult]
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
      ▷ globalPointsTo 0 (.i32 1048560) $$ [Hglobal]
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
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (x oldDeep oldWord oldResult : UInt32)
    (hzero : ∀ deep word : UInt32,
      pointsTo_u32 1048540 deep ∗ pointsTo_u32 1048556 word ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          roundCheckTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone : ∀ deep word : UInt32,
      pointsTo_u32 1048540 deep ∗ pointsTo_u32 1048556 word ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          roundCheckTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 1048540 oldDeep ∗ pointsTo_u32 1048556 oldWord ∗
      runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 oldResult ⊢
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
    (iprop(pointsTo_u32 1048572 oldResult))
    x oldDeep oldWord _ _
  · intro naive
    iintro ⟨Hresult, Hruntime, Hglobal, Hdeep, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply wp_localGet rfl
    inext
    iapply wp_call «module» 4 func4Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func4Def, Function.toLocals, Function.numParams]
    iapply func4_lowered_smallStep_wp
      (iprop(pointsTo_u32 1048540 naive ∗
        pointsTo_u32 1048572 oldResult))
      x naive _ _
    · iintro ⟨⟨Hdeep, Hresult⟩, Hruntime, Hglobal, Hword⟩
      iapply wp_returnFromCallExplicit
      inext
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
            ▷ pointsTo_u32 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
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
            pointsTo_u32 ((1048560 : UInt32) + 12) 1 =
              pointsTo_u32 1048572 1 :=
          congrArg (fun address => pointsTo_u32 address 1) (by decide)
        ihave HresultExact : pointsTo_u32 1048572 1 $$ [Hresult]
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
            ▷ pointsTo_u32 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
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
            pointsTo_u32 ((1048560 : UInt32) + 12) 0 =
              pointsTo_u32 1048572 0 :=
          congrArg (fun address => pointsTo_u32 address 0) (by decide)
        ihave HresultExact : pointsTo_u32 1048572 0 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply hzero naive (f32Nearest x)
        iframe
    · iframe
  · iframe

theorem func6_body_smallStep_wp
    [WasmSmallStepGS hlc] {s : Stuckness} {E : CoPset} :
    pointsTo_u32 1048540 0 ∗ pointsTo_u32 1048556 0 ∗
      pointsTo_u32 1048572 0 ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ⊢
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
  ihave HglobalLater : ▷ globalPointsTo 0 (.i32 1048576) $$ [Hglobal]
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
      (iprop(pointsTo_u32 1048540 deep ∗
        pointsTo_u32 1048556 word ∗ runtimeModuleOwn «module»))
      x 0
    iframe
  · intro deep word
    iintro ⟨Hdeep, Hword, Hruntime, Hglobal, Hresult⟩
    iapply roundCheck_tail_result_smallStep_wp
      (iprop(pointsTo_u32 1048540 deep ∗
        pointsTo_u32 1048556 word ∗ runtimeModuleOwn «module»))
      x 1
    iframe
  · iframe

def checkRoundConfig (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func6, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

theorem checkRound_smallStep (x : UInt32) :
    PartiallyMeets (checkRoundConfig x)
      (fun values _store => ∃ b : UInt32, values = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
      (α := Unit) (σ := roundHeap) (globalσ := roundGlobals)
      (φ := fun values => ∃ b : UInt32, values = [.i32 b])
  · simpa [checkRoundConfig] using roundHeap_agrees
  · simpa [checkRoundConfig] using roundHeap_inBounds
  · simpa [checkRoundConfig] using roundGlobals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := roundHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hdeep, Hword, Hresult⟩
    ihave Hglobal := roundGlobals_pointsTo $$ Hglobals
    simp only [checkRoundConfig]
    iapply func6_body_smallStep_wp
    iframe

-- after globalSet 0, the new global[0] holds the stored value
private theorem globals_set0 {st : Store Unit} {sp : UInt32} (sp' : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 sp)) :
    ({st with globals := {globals := st.globals.globals.set 0 (.i32 sp')}} : Store Unit).globals.globals[0]? = some (.i32 sp') := by
  cases h : st.globals.globals with
  | nil => simp [h] at hg
  | cons _ _ => rfl

-- frame at (sp-16)+12 stays in bounds given sp >= 16 and sp <= pages*65536
private theorem frame_oob_false {sp : UInt32} {pages : Nat}
    (h16 : 16 <= sp.toNat) (hb : sp.toNat <= pages * 65536) :
    ¬ ((sp - 16).toNat + 12 + 4 > pages * 65536) := by
  have hle : (16 : UInt32) <= sp := UInt32.le_iff_toNat_le.mpr (by simpa using h16)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  rw [hsub]; omega

-- WP rules produce off.toNat where off : UInt32 = 12; normalize to Nat literal
private theorem off12 : (12 : UInt32).toNat = 12 := rfl

/-! ## func1/2/3/5: single float op via frame -/

private theorem func1_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 1 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func1, [.f32], none⟩) rfl
  unfold func1; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

private theorem func2_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 2 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func2, [.f32], none⟩) rfl
  unfold func2; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

private theorem func3_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 3 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func3, [.f32], none⟩) rfl
  unfold func3; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

private theorem func5_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 5 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func5, [.f32], none⟩) rfl
  unfold func5; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

/-! ## func4: wrapper calling func5 -/

private theorem func4_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 4 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func4, [.f32], none⟩) rfl
  unfold func4; wp_run
  apply wp_call_tw (func5_term env st sp x [] hg hp h16 hb)
  rintro st5 vs5 ⟨v5, rfl, hg5, hp5⟩
  wp_run
  exact ⟨v5, rfl, hg5, hp5⟩

/-! ## func0: naive round via trunc + frac comparison -/

private theorem func0_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h32 : 32 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 0 st [.f32 x]
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32, .f32, .f32, .f32], func0, [.f32], none⟩) rfl
  unfold func0; wp_run; simp only [hg]
  -- frame setup: sp -> sp-16, local[1] = sp-16
  have hle32 : (16 : UInt32) <= sp := UInt32.le_iff_toNat_le.mpr (by simpa using (show 16 ≤ sp.toNat from by omega))
  have hsub32 : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle32
  have h16_1 : 16 <= (sp - 16).toNat := by rw [hsub32]; omega
  have hb1 : (sp - 16).toNat <= 16 * 65536 := by rw [hsub32]; omega
  have hg1 : ({st with globals := {globals := st.globals.globals.set 0 (.i32 (sp - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (sp - 16)) :=
    globals_set0 (sp - 16) hg
  -- call func1(x) -> v1 = f32Trunc x (operationally), global and mem unchanged
  apply wp_call_tw (func1_term env _ (sp - 16) x [] hg1 hp h16_1 hb1)
  rintro st1 vs1 ⟨v1, rfl, hg1', hp1'⟩
  -- compute frac = x - v1, enter 4-level block structure
  wp_run
  apply wp_block_cons; apply wp_block_cons; apply wp_block_cons; apply wp_block_cons
  -- inside innermost block D: comparisons and branching
  wp_run
  -- bounds check for func0's own f32Store/f32Load at (sp-16)+12
  have hnt0 : ¬ ((sp - 16).toNat + 12 + 4 > 16 * 65536) :=
    frame_oob_false (by omega) hb
  -- sp frame restore: const 16 is top, localGet 1 is second, add = 16+(sp-16) = sp
  have hrestored : (sp - 16 : UInt32) + 16 = sp := by apply UInt32.ext; simp
  have hrestored' : 16 + (sp - 16 : UInt32) = sp := by apply UInt32.ext; simp [hsub32]; omega
  -- OOB in the normalized form simp produces: (sp-16).toNat ≤ 1048560
  have hnt0' : (sp - 16).toNat ≤ 1048560 := by have := hnt0; omega
  cases hge : f32Ge (f32Sub x v1) 1056964608
  · -- frac < 0.5: not the ceil branch
    simp [hge]
    cases hle' : f32Le (f32Sub x v1) 3204448256
    · -- frac > -0.5: neutral (B cont: store v1 directly)
      simp
      -- B cont: localGet 1, localGet 2, f32Store 12, br 1
      -- rest_after_A: localGet 1, f32Load 12, localSet 4, localGet 1, const 16, add, globalSet 0, localGet 4, ret
      simp [hp1', hnt0', hg1', hrestored']
      exact globals_set0 sp hg1'
    · -- frac <= -0.5: floor branch (A cont: call func3)
      simp
      -- A cont: localGet 1, localGet 2, call 3
      apply wp_call_tw
        (func3_term env st1 (sp - 16) v1 [.i32 (sp - 16)] hg1' hp1' h16_1 hb1)
      rintro st3 vs3 ⟨v3, rfl, hg3, hp3⟩
      have hnt3' : (sp - 16).toNat ≤ 1048560 := by
        have := frame_oob_false (by omega) hb; omega
      -- A cont after call: f32Store 12, fall through to rest_after_A
      wp_run
      simp [hp3, hnt3', hg3, hrestored']
      exact globals_set0 sp hg3
  · -- frac >= 0.5: ceil branch (C cont: call func2, f32Store 12, br 2)
    simp [hge]
    -- C cont: localGet 1, localGet 2, call 2
    apply wp_call_tw
      (func2_term env st1 (sp - 16) v1 [.i32 (sp - 16)] hg1' hp1' h16_1 hb1)
    rintro st2 vs2 ⟨v2, rfl, hg2, hp2⟩
    have hnt2' : (sp - 16).toNat ≤ 1048560 := by
      have := frame_oob_false (by omega) hb; omega
    -- C cont after call: f32Store 12, br 2, rest_after_A
    wp_run
    simp [hp2, hnt2', hg2, hrestored']
    exact globals_set0 sp hg2

/-! ## FloatRoundSpec -/

@[spec_of "rust-exported" "float_round::check_round"]
def FloatRoundSpec : Prop :=
  ∀ (env : HostEnv Unit) (x : UInt32),
    TerminatesWith env «module» 6 «module».initialStore
      [.f32 x]
      (fun _ rs => ∃ b : UInt32, rs = [.i32 b])

@[proves Project.FloatRound.Spec.FloatRoundSpec]
theorem check_round_terminates : FloatRoundSpec := by
  intro env x
  have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 16 := rfl
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32, .i32], func6, [.i32], none⟩) rfl
  unfold func6; wp_run; simp only [hg]
  -- frame: sp = 1048576 -> 1048560
  have hg6 : ({«module».initialStore with globals := {globals := «module».initialStore.globals.globals.set 0 (.i32 (1048576 - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (1048576 - 16)) :=
    globals_set0 (1048576 - 16) hg
  apply wp_block_cons; apply wp_block_cons
  wp_run
  -- call func0(x)
  apply wp_call_tw
    (func0_term env _ (1048576 - 16) x hg6 (by rfl) (by decide) (by decide))
  rintro st0 vs0 ⟨v0, rfl, hg0, hp0⟩
  wp_run
  -- call func4(x)
  apply wp_call_tw
    (func4_term env st0 (1048576 - 16) x [.f32 v0] hg0 hp0 (by decide) (by decide))
  rintro st4 vs4 ⟨v4, rfl, hg4, hp4⟩
  -- f32Eq, const 1, and, br_if 0: case split on equality
  wp_run
  -- concrete OOB check: 1048560 + 12 + 4 = 1048576 ≤ 16 * 65536
  have hnt6 : ¬ ((1048576 - 16 : UInt32).toNat + 12 + 4 > 16 * 65536) := by decide
  have hrestored6 : (1048576 - 16 : UInt32) + 16 = 1048576 := by decide
  cases heq : f32Eq v0 v4
  · -- not equal: store32 0 at 1048560+12, br 1
    simp [heq]
    simp [hp4, hg4]
  · -- equal: B cont: store32 1 at 1048560+12
    simp [heq]
    simp [hp4, hg4]

end Project.FloatRound.Spec
