import Project.FloatReinterpret.Program

/-!
# Specification for `float_reinterpret`
-/

namespace Project.FloatReinterpret.Spec

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SmallStep
open Wasm.SepLogic

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000

/-! ## Authoritative small-step pure reinterpret leaves -/

def func5Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func5, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

theorem func5_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x : UInt32) (calls : List CallFrame) :
    ▷ WP (.running
      ⟨⟨[.f32 x], [], [.i32 x]⟩,
        [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func5, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simp only [func5]
  iintro Hret
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  iexact Hret

theorem func5_smallStep (x : UInt32) :
    PartiallyMeets (func5Config x)
      (fun rs _store => rs = [.i32 x]) := by
  apply wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [func5Config]
  iapply func5_body_smallStep_wp x []
  inext
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

def func6Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.i32 x], [], []⟩, func6, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

theorem func6_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x : UInt32) (calls : List CallFrame) :
    ▷ WP (.running
      ⟨⟨[.i32 x], [], [.f32 x]⟩,
        [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨[.i32 x], [], []⟩,
        func6, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simp only [func6]
  iintro Hret
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  iexact Hret

theorem func6_smallStep (x : UInt32) :
    PartiallyMeets (func6Config x)
      (fun rs _store => rs = [.f32 x]) := by
  apply wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [func6Config]
  iapply func6_body_smallStep_wp x []
  inext
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

def func9Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func9, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

/-- Complete small-step Iris proof for the bit-manipulation implementation of
`f32.abs`. The two reinterpret calls are composed through their actual saved
call frames. -/
theorem func9_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x : UInt32) :
    runtimeModuleOwn «module» ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩, func9, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (2147483647 &&& x)]⌝ }} := by
  iintro Hruntime
  simp only [func9]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply func5_body_smallStep_wp x _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  iapply wp_const
  inext
  iapply wp_and
  inext
  iapply wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm x 2147483647]
  iapply func6_body_smallStep_wp (2147483647 &&& x) _
  inext
  iapply wp_returnFromCallExplicit
  inext
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  iclear Hruntime
  ipureintro
  rfl

theorem func9_smallStep (x : UInt32) :
    PartiallyMeets (func9Config x)
      (fun rs _store => rs = [.f32 (2147483647 &&& x)]) := by
  apply wasm_smallStep_runtime_partiallyMeets (α := Unit)
  intro gs
  simp only [func9Config]
  iapply func9_smallStep_wp

def func4Result (x y : UInt32) : UInt32 :=
  (2147483648 &&& y) ||| (2147483647 &&& x)

def func4Config (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func4, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

/-- Complete small-step Iris proof for the bit-manipulation implementation of
`f32.copysign`. -/
theorem func4_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x y : UInt32) :
    runtimeModuleOwn «module» ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func4, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (func4Result x y)]⌝ }} := by
  iintro Hruntime
  simp only [func4]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply func5_body_smallStep_wp y _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  iapply wp_const
  inext
  iapply wp_and
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply func5_body_smallStep_wp x _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  iapply wp_const
  inext
  iapply wp_and
  inext
  iapply wp_or
  inext
  iapply wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  simp only [func4Result]
  rw [UInt32.and_comm y 2147483648, UInt32.and_comm x 2147483647]
  iapply func6_body_smallStep_wp
    ((2147483648 &&& y) ||| (2147483647 &&& x)) _
  inext
  iapply wp_returnFromCallExplicit
  inext
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  iclear Hruntime
  ipureintro
  rfl

theorem func4_smallStep (x y : UInt32) :
    PartiallyMeets (func4Config x y)
      (fun rs _store => rs = [.f32 (func4Result x y)]) := by
  apply wasm_smallStep_runtime_partiallyMeets (α := Unit)
  intro gs
  simp only [func4Config]
  iapply func4_smallStep_wp

/-! ## Authoritative frame-backed `f32.abs` -/

def func1Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [.i32 0], []⟩, func1, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

def func1Heap : WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 1048572 0

def func1Globals : WasmGlobalMap Value :=
  insert ∅ 0 (.i32 1048576)

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

theorem func1Heap_agrees :
    heapAgreesWithMem func1Heap (func1Config 0).store.wasm.mem := by
  unfold func1Heap func1Config
  have hagree := store32_sound
    (σ := (∅ : WasmHeapMap (Option UInt8)))
    (mem := («module».initialStore : Store Unit).mem)
    (addr := 1048572) (value := 0)
    (by decide) (by decide) (by decide)
    (emptyHeap_agrees _)
  rw [Mem.write32_eq_self (by decide) (by decide) (by decide) (by decide)]
    at hagree
  exact hagree

theorem func1Heap_inBounds :
    heapAddressesInBounds func1Heap (func1Config 0).store.wasm.mem := by
  unfold func1Heap func1Config
  apply store32_inBounds
    (σ := (∅ : WasmHeapMap (Option UInt8)))
    (mem := («module».initialStore : Store Unit).mem)
    (addr := 1048572) (value := 0)
    (by decide) (by decide) (by decide)
    (emptyHeap_inBounds _)
  decide

theorem func1Globals_agree :
    globalHeapAgrees func1Globals (func1Config 0).store.wasm.globals := by
  intro index value hget
  simp only [func1Globals] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (Ne.symm hindex), get?_empty] at hget
    contradiction

theorem func1Heap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func1Heap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 1048572 0 := by
  unfold func1Heap
  simpa only [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq] using
    (store32Heap_pointsTo (∅ : WasmHeapMap (Option UInt8))
      1048572 0
      (get?_empty _) (get?_empty _) (get?_empty _) (get?_empty _)
      (by decide) (by decide) (by decide))

theorem func1Globals_pointsTo [WasmGlobalGS Unit] :
    ([∗map] index ↦ value ∈ func1Globals,
      globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576) := by
  unfold func1Globals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty 0)).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

theorem func1_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048576) ∗
        pointsTo_u32 1048572 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u32 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func1]
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
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 ((1048560 : UInt32) + 12) oldWord $$ [Hword]
  · inext
    rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hword
  iapply wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 ((1048560 : UInt32) + 12) (f32Abs x) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load (f32Abs x)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 ((1048560 : UInt32) + 12) (f32Abs x) =
        pointsTo_u32 1048572 (f32Abs x) :=
    congrArg (fun address => pointsTo_u32 address (f32Abs x)) (by decide)
  ihave HwordExact : pointsTo_u32 1048572 (f32Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func1_smallStep (x : UInt32) :
    PartiallyMeets (func1Config x)
      (fun rs _store => rs = [.f32 (f32Abs x)]) := by
  apply wasm_smallStep_heap_globals_partiallyMeets
    (α := Unit) (σ := func1Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f32 (f32Abs x)])
  · simpa [func1Config] using func1Heap_agrees
  · simpa [func1Config] using func1Heap_inBounds
  · simpa [func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func1Config]
    iapply func1_body_smallStep_wp (iprop(True)) x 0 []
    · iintro ⟨_Htrue, Hglobal, Hword⟩
      iapply wp_returnFromFunction
      inext
      iapply wp_value'
      iclear Hglobal Hword
      ipureintro
      rfl
    · iframe

def func0Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func0, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

/-- Small-step Iris proof for the generated wrapper around the frame-backed
`f32.abs` implementation. -/
theorem func0_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x oldWord : UInt32) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u32 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩, func0, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (f32Abs x)]⌝ }} := by
  iintro ⟨Hruntime, Hglobal, Hword⟩
  simp only [func0]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func1_body_smallStep_wp
    (runtimeModuleOwn «module») x oldWord _
  · iintro ⟨Hruntime, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hruntime Hglobal Hword
    ipureintro
    rfl
  · iframe

theorem func0_smallStep (x : UInt32) :
    PartiallyMeets (func0Config x)
      (fun rs _store => rs = [.f32 (f32Abs x)]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
    (α := Unit) (σ := func1Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f32 (f32Abs x)])
  · simpa [func0Config, func1Config] using func1Heap_agrees
  · simpa [func0Config, func1Config] using func1Heap_inBounds
  · simpa [func0Config, func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func0Config]
    iapply func0_smallStep_wp x 0
    iframe

/-! ## Authoritative frame-backed `f64.abs` -/

def func3Config (x : UInt64) : Config Unit :=
  { expr := .running
      ⟨⟨[.f64 x], [.i32 0], []⟩, func3, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

def func3Heap : WasmHeapMap (Option UInt8) :=
  Wasm.RustStd.U64.absDiffHeap 0

theorem func3_initialScratchMem_eq :
    («module».initialStore : Store Unit).mem.write64 1048568 0 =
      («module».initialStore : Store Unit).mem := by
  simp [«module», Module.initialStore, Mem.write64, Mem.empty]

theorem func3Heap_agrees :
    heapAgreesWithMem func3Heap (func3Config 0).store.wasm.mem := by
  unfold func3Heap func3Config Wasm.RustStd.U64.absDiffHeap
  have hagree := store64_sound
    (σ := (∅ : WasmHeapMap (Option UInt8)))
    (mem := («module».initialStore : Store Unit).mem)
    (addr := 1048568) (value := 0)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (emptyHeap_agrees _)
  rw [func3_initialScratchMem_eq] at hagree
  exact hagree

theorem func3Heap_inBounds :
    heapAddressesInBounds func3Heap (func3Config 0).store.wasm.mem := by
  unfold func3Heap func3Config Wasm.RustStd.U64.absDiffHeap
  rw [← func3_initialScratchMem_eq]
  apply store64_inBounds
    (σ := (∅ : WasmHeapMap (Option UInt8)))
    (mem := («module».initialStore : Store Unit).mem)
    (addr := 1048568) (value := 0)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (emptyHeap_inBounds _)
  decide

theorem func3Heap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func3Heap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048568 0 := by
  exact Wasm.RustStd.U64.absDiffHeap_pointsTo 0

theorem func3_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048576) ∗
        pointsTo_u64 1048568 (f64Abs x) ⊢
      WP (.running
        ⟨⟨[.f64 x], [.i32 1048560], [.f64 (f64Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048568 oldWord ⊢
    WP (.running
      ⟨⟨[.f64 x], [.i32 0], []⟩,
        func3, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func3]
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
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u64 ((1048560 : UInt32) + 8) oldWord $$ [Hword]
  · inext
    rw [show (1048560 : UInt32) + 8 = 1048568 by decide]
    iexact Hword
  iapply wp_f64Store oldWord
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u64 ((1048560 : UInt32) + 8) (f64Abs x) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f64Load (f64Abs x)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u64 ((1048560 : UInt32) + 8) (f64Abs x) =
        pointsTo_u64 1048568 (f64Abs x) :=
    congrArg (fun address => pointsTo_u64 address (f64Abs x)) (by decide)
  ihave HwordExact : pointsTo_u64 1048568 (f64Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func3_smallStep (x : UInt64) :
    PartiallyMeets (func3Config x)
      (fun rs _store => rs = [.f64 (f64Abs x)]) := by
  apply wasm_smallStep_heap_globals_partiallyMeets
    (α := Unit) (σ := func3Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f64 (f64Abs x)])
  · simpa [func3Config] using func3Heap_agrees
  · simpa [func3Config] using func3Heap_inBounds
  · simpa [func3Config, func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hword := func3Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func3Config]
    iapply func3_body_smallStep_wp (iprop(True)) x 0 []
    · iintro ⟨_Htrue, Hglobal, Hword⟩
      iapply wp_returnFromFunction
      inext
      iapply wp_value'
      iclear Hglobal Hword
      ipureintro
      rfl
    · iframe

def func2Result (x : UInt32) : UInt32 :=
  f32DemoteF64 (f64Abs (f64PromoteF32 x))

def func2Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func2, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

/-- Small-step Iris proof for the generated promote/`f64.abs`/demote wrapper. -/
theorem func2_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x : UInt32) (oldWord : UInt64) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048568 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩, func2, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (func2Result x)]⌝ }} := by
  iintro ⟨Hruntime, Hglobal, Hword⟩
  simp only [func2]
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  inext
  iapply wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func3_body_smallStep_wp
    (runtimeModuleOwn «module») (f64PromoteF32 x) oldWord _
  · iintro ⟨Hruntime, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply wp_scalarFloat1 rfl rfl
    inext
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hruntime Hglobal Hword
    ipureintro
    rfl
  · iframe

theorem func2_smallStep (x : UInt32) :
    PartiallyMeets (func2Config x)
      (fun rs _store => rs = [.f32 (func2Result x)]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
    (α := Unit) (σ := func3Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f32 (func2Result x)])
  · simpa [func2Config, func3Config] using func3Heap_agrees
  · simpa [func2Config, func3Config] using func3Heap_inBounds
  · simpa [func2Config, func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func3Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func2Config]
    iapply func2_smallStep_wp x 0
    iframe

/-! ## Authoritative frame-backed `f32.copysign` -/

def func8Config (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [.i32 0], []⟩, func8, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

theorem func8_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048576) ∗
        pointsTo_u32 1048572 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560],
            [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u32 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0], []⟩,
        func8, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func8]
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
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat2 rfl rfl rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 ((1048560 : UInt32) + 12) oldWord $$ [Hword]
  · inext
    rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hword
  iapply wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u32 ((1048560 : UInt32) + 12) (f32Copysign x y) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load (f32Copysign x y)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 ((1048560 : UInt32) + 12) (f32Copysign x y) =
        pointsTo_u32 1048572 (f32Copysign x y) :=
    congrArg (fun address => pointsTo_u32 address (f32Copysign x y)) (by decide)
  ihave HwordExact : pointsTo_u32 1048572 (f32Copysign x y) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func8_smallStep (x y : UInt32) :
    PartiallyMeets (func8Config x y)
      (fun rs _store => rs = [.f32 (f32Copysign x y)]) := by
  apply wasm_smallStep_heap_globals_partiallyMeets
    (α := Unit) (σ := func1Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f32 (f32Copysign x y)])
  · simpa [func8Config, func1Config] using func1Heap_agrees
  · simpa [func8Config, func1Config] using func1Heap_inBounds
  · simpa [func8Config, func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func8Config]
    iapply func8_body_smallStep_wp (iprop(True)) x y 0 []
    · iintro ⟨_Htrue, Hglobal, Hword⟩
      iapply wp_returnFromFunction
      inext
      iapply wp_value'
      iclear Hglobal Hword
      ipureintro
      rfl
    · iframe

def func7Config (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func7, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

theorem func7_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x y oldWord : UInt32) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u32 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func7, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (f32Copysign x y)]⌝ }} := by
  iintro ⟨Hruntime, Hglobal, Hword⟩
  simp only [func7]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 8 func8Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func8Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func8_body_smallStep_wp
    (runtimeModuleOwn «module») x y oldWord _
  · iintro ⟨Hruntime, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hruntime Hglobal Hword
    ipureintro
    rfl
  · iframe

theorem func7_smallStep (x y : UInt32) :
    PartiallyMeets (func7Config x y)
      (fun rs _store => rs = [.f32 (f32Copysign x y)]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
    (α := Unit) (σ := func1Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f32 (f32Copysign x y)])
  · simpa [func7Config, func1Config] using func1Heap_agrees
  · simpa [func7Config, func1Config] using func1Heap_inBounds
  · simpa [func7Config, func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func7Config]
    iapply func7_smallStep_wp x y 0
    iframe

/-! ## Combined ownership for the exported checks

The exports allocate an outer 16-byte frame. Calls made beneath that frame
allocate one more 16-byte frame, so the widest inner scratch slot is the
eight-byte range at `1048552`; the outer check result is the disjoint word at
`1048572`. -/

def exportHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store64Heap ∅ 1048552 0) 1048572 0

def exportMem (memory : Mem) : Mem :=
  (memory.write64 1048552 0).write32 1048572 0

theorem export_initialMem_eq :
    exportMem («module».initialStore : Store Unit).mem =
      («module».initialStore : Store Unit).mem := by
  simp [exportMem, «module», Module.initialStore, Mem.write64,
    Mem.write32, Mem.empty]

theorem exportHeap_agrees :
    heapAgreesWithMem exportHeap
      («module».initialStore : Store Unit).mem := by
  rw [← export_initialMem_eq]
  unfold exportHeap exportMem
  apply store32_sound <;> try rfl
  apply store64_sound <;> try rfl
  exact emptyHeap_agrees _

theorem exportHeap_inBounds :
    heapAddressesInBounds exportHeap
      («module».initialStore : Store Unit).mem := by
  rw [← export_initialMem_eq]
  unfold exportHeap exportMem
  apply store32_inBounds <;> try rfl
  · apply store64_inBounds <;> try rfl
    · exact emptyHeap_inBounds _
    · decide

theorem exportHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ exportHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 0 ∗ pointsTo_u32 1048572 0 := by
  unfold exportHeap
  iintro Hheap
  ihave Houter := store32Heap_pointsTo
    (store64Heap ∅ 1048552 0) 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Houter with ⟨Houter, HinnerHeap⟩
  ihave Hinner := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HinnerHeap
  icases Hinner with ⟨Hinner, Hempty⟩
  iframe

def packUpper32 (upper : UInt32) : UInt64 :=
  upper.toUInt64 <<< 32

theorem innerScratch_split_zero [WasmHeapGS Unit] :
    pointsTo_u64 1048552 0 ⊢
      pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048556 0 := by
  have h0 : u64Byte 0 0 = u32Byte 0 0 := rfl
  have h1 : u64Byte 0 1 = u32Byte 0 1 := rfl
  have h2 : u64Byte 0 2 = u32Byte 0 2 := rfl
  have h3 : u64Byte 0 3 = u32Byte 0 3 := rfl
  have h4 : u64Byte 0 4 = u32Byte 0 0 := rfl
  have h5 : u64Byte 0 5 = u32Byte 0 1 := rfl
  have h6 : u64Byte 0 6 = u32Byte 0 2 := rfl
  have h7 : u64Byte 0 7 = u32Byte 0 3 := rfl
  unfold pointsTo_u64 pointsTo_u32
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [show (1048552 : UInt32) + 4 = 1048556 by decide,
    show (1048552 : UInt32) + 5 = 1048556 + 1 by decide,
    show (1048552 : UInt32) + 6 = 1048556 + 2 by decide,
    show (1048552 : UInt32) + 7 = 1048556 + 3 by decide]
  iintro Hbytes
  icases Hbytes with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iframe

theorem innerScratch_merge_upper [WasmHeapGS Unit] (upper : UInt32) :
    pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048556 upper ⊢
      pointsTo_u64 1048552 (packUpper32 upper) := by
  have h0 : u64Byte (packUpper32 upper) 0 = u32Byte 0 0 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  have h1 : u64Byte (packUpper32 upper) 1 = u32Byte 0 1 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  have h2 : u64Byte (packUpper32 upper) 2 = u32Byte 0 2 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  have h3 : u64Byte (packUpper32 upper) 3 = u32Byte 0 3 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  have h4 : u64Byte (packUpper32 upper) 4 = u32Byte upper 0 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  have h5 : u64Byte (packUpper32 upper) 5 = u32Byte upper 1 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  have h6 : u64Byte (packUpper32 upper) 6 = u32Byte upper 2 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  have h7 : u64Byte (packUpper32 upper) 7 = u32Byte upper 3 := by
    unfold packUpper32 u64Byte u32Byte
    bv_decide
  unfold pointsTo_u64 pointsTo_u32
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [show (1048552 : UInt32) + 4 = 1048556 by decide,
    show (1048552 : UInt32) + 5 = 1048556 + 1 by decide,
    show (1048552 : UInt32) + 6 = 1048556 + 2 by decide,
    show (1048552 : UInt32) + 7 = 1048556 + 3 by decide]
  iintro Hbytes
  icases Hbytes with ⟨Hlow, Hhigh⟩
  icases Hlow with ⟨H0, H1, H2, H3⟩
  icases Hhigh with ⟨H4, H5, H6, H7⟩
  iframe

/-- `func1` under an export's already-lowered stack pointer. The upper half of
the owned `u64` scratch range is exposed as the `u32` word at `1048556`. -/
theorem func1_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048556 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048544], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func1]
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
      ▷ pointsTo_u32 ((1048544 : UInt32) + 12) (f32Abs x) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load (f32Abs x)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 ((1048544 : UInt32) + 12) (f32Abs x) =
        pointsTo_u32 1048556 (f32Abs x) :=
    congrArg (fun address => pointsTo_u32 address (f32Abs x)) (by decide)
  ihave HwordExact : pointsTo_u32 1048556 (f32Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func0_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048556 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func0, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func0]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func1_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn «module»)) x oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply hreturn
    iframe
  · iframe

/-- `func3` under an export's already-lowered stack pointer. -/
theorem func3_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 (f64Abs x) ⊢
      WP (.running
        ⟨⟨[.f64 x], [.i32 1048544], [.f64 (f64Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldWord ⊢
    WP (.running
      ⟨⟨[.f64 x], [.i32 0], []⟩,
        func3, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func3]
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
      ▷ pointsTo_u64 ((1048544 : UInt32) + 8) oldWord $$ [Hword]
  · inext
    rw [show (1048544 : UInt32) + 8 = 1048552 by decide]
    iexact Hword
  iapply wp_f64Store oldWord
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  iapply wp_localGet rfl
  inext
  ihave HwordLater :
      ▷ pointsTo_u64 ((1048544 : UInt32) + 8) (f64Abs x) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f64Load (f64Abs x)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u64 ((1048544 : UInt32) + 8) (f64Abs x) =
        pointsTo_u64 1048552 (f64Abs x) :=
    congrArg (fun address => pointsTo_u64 address (f64Abs x)) (by decide)
  ihave HwordExact : pointsTo_u64 1048552 (f64Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func2_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32) (oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (func2Result x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func2, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func2]
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  inext
  iapply wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func3_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn «module»))
    (f64PromoteF32 x) oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply wp_scalarFloat1 rfl rfl
    inext
    simp only [func2Result] at hreturn
    iapply hreturn
    iframe
  · iframe

/-- `func8` under an export's already-lowered stack pointer. -/
theorem func8_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048556 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048544],
            [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0], []⟩,
        func8, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func8]
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
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat2 rfl rfl rfl
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
      ▷ pointsTo_u32 ((1048544 : UInt32) + 12) (f32Copysign x y) $$ [Hword]
  · inext
    iexact Hword
  iapply wp_f32Load (f32Copysign x y)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  inext
  iintro Hword
  have hWordProp :
      pointsTo_u32 ((1048544 : UInt32) + 12) (f32Copysign x y) =
        pointsTo_u32 1048556 (f32Copysign x y) :=
    congrArg (fun address => pointsTo_u32 address (f32Copysign x y)) (by decide)
  ihave HwordExact : pointsTo_u32 1048556 (f32Copysign x y) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply hreturn
  iframe

theorem func7_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048556 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [], [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩,
        func7, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func7]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 8 func8Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func8Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func8_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn «module»)) x y oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply hreturn
    iframe
  · iframe

theorem func9_context_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (2147483647 &&& x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func9, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime⟩
  simp only [func9]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply func5_body_smallStep_wp x _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  iapply wp_const
  inext
  iapply wp_and
  inext
  iapply wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm x 2147483647]
  iapply func6_body_smallStep_wp (2147483647 &&& x) _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  iapply hreturn
  iframe

theorem func4_context_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [], [.f32 (func4Result x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩,
        func4, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime⟩
  simp only [func4]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply func5_body_smallStep_wp y _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  iapply wp_const
  inext
  iapply wp_and
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply func5_body_smallStep_wp x _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  iapply wp_const
  inext
  iapply wp_and
  inext
  iapply wp_or
  inext
  iapply wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm y 2147483648, UInt32.and_comm x 2147483647]
  iapply func6_body_smallStep_wp
    ((2147483648 &&& y) ||| (2147483647 &&& x)) _
  inext
  iapply wp_returnFromCallExplicit
  inext
  simp only [List.take, List.singleton_append]
  rw [← show func4Result x y =
    (2147483648 &&& y) ||| (2147483647 &&& x) by rfl]
  iapply hreturn
  iframe

def checkAbsTailProg : Program :=
  [ .localGet 1, .load32 12, .localSet 2,
    .localGet 1, .const 16, .add, .globalSet 0,
    .localGet 2, .ret ]

theorem checkAbs_tail_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048576) ∗
        pointsTo_u32 1048572 result ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 result], [.i32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsTailProg, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkAbsTailProg]
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
  have hResultProp :
      pointsTo_u32 ((1048560 : UInt32) + 12) result =
        pointsTo_u32 1048572 result :=
    congrArg (fun address => pointsTo_u32 address result) (by decide)
  ihave HresultExact : pointsTo_u32 1048572 result $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  iapply hreturn
  iframe

def checkAbsInnerBody : Program :=
  [ .localGet 0, .call 0, .localGet 0, .call 9,
    .f32Eq, .const 1, .and, .eqz, .br_if 0,
    .localGet 0, .call 0, .localGet 0, .call 2,
    .f32Eq, .const 1, .and, .eqz, .br_if 0,
    .localGet 1, .const 1, .store32 12, .br 1 ]

def checkAbsZeroProg : Program :=
  [.localGet 1, .const 0, .store32 12]

def checkAbsOuterBody : Program :=
  [.block 0 0 checkAbsInnerBody] ++ checkAbsZeroProg

def checkAbsOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := checkAbsOuterBody
    continuation := checkAbsTailProg
    belowStack := [] }

def checkAbsInnerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := checkAbsInnerBody
    continuation := checkAbsZeroProg
    belowStack := [] }

theorem checkAbs_zeroPath_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldResult : UInt32)
    (hcontinue :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsZeroProg, 1, [], [checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkAbsZeroProg]
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
  simp only [checkAbsOuterFrame, List.take, List.nil_append]
  have hResultProp :
      pointsTo_u32 ((1048560 : UInt32) + 12) 0 =
        pointsTo_u32 1048572 0 :=
    congrArg (fun address => pointsTo_u32 address 0) (by decide)
  ihave HresultExact : pointsTo_u32 1048572 0 $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  iapply hcontinue
  iframe

theorem checkAbs_onePath_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldResult : UInt32)
    (hcontinue :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        [.localGet 1, .const 1, .store32 12, .br 1],
        1, [], [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
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
  simp only [checkAbsOuterFrame, List.take, List.nil_append]
  have hResultProp :
      pointsTo_u32 ((1048560 : UInt32) + 12) 1 =
        pointsTo_u32 1048572 1 :=
    congrArg (fun address => pointsTo_u32 address 1) (by decide)
  ihave HresultExact : pointsTo_u32 1048572 1 $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  iapply hcontinue
  iframe

def checkAbsSecondProg : Program :=
  [ .localGet 0, .call 0, .localGet 0, .call 2,
    .f32Eq, .const 1, .and, .eqz, .br_if 0,
    .localGet 1, .const 1, .store32 12, .br 1 ]

theorem checkAbs_secondComparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x upper oldResult : UInt32)
    (hzero :
      pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048556 upper ∗
      runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        [ .localGet 0, .call 0, .localGet 0, .call 2,
          .f32Eq, .const 1, .and, .eqz, .br_if 0,
          .localGet 1, .const 1, .store32 12, .br 1 ],
        1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams]
  iapply func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048572 oldResult))
    x upper _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply wp_localGet rfl
    inext
    iapply wp_call «module» 2 func2Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    icombine Hlow Hupper as Hscratch
    ihave Hpacked := innerScratch_merge_upper (f32Abs x) $$ Hscratch
    simp [func2Def, Function.toLocals, Function.numParams]
    iapply func2_lowered_smallStep_wp
      (iprop(pointsTo_u32 1048572 oldResult))
      x (packUpper32 (f32Abs x)) _
    · iintro ⟨Hresult, Hruntime, Hglobal, Hscratch⟩
      iapply wp_returnFromCallExplicit
      inext
      simp only [List.take, List.singleton_append]
      by_cases heq :
          f32Eq (f32Abs x) (func2Result x) = true
      · iapply wp_scalarFloat2 (value := .i32 1) rfl rfl
          (by simp [evalScalarFloat2?, heq])
        inext
        iapply wp_const
        inext
        iapply wp_and
        inext
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        iapply wp_eqz (result := 0) (by decide)
        inext
        iapply wp_brIfZero
        inext
        iapply checkAbs_onePath_smallStep_wp
          (iprop(pointsTo_u64 1048552
            (f64Abs (f64PromoteF32 x)) ∗ runtimeModuleOwn «module»))
          x oldResult _
        · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
          iapply hone
          iframe
        · iframe
      · have heqFalse :
            f32Eq (f32Abs x) (func2Result x) = false := by
          cases h : f32Eq (f32Abs x) (func2Result x) <;> simp_all
        iapply wp_scalarFloat2 (value := .i32 0) rfl rfl
          (by simp [evalScalarFloat2?, heqFalse])
        inext
        iapply wp_const
        inext
        iapply wp_and
        inext
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        iapply wp_eqz (result := 1) (by decide)
        inext
        iapply wp_brIf (by decide) rfl
        inext
        simp only [checkAbsInnerFrame, List.take, List.nil_append]
        iapply checkAbs_zeroPath_smallStep_wp
          (iprop(pointsTo_u64 1048552
            (f64Abs (f64PromoteF32 x)) ∗ runtimeModuleOwn «module»))
          x oldResult _
        · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
          iapply hzero
          iframe
        · iframe
    · iframe
  · iframe

def checkAbsFirstTailProg : Program :=
  [ .f32Eq, .const 1, .and, .eqz, .br_if 0 ] ++ checkAbsSecondProg

theorem checkAbs_firstComparisonTail_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x oldResult : UInt32)
    (hzeroFirst :
      pointsTo_u64 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hzeroSecond :
      pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048556 (f32Abs x) ∗
      runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0],
          [.f32 (2147483647 &&& x), .f32 (f32Abs x)]⟩,
        [ .f32Eq, .const 1, .and, .eqz, .br_if 0,
          .localGet 0, .call 0, .localGet 0, .call 2,
          .f32Eq, .const 1, .and, .eqz, .br_if 0,
          .localGet 1, .const 1, .store32 12, .br 1 ],
        1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  by_cases heq : f32Eq (f32Abs x) (2147483647 &&& x) = true
  · iapply wp_scalarFloat2 (value := .i32 1) rfl rfl
      (by simp [evalScalarFloat2?, heq])
    inext
    iapply wp_const
    inext
    iapply wp_and
    inext
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    iapply wp_eqz (result := 0) (by decide)
    inext
    iapply wp_brIfZero
    inext
    iapply checkAbs_secondComparison_smallStep_wp
      (s := s) (E := E) (Φ := Φ)
      x (f32Abs x) oldResult _ _
    · exact hzeroSecond
    · exact hone
    · iframe
  · have heqFalse :
        f32Eq (f32Abs x) (2147483647 &&& x) = false := by
      cases h : f32Eq (f32Abs x) (2147483647 &&& x) <;> simp_all
    iapply wp_scalarFloat2 (value := .i32 0) rfl rfl
      (by simp [evalScalarFloat2?, heqFalse])
    inext
    iapply wp_const
    inext
    iapply wp_and
    inext
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    iapply wp_eqz (result := 1) (by decide)
    inext
    iapply wp_brIf (by decide) rfl
    inext
    simp only [checkAbsInnerFrame, List.take, List.nil_append]
    icombine Hlow Hupper as Hscratch
    ihave Hpacked := innerScratch_merge_upper (f32Abs x) $$ Hscratch
    iapply checkAbs_zeroPath_smallStep_wp
      (iprop(pointsTo_u64 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn «module»))
      x oldResult _
    · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
      iapply hzeroFirst
      iframe
    · iframe

theorem checkAbs_firstComparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x upper oldResult : UInt32)
    (hzeroFirst :
      pointsTo_u64 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hzeroSecond :
      pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048556 upper ∗
      runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsInnerBody, 1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  simp only [checkAbsInnerBody]
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams]
  iapply func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048572 oldResult))
    x upper _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply wp_localGet rfl
    inext
    iapply wp_call «module» 9 func9Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func9Def, Function.toLocals, Function.numParams]
    iapply func9_context_smallStep_wp
      (iprop(pointsTo_u32 1048552 0 ∗
        pointsTo_u32 1048556 (f32Abs x) ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048572 oldResult))
      x _ _
    · iintro ⟨HR, Hruntime⟩
      iapply wp_returnFromCallExplicit
      inext
      simp only [List.take, List.singleton_append]
      icases HR with ⟨Hlow, Hupper, Hglobal, Hresult⟩
      iapply checkAbs_firstComparisonTail_smallStep_wp
        (s := s) (E := E) (Φ := Φ)
        x oldResult _ _ _
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hone
      · iframe
    · iframe
  · iframe

theorem checkAbs_tail_result_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iapply checkAbs_tail_smallStep_wp R x result [] _
  iintro ⟨HR, Hglobal, Hresult⟩
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  iclear HR Hglobal Hresult
  ipureintro
  exact ⟨result, rfl⟩

theorem func10_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u64 1048552 0 ∗ pointsTo_u32 1048572 0 ∗
      runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func10, 1, [], [], []⟩ : Expr Unit) @ s; E
      {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨Hscratch, Hresult, Hruntime, Hglobal⟩
  simp only [func10]
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
  rw [← show checkAbsInnerBody =
    [ .localGet 0, .call 0, .localGet 0, .call 9,
      .f32Eq, .const 1, .and, .eqz, .br_if 0,
      .localGet 0, .call 0, .localGet 0, .call 2,
      .f32Eq, .const 1, .and, .eqz, .br_if 0,
      .localGet 1, .const 1, .store32 12, .br 1 ] by rfl]
  rw [← show checkAbsZeroProg =
    [.localGet 1, .const 0, .store32 12] by rfl]
  rw [← show checkAbsOuterBody =
    .block 0 0 checkAbsInnerBody :: checkAbsZeroProg by rfl]
  rw [← show checkAbsTailProg =
    [ .localGet 1, .load32 12, .localSet 2,
      .localGet 1, .const 16, .add, .globalSet 0,
      .localGet 2, .ret ] by rfl]
  iapply wp_block
  inext
  rw (occs := .pos [1]) [show checkAbsOuterBody =
    (.block 0 0 checkAbsInnerBody :: checkAbsZeroProg) by rfl]
  iapply wp_block
  inext
  simp only [List.drop_zero]
  rw [← show checkAbsInnerFrame =
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := checkAbsInnerBody
      continuation := checkAbsZeroProg
      belowStack := [] } by rfl]
  rw [← show checkAbsOuterFrame =
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := checkAbsOuterBody
      continuation := checkAbsTailProg
      belowStack := [] } by rfl]
  ihave HscratchSplit := innerScratch_split_zero $$ Hscratch
  icases HscratchSplit with ⟨Hlow, Hupper⟩
  iapply checkAbs_firstComparison_smallStep_wp
    (s := s) (E := E)
    x 0 0 _ _ _
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn «module»))
      x 0
    iframe
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module»))
      x 0
    iframe
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn «module»))
      x 1
    iframe
  · iframe

def checkAbsConfig (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func10, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

theorem checkAbs_smallStep (x : UInt32) :
    PartiallyMeets (checkAbsConfig x)
      (fun values _store => ∃ b : UInt32, values = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
      (α := Unit) (σ := exportHeap) (globalσ := func1Globals)
      (φ := fun values => ∃ b : UInt32, values = [.i32 b])
  · simpa [checkAbsConfig] using exportHeap_agrees
  · simpa [checkAbsConfig] using exportHeap_inBounds
  · simpa [checkAbsConfig, func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := exportHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hscratch, Hresult⟩
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [checkAbsConfig]
    iapply func10_body_smallStep_wp
    iframe

/-! ## Exported `check_copysign` -/

def checkCopysignTailProg : Program :=
  [ .localGet 2, .load32 12, .localSet 3,
    .localGet 2, .const 16, .add, .globalSet 0,
    .localGet 3, .ret ]

def checkCopysignInnerBody : Program :=
  [ .localGet 0, .localGet 1, .call 7,
    .localGet 0, .localGet 1, .call 4,
    .f32Eq, .const 1, .and, .br_if 0,
    .localGet 2, .const 0, .store32 12, .br 1 ]

def checkCopysignOneProg : Program :=
  [.localGet 2, .const 1, .store32 12]

def checkCopysignOuterBody : Program :=
  [.block 0 0 checkCopysignInnerBody] ++ checkCopysignOneProg

def checkCopysignOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := checkCopysignOuterBody
    continuation := checkCopysignTailProg
    belowStack := [] }

def checkCopysignInnerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := checkCopysignInnerBody
    continuation := checkCopysignOneProg
    belowStack := [] }

theorem checkCopysign_tail_result_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (R : IProp (WasmHeapGF Unit)) (x y result : UInt32) :
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
        checkCopysignTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkCopysignTailProg]
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

theorem checkCopysign_comparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x y upper oldResult : UInt32)
    (hzero :
      pointsTo_u32 1048552 0 ∗
        pointsTo_u32 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
          checkCopysignTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u32 1048552 0 ∗
        pointsTo_u32 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗ pointsTo_u32 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
          checkCopysignTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048556 upper ∗
      runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u32 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
        checkCopysignInnerBody, 1, [],
        [checkCopysignInnerFrame, checkCopysignOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  simp only [checkCopysignInnerBody]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_call «module» 7 func7Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func7Def, Function.toLocals, Function.numParams]
  iapply func7_lowered_smallStep_wp
    (iprop(pointsTo_u32 1048552 0 ∗ pointsTo_u32 1048572 oldResult))
    x y upper _ _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    iapply wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_call «module» 4 func4Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func4Def, Function.toLocals, Function.numParams]
    iapply func4_context_smallStep_wp
      (iprop(pointsTo_u32 1048552 0 ∗
        pointsTo_u32 1048556 (f32Copysign x y) ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u32 1048572 oldResult))
      x y _ _
    · iintro ⟨HR, Hruntime⟩
      iapply wp_returnFromCallExplicit
      inext
      simp only [List.take, List.singleton_append]
      icases HR with ⟨Hlow, Hupper, Hglobal, Hresult⟩
      by_cases heq :
          f32Eq (f32Copysign x y) (func4Result x y) = true
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
        simp only [checkCopysignInnerFrame, List.take, List.nil_append]
        simp only [checkCopysignOneProg]
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
        simp only [checkCopysignOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 ((1048560 : UInt32) + 12) 1 =
              pointsTo_u32 1048572 1 :=
          congrArg (fun address => pointsTo_u32 address 1) (by decide)
        ihave HresultExact : pointsTo_u32 1048572 1 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply hone
        iframe
      · have heqFalse :
            f32Eq (f32Copysign x y) (func4Result x y) = false := by
          cases h : f32Eq (f32Copysign x y) (func4Result x y) <;> simp_all
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
        simp only [checkCopysignOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 ((1048560 : UInt32) + 12) 0 =
              pointsTo_u32 1048572 0 :=
          congrArg (fun address => pointsTo_u32 address 0) (by decide)
        ihave HresultExact : pointsTo_u32 1048572 0 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply hzero
        iframe
    · iframe
  · iframe

theorem func11_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u64 1048552 0 ∗ pointsTo_u32 1048572 0 ∗
      runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0, .i32 0], []⟩,
        func11, 1, [], [], []⟩ : Expr Unit) @ s; E
      {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨Hscratch, Hresult, Hruntime, Hglobal⟩
  simp only [func11]
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
  rw [← show checkCopysignInnerBody =
    [ .localGet 0, .localGet 1, .call 7,
      .localGet 0, .localGet 1, .call 4,
      .f32Eq, .const 1, .and, .br_if 0,
      .localGet 2, .const 0, .store32 12, .br 1 ] by rfl]
  rw [← show checkCopysignOneProg =
    [.localGet 2, .const 1, .store32 12] by rfl]
  rw [← show checkCopysignOuterBody =
    .block 0 0 checkCopysignInnerBody :: checkCopysignOneProg by rfl]
  rw [← show checkCopysignTailProg =
    [ .localGet 2, .load32 12, .localSet 3,
      .localGet 2, .const 16, .add, .globalSet 0,
      .localGet 3, .ret ] by rfl]
  iapply wp_block
  inext
  rw (occs := .pos [1]) [show checkCopysignOuterBody =
    (.block 0 0 checkCopysignInnerBody :: checkCopysignOneProg) by rfl]
  iapply wp_block
  inext
  simp only [List.drop_zero]
  rw [← show checkCopysignInnerFrame =
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := checkCopysignInnerBody
      continuation := checkCopysignOneProg
      belowStack := [] } by rfl]
  rw [← show checkCopysignOuterFrame =
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := checkCopysignOuterBody
      continuation := checkCopysignTailProg
      belowStack := [] } by rfl]
  ihave HscratchSplit := innerScratch_split_zero $$ Hscratch
  icases HscratchSplit with ⟨Hlow, Hupper⟩
  iapply checkCopysign_comparison_smallStep_wp
    (s := s) (E := E)
    x y 0 0 _ _
  · iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
    iapply checkCopysign_tail_result_smallStep_wp
      (iprop(pointsTo_u32 1048552 0 ∗
        pointsTo_u32 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn «module»))
      x y 0
    iframe
  · iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
    iapply checkCopysign_tail_result_smallStep_wp
      (iprop(pointsTo_u32 1048552 0 ∗
        pointsTo_u32 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn «module»))
      x y 1
    iframe
  · iframe

def checkCopysignConfig (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [.i32 0, .i32 0], []⟩,
        func11, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

theorem checkCopysign_smallStep (x y : UInt32) :
    PartiallyMeets (checkCopysignConfig x y)
      (fun values _store => ∃ b : UInt32, values = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
      (α := Unit) (σ := exportHeap) (globalσ := func1Globals)
      (φ := fun values => ∃ b : UInt32, values = [.i32 b])
  · simpa [checkCopysignConfig] using exportHeap_agrees
  · simpa [checkCopysignConfig] using exportHeap_inBounds
  · simpa [checkCopysignConfig, func1Config] using func1Globals_agree
  · intro gs
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := exportHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hscratch, Hresult⟩
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [checkCopysignConfig]
    iapply func11_body_smallStep_wp
    iframe

-- after globalSet 0, the new global[0] holds the stored value
private theorem globals_set0 {st : Store Unit} {sp : UInt32} (sp' : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 sp)) :
    ({st with globals := {globals := st.globals.globals.set 0 (.i32 sp')}} : Store Unit).globals.globals[0]? = some (.i32 sp') := by
  cases h : st.globals.globals with
  | nil => simp [h] at hg
  | cons _ _ => rfl

-- frame at (sp-16)+N stays in bounds given sp >= 16 and sp <= pages*65536
private theorem frame_oob_false {sp : UInt32} {pages : Nat}
    (h16 : 16 <= sp.toNat) (hb : sp.toNat <= pages * 65536) :
    ¬ ((sp - 16).toNat + 12 + 4 > pages * 65536) := by
  have hle : (16 : UInt32) <= sp := UInt32.le_iff_toNat_le.mpr (by simpa using h16)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  rw [hsub]; omega

/-! ## func1: f32Abs via frame -/

private theorem func1_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 1 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func1, [.f32], some 0⟩) rfl
  unfold func1; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

/-! ## func3: f64Abs via frame -/

private theorem func3_term (env : HostEnv Unit) (st : Store Unit) (sp : UInt32) (x : UInt64)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 3 st ([.f64 x] ++ tail)
      (fun st' rs => ∃ v : UInt64, rs = [.f64 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f64], [.i32], func3, [.f64], some 1⟩) rfl
  unfold func3; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

/-! ## func5: i32ReinterpretF32 (pure) -/

private theorem func5_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 5 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.i32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func5, [.i32], some 3⟩) rfl
  unfold func5; wp_run
  exact ⟨x, rfl, hg, hp⟩

/-! ## func6: f32ReinterpretI32 (pure) -/

private theorem func6_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 6 st ([.i32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [], func6, [.f32], some 4⟩) rfl
  unfold func6; wp_run
  exact ⟨x, rfl, hg, hp⟩

/-! ## func0: abs wrapper (calls func1) -/

private theorem func0_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 0 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func0, [.f32], some 0⟩) rfl
  unfold func0; wp_run
  apply wp_call_tw (func1_term env st sp x [] hg hp h16 hb)
  rintro st1 vs1 ⟨v1, rfl, hg1, hp1⟩
  wp_run
  exact ⟨v1, rfl, hg1, hp1⟩

/-! ## func2: f64Abs wrapper via promotion (calls func3) -/

private theorem func2_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 2 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func2, [.f32], some 0⟩) rfl
  unfold func2; wp_run
  apply wp_call_tw (func3_term env st sp (f64PromoteF32 x) [] hg hp h16 hb)
  rintro st3 vs3 ⟨v3, rfl, hg3, hp3⟩
  wp_run
  exact ⟨f32DemoteF64 v3, rfl, hg3, hp3⟩

/-! ## func8: f32Copysign via frame (2 f32 params) -/

private theorem func8_term (env : HostEnv Unit) (st : Store Unit) (sp x y : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 8 st ([.f32 y, .f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [.i32], func8, [.f32], some 2⟩) rfl
  unfold func8; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

/-! ## func7: copysign wrapper (calls func8, 2 f32 params) -/

private theorem func7_term (env : HostEnv Unit) (st : Store Unit) (sp x y : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 7 st ([.f32 y, .f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [], func7, [.f32], some 2⟩) rfl
  unfold func7; wp_run
  apply wp_call_tw (func8_term env st sp x y [] hg hp h16 hb)
  rintro st8 vs8 ⟨v8, rfl, hg8, hp8⟩
  wp_run
  exact ⟨v8, rfl, hg8, hp8⟩

/-! ## func9: abs via bit manipulation (calls func5, func6) -/

private theorem func9_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 9 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func9, [.f32], some 0⟩) rfl
  unfold func9; wp_run
  apply wp_call_tw (func5_term env st sp x [] hg hp)
  rintro st5 vs5 ⟨v5, rfl, hg5, hp5⟩
  wp_run
  apply wp_call_tw (func6_term env st5 sp (2147483647 &&& v5) [] hg5 hp5)
  rintro st6 vs6 ⟨v6, rfl, hg6, hp6⟩
  wp_run
  exact ⟨v6, rfl, hg6, hp6⟩

/-! ## func4: copysign via bit manipulation (calls func5 twice, func6; 2 f32 params) -/

private theorem func4_term (env : HostEnv Unit) (st : Store Unit) (sp x y : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 4 st ([.f32 y, .f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [], func4, [.f32], some 2⟩) rfl
  unfold func4; wp_run
  apply wp_call_tw (func5_term env st sp y [] hg hp)
  rintro st5 vs5 ⟨v5, rfl, hg5, hp5⟩
  wp_run
  apply wp_call_tw (func5_term env st5 sp x [.i32 (2147483648 &&& v5)] hg5 hp5)
  rintro st5' vs5' ⟨v5', rfl, hg5', hp5'⟩
  wp_run
  apply wp_call_tw
    (func6_term env st5' sp ((2147483648 &&& v5) ||| (2147483647 &&& v5')) [] hg5' hp5')
  rintro st6 vs6 ⟨v6, rfl, hg6, hp6⟩
  wp_run
  exact ⟨v6, rfl, hg6, hp6⟩

/-! ## FloatReinterpretSpec -/

@[spec_of "rust-exported" "float_reinterpret::float_reinterpret"]
def FloatReinterpretSpec : Prop :=
  (∀ (env : HostEnv Unit) (x : UInt32),
    TerminatesWith env «module» 10 «module».initialStore [.f32 x]
      (fun _ rs => ∃ b : UInt32, rs = [.i32 b])) ∧
  (∀ (env : HostEnv Unit) (x y : UInt32),
    TerminatesWith env «module» 11 «module».initialStore [.f32 y, .f32 x]
      (fun _ rs => ∃ b : UInt32, rs = [.i32 b]))

@[proves Project.FloatReinterpret.Spec.FloatReinterpretSpec]
theorem check_terminates : FloatReinterpretSpec := by
  constructor
  · -- check_abs
    intro env x
    have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := rfl
    have hp : («module».initialStore : Store Unit).mem.pages = 16 := rfl
    apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32, .i32], func10, [.i32], some 3⟩) rfl
    unfold func10; wp_run; simp only [hg]
    have hg10 : ({«module».initialStore with globals := {globals := «module».initialStore.globals.globals.set 0 (.i32 (1048576 - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (1048576 - 16)) :=
      globals_set0 (1048576 - 16) hg
    apply wp_block_cons; apply wp_block_cons
    wp_run
    apply wp_call_tw
      (func0_term env _ (1048576 - 16) x [] hg10 (by rfl) (by decide) (by decide))
    rintro st0 vs0 ⟨v0, rfl, hg0, hp0⟩
    wp_run
    apply wp_call_tw (func9_term env st0 (1048576 - 16) x [.f32 v0] hg0 hp0)
    rintro st9 vs9 ⟨v9, rfl, hg9, hp9⟩
    wp_run
    have hnt : ¬ ((1048576 - 16 : UInt32).toNat + 12 + 4 > 16 * 65536) := by decide
    have hrestored : (1048576 - 16 : UInt32) + 16 = 1048576 := by decide
    cases heq09 : f32Eq v0 v9
    · -- v0 ≠ v9: break inner → outer body: store 0
      simp [heq09]
      simp [hp9, hg9]
    · -- v0 = v9: continue; second comparison
      simp [heq09]
      apply wp_call_tw
        (func0_term env st9 (1048576 - 16) x [] hg9 hp9 (by decide) (by decide))
      rintro st0' vs0' ⟨v0', rfl, hg0', hp0'⟩
      wp_run
      apply wp_call_tw
        (func2_term env st0' (1048576 - 16) x [.f32 v0'] hg0' hp0' (by decide) (by decide))
      rintro st2 vs2 ⟨v2, rfl, hg2, hp2⟩
      wp_run
      cases heq02 : f32Eq v0' v2
      · -- v0' ≠ v2: break inner → outer body: store 0
        simp [heq02]
        simp [hp2, hg2]
      · -- v0' = v2: store 1, break outer
        simp [heq02]
        simp [hp2,hg2]
  · -- check_copysign
    intro env x y
    have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := rfl
    have hp : («module».initialStore : Store Unit).mem.pages = 16 := rfl
    apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [.i32, .i32], func11, [.i32], some 5⟩) rfl
    unfold func11; wp_run; simp only [hg]
    have hg11 : ({«module».initialStore with globals := {globals := «module».initialStore.globals.globals.set 0 (.i32 (1048576 - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (1048576 - 16)) :=
      globals_set0 (1048576 - 16) hg
    apply wp_block_cons; apply wp_block_cons
    wp_run
    apply wp_call_tw
      (func7_term env _ (1048576 - 16) x y [] hg11 (by rfl) (by decide) (by decide))
    rintro st7 vs7 ⟨v7, rfl, hg7, hp7⟩
    wp_run
    apply wp_call_tw (func4_term env st7 (1048576 - 16) x y [.f32 v7] hg7 hp7)
    rintro st4 vs4 ⟨v4, rfl, hg4, hp4⟩
    wp_run
    have hnt : ¬ ((1048576 - 16 : UInt32).toNat + 12 + 4 > 16 * 65536) := by decide
    have hrestored : (1048576 - 16 : UInt32) + 16 = 1048576 := by decide
    cases heq : f32Eq v7 v4
    · -- v7 ≠ v4: store 0, break outer
      simp [heq]
      simp [hp4, hg4]
    · -- v7 = v4: break inner → outer body: store 1
      simp [heq]
      simp [hp4, hg4]


end Project.FloatReinterpret.Spec
