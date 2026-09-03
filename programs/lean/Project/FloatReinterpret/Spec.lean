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
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
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
  wasm_wp_pures [wp_localGet]
  iapply wp_scalarFloat1 rfl rfl
  iexact Hret

theorem func5_smallStep (x : UInt32) :
    PartiallyMeets (func5Config x)
      (fun rs _store => rs = [.i32 x]) := by
  apply wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [func5Config]
  wasm_wp_next func5_body_smallStep_wp x []
  wasm_wp_return_value_rfl

def func6Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.i32 x], [], []⟩, func6, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
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
  wasm_wp_pures [wp_localGet]
  iapply wp_scalarFloat1 rfl rfl
  iexact Hret

theorem func6_smallStep (x : UInt32) :
    PartiallyMeets (func6Config x)
      (fun rs _store => rs = [.f32 x]) := by
  apply wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [func6Config]
  wasm_wp_next func6_body_smallStep_wp x []
  wasm_wp_return_value_rfl

def func9Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func9, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

/-- Complete small-step Iris proof for the bit-manipulation implementation of
`f32.abs`. The two reinterpret calls are composed through their actual saved
call frames. -/
theorem func9_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x : UInt32) :
    runtimeModuleOwn ⟨0⟩ «module» ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩, func9, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (2147483647 &&& x)]⌝ }} := by
  iintro Hruntime
  simp only [func9]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  wasm_wp_next func5_body_smallStep_wp x _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_wp_pures [wp_const wp_and]
  wasm_wp_next wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm x 2147483647]
  wasm_wp_next func6_body_smallStep_wp (2147483647 &&& x) _
  wasm_wp_return_from_call Hruntime
  wasm_wp_return_value
  iclear Hruntime
  ipureexact rfl

theorem func9_smallStep (x : UInt32) :
    PartiallyMeets (func9Config x)
      (fun rs _store => rs = [.f32 (2147483647 &&& x)]) := by
  apply wasm_smallStep_runtime_partiallyMeets (α := Unit)
  · simp only [func9Config]; decide
  · intro gs
    simp only [func9Config, RuntimeEnv.currentModule_mk1]
    iapply func9_smallStep_wp

def func4Result (x y : UInt32) : UInt32 :=
  (2147483648 &&& y) ||| (2147483647 &&& x)

def func4Config (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func4, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

/-- Complete small-step Iris proof for the bit-manipulation implementation of
`f32.copysign`. -/
theorem func4_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x y : UInt32) :
    runtimeModuleOwn ⟨0⟩ «module» ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func4, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (func4Result x y)]⌝ }} := by
  iintro Hruntime
  simp only [func4]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  wasm_wp_next func5_body_smallStep_wp y _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_wp_pures [wp_const wp_and wp_localGet]
  wasm_wp_next wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  wasm_wp_next func5_body_smallStep_wp x _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_wp_pures [wp_const wp_and wp_or]
  wasm_wp_next wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  simp only [func4Result]
  rw [UInt32.and_comm y 2147483648, UInt32.and_comm x 2147483647]
  wasm_wp_next func6_body_smallStep_wp
    ((2147483648 &&& y) ||| (2147483647 &&& x)) _
  wasm_wp_return_from_call Hruntime
  wasm_wp_return_value
  iclear Hruntime
  ipureexact rfl

theorem func4_smallStep (x y : UInt32) :
    PartiallyMeets (func4Config x y)
      (fun rs _store => rs = [.f32 (func4Result x y)]) := by
  apply wasm_smallStep_runtime_partiallyMeets (α := Unit)
  · simp only [func4Config]; decide
  · intro gs
    simp only [func4Config, RuntimeEnv.currentModule_mk1]
    iapply func4_smallStep_wp

/-! ## Authoritative frame-backed `f32.abs` -/

def func1Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [.i32 0], []⟩, func1, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

def func1Heap : WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 1048572 0

def func1Globals : WasmGlobalMap Value :=
  insert ∅ ⟨0, 0⟩ (.i32 1048576)

theorem func1Heap_agrees :
    heapAgreesWithMem func1Heap (storeResolve (func1Config 0).store) := by
  unfold func1Heap
  have h := store32_sound0 (∅ : WasmHeapMap (Option UInt8))
      («module».initialStore : Store Unit).mem 1048572 0
      (by decide) (by decide) (by decide)
      (heapAgreesWithMem_empty _)
  rw [Mem.write32_eq_self (by decide) (by decide) (by decide) (by decide)] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func1Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func1Config]
    · simp [h0, storeResolve, func1Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

theorem func1Heap_inBounds :
    heapAddressesInBounds func1Heap (storeResolve (func1Config 0).store) := by
  unfold func1Heap
  have h := store32_inBounds0 (∅ : WasmHeapMap (Option UInt8))
      («module».initialStore : Store Unit).mem 1048572 0
      (by decide) (by decide) (by decide) (by decide)
      (heapAddressesInBounds_empty _)
  rw [Mem.write32_eq_self (by decide) (by decide) (by decide) (by decide)] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func1Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func1Config]
    · simp [h0, storeResolve, func1Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

theorem func1Globals_agree :
    globalHeapAgrees func1Globals (func1Config 0).store.wasm.globals := by
  intro index value hget
  simp only [func1Globals] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (show (⟨0, 0⟩ : GlobalKey) ≠ ⟨0, index⟩ from
          fun h => hindex (congrArg GlobalKey.index h).symm),
        get?_empty] at hget
    contradiction

theorem func1Heap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func1Heap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 1048572 0 := by
  unfold func1Heap
  simpa only [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq] using
    (store32Heap_pointsTo (∅ : WasmHeapMap (Option UInt8))
      0 1048572 0
      (get?_empty _) (get?_empty _) (get?_empty _) (get?_empty _)
      (by decide) (by decide) (by decide))

theorem func1Globals_pointsTo [WasmGlobalGS Unit] :
    ([∗map] index ↦ value ∈ func1Globals,
      globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576) := by
  unfold func1Globals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  simp only [globalPointsToAt_eq]
  rfl

theorem func1_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u32 0 1048572 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u32 0 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func1]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next wp_scalarFloat1 rfl rfl
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldWord $$ [Hword]
  · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hword
  wasm_wp_next wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  wasm_wp_pures [wp_localGet]
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) (f32Abs x) $$ [Hword]
  · ilater_exact Hword
  wasm_wp_next wp_f32Load (f32Abs x)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) (f32Abs x) =
        pointsTo_u32 0 1048572 (f32Abs x) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Abs x)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048572 (f32Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply_frame hreturn

theorem func1_smallStep (x : UInt32) :
    PartiallyMeets (func1Config x)
      (fun rs _store => rs = [.f32 (f32Abs x)]) := by
  apply wasm_smallStep_heap_globals_partiallyMeets
    (α := Unit) (σ := func1Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f32 (f32Abs x)])
  · simpa [func1Config] using func1Heap_agrees
  · simpa [func1Config] using func1Heap_inBounds
  · simpa [func1Config] using func1Globals_agree
  · simp only [func1Config]; decide
  · intro gs
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func1Config]
    iapply func1_body_smallStep_wp (iprop(True)) x 0 []
    · iintro ⟨_Htrue, Hglobal, Hword⟩
      wasm_wp_return_value
      iclear Hglobal Hword
      ipureexact rfl
    · iframe

def func0Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func0, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

/-- Small-step Iris proof for the generated wrapper around the frame-backed
`f32.abs` implementation. -/
theorem func0_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x oldWord : UInt32) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u32 0 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩, func0, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (f32Abs x)]⌝ }} := by
  iintro ⟨Hruntime, Hglobal, Hword⟩
  simp only [func0]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func1_body_smallStep_wp
    (runtimeModuleOwn ⟨0⟩ «module») x oldWord _
  · iintro ⟨Hruntime, Hglobal, Hword⟩
    wasm_wp_return_from_call Hruntime
    wasm_wp_return_value
    iclear Hruntime Hglobal Hword
    ipureexact rfl
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
  · simp only [func0Config]; decide
  · intro gs
    simp only [func0Config, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    iapply_frame func0_smallStep_wp x 0

/-! ## Authoritative frame-backed `f64.abs` -/

def func3Config (x : UInt64) : Config Unit :=
  { expr := .running
      ⟨⟨[.f64 x], [.i32 0], []⟩, func3, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

def func3Heap : WasmHeapMap (Option UInt8) :=
  Wasm.RustStd.U64.absDiffHeap 0

theorem func3_initialScratchMem_eq :
    («module».initialStore : Store Unit).mem.write64 1048568 0 =
      («module».initialStore : Store Unit).mem := by
  simp [«module», Module.initialStore, Mem.write64, Mem.empty]

theorem func3Heap_agrees :
    heapAgreesWithMem func3Heap (storeResolve (func3Config 0).store) := by
  unfold func3Heap func3Config Wasm.RustStd.U64.absDiffHeap
  have h := store64_sound0 (∅ : WasmHeapMap (Option UInt8))
      («module».initialStore : Store Unit).mem 1048568 0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (heapAgreesWithMem_empty _)
  rw [func3_initialScratchMem_eq] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func3Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func3Config]
    · simp [h0, storeResolve, func3Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  exact hresolveEq ▸ h

theorem func3Heap_inBounds :
    heapAddressesInBounds func3Heap (storeResolve (func3Config 0).store) := by
  unfold func3Heap func3Config Wasm.RustStd.U64.absDiffHeap
  have h := store64_inBounds0 (∅ : WasmHeapMap (Option UInt8))
      («module».initialStore : Store Unit).mem 1048568 0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
      (heapAddressesInBounds_empty _)
  rw [func3_initialScratchMem_eq] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func3Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func3Config]
    · simp [h0, storeResolve, func3Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  exact hresolveEq ▸ h

theorem func3Heap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func3Heap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048568 0 := by
  exact Wasm.RustStd.U64.absDiffHeap_pointsTo 0

theorem func3_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u64 0 1048568 (f64Abs x) ⊢
      WP (.running
        ⟨⟨[.f64 x], [.i32 1048560], [.f64 (f64Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u64 0 1048568 oldWord ⊢
    WP (.running
      ⟨⟨[.f64 x], [.i32 0], []⟩,
        func3, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func3]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next wp_scalarFloat1 rfl rfl
  ihave HwordLater :
      ▷ pointsTo_u64 0 ((1048560 : UInt32) + 8) oldWord $$ [Hword]
  · ilater_rw_exact [show (1048560 : UInt32) + 8 = 1048568 by decide] with Hword
  wasm_wp_next wp_f64Store oldWord
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  wasm_wp_pures [wp_localGet]
  ihave HwordLater :
      ▷ pointsTo_u64 0 ((1048560 : UInt32) + 8) (f64Abs x) $$ [Hword]
  · ilater_exact Hword
  wasm_wp_next wp_f64Load (f64Abs x)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  have hWordProp :
      pointsTo_u64 0 ((1048560 : UInt32) + 8) (f64Abs x) =
        pointsTo_u64 0 1048568 (f64Abs x) :=
    congrArg (fun address => pointsTo_u64 0 address (f64Abs x)) (by decide)
  ihave HwordExact : pointsTo_u64 0 1048568 (f64Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply_frame hreturn

theorem func3_smallStep (x : UInt64) :
    PartiallyMeets (func3Config x)
      (fun rs _store => rs = [.f64 (f64Abs x)]) := by
  apply wasm_smallStep_heap_globals_partiallyMeets
    (α := Unit) (σ := func3Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f64 (f64Abs x)])
  · simpa [func3Config] using func3Heap_agrees
  · simpa [func3Config] using func3Heap_inBounds
  · simpa [func3Config, func1Config] using func1Globals_agree
  · simp only [func3Config]; decide
  · intro gs
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hword := func3Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func3Config]
    iapply func3_body_smallStep_wp (iprop(True)) x 0 []
    · iintro ⟨_Htrue, Hglobal, Hword⟩
      wasm_wp_return_value
      iclear Hglobal Hword
      ipureexact rfl
    · iframe

def func2Result (x : UInt32) : UInt32 :=
  f32DemoteF64 (f64Abs (f64PromoteF32 x))

def func2Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func2, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

/-- Small-step Iris proof for the generated promote/`f64.abs`/demote wrapper. -/
theorem func2_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x : UInt32) (oldWord : UInt64) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u64 0 1048568 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩, func2, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (func2Result x)]⌝ }} := by
  iintro ⟨Hruntime, Hglobal, Hword⟩
  simp only [func2]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_scalarFloat1 rfl rfl
  wasm_wp_next wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func3_body_smallStep_wp
    (runtimeModuleOwn ⟨0⟩ «module») (f64PromoteF32 x) oldWord _
  · iintro ⟨Hruntime, Hglobal, Hword⟩
    wasm_wp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_next wp_scalarFloat1 rfl rfl
    wasm_wp_return_value
    iclear Hruntime Hglobal Hword
    ipureexact rfl
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
  · simp only [func2Config]; decide
  · intro gs
    simp only [func2Config, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func3Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    iapply_frame func2_smallStep_wp x 0

/-! ## Authoritative frame-backed `f32.copysign` -/

def func8Config (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [.i32 0], []⟩, func8, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

theorem func8_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u32 0 1048572 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560],
            [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u32 0 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0], []⟩,
        func8, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func8]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_localGet wp_localGet]
  wasm_wp_next wp_scalarFloat2 rfl rfl rfl
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldWord $$ [Hword]
  · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hword
  wasm_wp_next wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  wasm_wp_pures [wp_localGet]
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) (f32Copysign x y) $$ [Hword]
  · ilater_exact Hword
  wasm_wp_next wp_f32Load (f32Copysign x y)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) (f32Copysign x y) =
        pointsTo_u32 0 1048572 (f32Copysign x y) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Copysign x y)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048572 (f32Copysign x y) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply_frame hreturn

theorem func8_smallStep (x y : UInt32) :
    PartiallyMeets (func8Config x y)
      (fun rs _store => rs = [.f32 (f32Copysign x y)]) := by
  apply wasm_smallStep_heap_globals_partiallyMeets
    (α := Unit) (σ := func1Heap) (globalσ := func1Globals)
    (φ := fun rs => rs = [.f32 (f32Copysign x y)])
  · simpa [func8Config, func1Config] using func1Heap_agrees
  · simpa [func8Config, func1Config] using func1Heap_inBounds
  · simpa [func8Config, func1Config] using func1Globals_agree
  · simp only [func8Config]; decide
  · intro gs
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    simp only [func8Config]
    iapply func8_body_smallStep_wp (iprop(True)) x y 0 []
    · iintro ⟨_Htrue, Hglobal, Hword⟩
      wasm_wp_return_value
      iclear Hglobal Hword
      ipureexact rfl
    · iframe

def func7Config (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func7, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

theorem func7_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x y oldWord : UInt32) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u32 0 1048572 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩, func7, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      {{ rs, ⌜rs = [.f32 (f32Copysign x y)]⌝ }} := by
  iintro ⟨Hruntime, Hglobal, Hword⟩
  simp only [func7]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next wp_call «module» 8 func8Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func8Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func8_body_smallStep_wp
    (runtimeModuleOwn ⟨0⟩ «module») x y oldWord _
  · iintro ⟨Hruntime, Hglobal, Hword⟩
    wasm_wp_return_from_call Hruntime
    wasm_wp_return_value
    iclear Hruntime Hglobal Hword
    ipureexact rfl
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
  · simp only [func7Config]; decide
  · intro gs
    simp only [func7Config, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func1Heap_pointsTo $$ Hbytes
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    iapply_frame func7_smallStep_wp x y 0

/-! ## Combined ownership for the exported checks

The exports allocate an outer 16-byte frame. Calls made beneath that frame
allocate one more 16-byte frame, so the widest inner scratch slot is the
eight-byte range at `1048552`; the outer check result is the disjoint word at
`1048572`. -/

def exportHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store64Heap ∅ 0 1048552 0) 0 1048572 0

def exportMem (memory : Mem) : Mem :=
  (memory.write64 1048552 0).write32 1048572 0

theorem export_initialMem_eq :
    exportMem («module».initialStore : Store Unit).mem =
      («module».initialStore : Store Unit).mem := by
  simp [exportMem, «module», Module.initialStore, Mem.write64,
    Mem.write32, Mem.empty]

theorem exportHeap_agrees :
    heapAgreesWithMem exportHeap (storeResolve (func1Config 0).store) := by
  unfold exportHeap
  have h := store32_sound0 (store64Heap ∅ 0 1048552 0)
      ((«module».initialStore : Store Unit).mem.write64 1048552 0) 1048572 0
      (by decide) (by decide) (by decide)
      (store64_sound0 (∅ : WasmHeapMap (Option UInt8))
          («module».initialStore : Store Unit).mem 1048552 0
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (heapAgreesWithMem_empty _))
  have hrw : ((«module».initialStore : Store Unit).mem.write64 1048552 0).write32 1048572 0 =
      («module».initialStore : Store Unit).mem := by
    have := export_initialMem_eq; unfold exportMem at this; exact this
  rw [hrw] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func1Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func1Config]
    · simp [h0, storeResolve, func1Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

theorem exportHeap_inBounds :
    heapAddressesInBounds exportHeap (storeResolve (func1Config 0).store) := by
  unfold exportHeap
  have h := store32_inBounds0 (store64Heap ∅ 0 1048552 0)
      ((«module».initialStore : Store Unit).mem.write64 1048552 0) 1048572 0
      (by decide) (by decide) (by decide) (by decide)
      (store64_inBounds0 (∅ : WasmHeapMap (Option UInt8))
          («module».initialStore : Store Unit).mem 1048552 0
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)
          (heapAddressesInBounds_empty _))
  have hrw : ((«module».initialStore : Store Unit).mem.write64 1048552 0).write32 1048572 0 =
      («module».initialStore : Store Unit).mem := by
    have := export_initialMem_eq; unfold exportMem at this; exact this
  rw [hrw] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func1Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func1Config]
    · simp [h0, storeResolve, func1Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

theorem exportHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ exportHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 0 ∗ pointsTo_u32 0 1048572 0 := by
  unfold exportHeap
  iintro Hheap
  ihave Houter := store32Heap_pointsTo
    (store64Heap ∅ 0 1048552 0) 0 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Houter with ⟨Houter, HinnerHeap⟩
  ihave Hinner := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HinnerHeap
  icases Hinner with ⟨Hinner, Hempty⟩
  iframe

def packUpper32 (upper : UInt32) : UInt64 :=
  upper.toUInt64 <<< 32

theorem innerScratch_split_zero [WasmHeapGS Unit] :
    pointsTo_u64 0 1048552 0 ⊢
      pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 0 := by
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
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  iframe

theorem innerScratch_merge_upper [WasmHeapGS Unit] (upper : UInt32) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 upper ⊢
      pointsTo_u64 0 1048552 (packUpper32 upper) := by
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
  iintro ⟨Hlow, Hhigh⟩
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
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048544], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func1]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next wp_scalarFloat1 rfl rfl
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · ilater_rw_exact [show (1048544 : UInt32) + 12 = 1048556 by decide] with Hword
  wasm_wp_next wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  wasm_wp_pures [wp_localGet]
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Abs x) $$ [Hword]
  · ilater_exact Hword
  wasm_wp_next wp_f32Load (f32Abs x)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Abs x) =
        pointsTo_u32 0 1048556 (f32Abs x) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Abs x)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply_frame hreturn

theorem func0_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func0, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func0]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func1_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»)) x oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    wasm_wp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    iapply_frame hreturn
  · iframe

/-- `func3` under an export's already-lowered stack pointer. -/
theorem func3_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 (f64Abs x) ⊢
      WP (.running
        ⟨⟨[.f64 x], [.i32 1048544], [.f64 (f64Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldWord ⊢
    WP (.running
      ⟨⟨[.f64 x], [.i32 0], []⟩,
        func3, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func3]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next wp_scalarFloat1 rfl rfl
  ihave HwordLater :
      ▷ pointsTo_u64 0 ((1048544 : UInt32) + 8) oldWord $$ [Hword]
  · ilater_rw_exact [show (1048544 : UInt32) + 8 = 1048552 by decide] with Hword
  wasm_wp_next wp_f64Store oldWord
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  wasm_wp_pures [wp_localGet]
  ihave HwordLater :
      ▷ pointsTo_u64 0 ((1048544 : UInt32) + 8) (f64Abs x) $$ [Hword]
  · ilater_exact Hword
  wasm_wp_next wp_f64Load (f64Abs x)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  have hWordProp :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) (f64Abs x) =
        pointsTo_u64 0 1048552 (f64Abs x) :=
    congrArg (fun address => pointsTo_u64 0 address (f64Abs x)) (by decide)
  ihave HwordExact : pointsTo_u64 0 1048552 (f64Abs x) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply_frame hreturn

theorem func2_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32) (oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (func2Result x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func2, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func2]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_scalarFloat1 rfl rfl
  wasm_wp_next wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func3_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»))
    (f64PromoteF32 x) oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    wasm_wp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_next wp_scalarFloat1 rfl rfl
    simp only [func2Result] at hreturn
    iapply_frame hreturn
  · iframe

/-- `func8` under an export's already-lowered stack pointer. -/
theorem func8_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048544],
            [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0], []⟩,
        func8, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func8]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_localGet wp_localGet]
  wasm_wp_next wp_scalarFloat2 rfl rfl rfl
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · ilater_rw_exact [show (1048544 : UInt32) + 12 = 1048556 by decide] with Hword
  wasm_wp_next wp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  wasm_wp_pures [wp_localGet]
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Copysign x y) $$ [Hword]
  · ilater_exact Hword
  wasm_wp_next wp_f32Load (f32Copysign x y)
    (by decide) (by decide) (by decide) (by decide) $$ HwordLater
  iintro Hword
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Copysign x y) =
        pointsTo_u32 0 1048556 (f32Copysign x y) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Copysign x y)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Copysign x y) $$ [Hword]
  · rw [← hWordProp]
    iexact Hword
  iapply_frame hreturn

theorem func7_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [], [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩,
        func7, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func7]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next wp_call «module» 8 func8Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func8Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply func8_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»)) x y oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    wasm_wp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    iapply_frame hreturn
  · iframe

theorem func9_context_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (2147483647 &&& x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func9, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime⟩
  simp only [func9]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  wasm_wp_next func5_body_smallStep_wp x _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_wp_pures [wp_const wp_and]
  wasm_wp_next wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm x 2147483647]
  wasm_wp_next func6_body_smallStep_wp (2147483647 &&& x) _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  iapply_frame hreturn

theorem func4_context_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [], [.f32 (func4Result x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩,
        func4, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime⟩
  simp only [func4]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  wasm_wp_next func5_body_smallStep_wp y _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_wp_pures [wp_const wp_and wp_localGet]
  wasm_wp_next wp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  wasm_wp_next func5_body_smallStep_wp x _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_wp_pures [wp_const wp_and wp_or]
  wasm_wp_next wp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm y 2147483648, UInt32.and_comm x 2147483647]
  wasm_wp_next func6_body_smallStep_wp
    ((2147483648 &&& y) ||| (2147483647 &&& x)) _
  wasm_wp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  rw [← show func4Result x y =
    (2147483648 &&& y) ||| (2147483647 &&& x) by rfl]
  iapply_frame hreturn

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
      R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u32 0 1048572 result ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 result], [.i32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsTailProg, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkAbsTailProg]
  wasm_wp_pures [wp_localGet]
  ihave HresultLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) result $$ [Hresult]
  · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hresult
  wasm_wp_next wp_load32 result
    (by decide) (by decide) (by decide) (by decide) $$ HresultLater
  iintro Hresult
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_const wp_add]
  rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
  ihave HglobalLater :
      ▷ globalPointsToAt 0 0 (.i32 1048560) $$ [Hglobal]
  · ilater_exact Hglobal
  wasm_wp_next_bind wp_globalSet with HglobalLater => Hglobal
  wasm_wp_pures [wp_localGet]
  have hResultProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) result =
        pointsTo_u32 0 1048572 result :=
    congrArg (fun address => pointsTo_u32 0 address result) (by decide)
  ihave HresultExact : pointsTo_u32 0 1048572 result $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  iapply_frame hreturn

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
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsZeroProg, 1, [], [checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkAbsZeroProg]
  wasm_wp_pures [wp_localGet wp_const]
  ihave HresultLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
  · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hresult
  wasm_wp_next wp_store32 oldResult
    (by decide) (by decide) (by decide) (by decide) $$ HresultLater
  iintro Hresult
  wasm_wp_pures [wp_exitControl]
  simp only [checkAbsOuterFrame, List.take, List.nil_append]
  have hResultProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) 0 =
        pointsTo_u32 0 1048572 0 :=
    congrArg (fun address => pointsTo_u32 0 address 0) (by decide)
  ihave HresultExact : pointsTo_u32 0 1048572 0 $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  iapply_frame hcontinue

theorem checkAbs_onePath_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldResult : UInt32)
    (hcontinue :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        [.localGet 1, .const 1, .store32 12, .br 1],
        1, [], [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  wasm_wp_pures [wp_localGet wp_const]
  ihave HresultLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
  · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hresult
  wasm_wp_next wp_store32 oldResult
    (by decide) (by decide) (by decide) (by decide) $$ HresultLater
  iintro Hresult
  wasm_wp_pures [wp_br]
  simp only [checkAbsOuterFrame, List.take, List.nil_append]
  have hResultProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) 1 =
        pointsTo_u32 0 1048572 1 :=
    congrArg (fun address => pointsTo_u32 0 address 1) (by decide)
  ihave HresultExact : pointsTo_u32 0 1048572 1 $$ [Hresult]
  · rw [← hResultProp]
    iexact Hresult
  iapply_frame hcontinue

def checkAbsSecondProg : Program :=
  [ .localGet 0, .call 0, .localGet 0, .call 2,
    .f32Eq, .const 1, .and, .eqz, .br_if 0,
    .localGet 1, .const 1, .store32 12, .br 1 ]

theorem checkAbs_secondComparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x upper oldResult : UInt32)
    (hzero :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 upper ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        [ .localGet 0, .call 0, .localGet 0, .call 2,
          .f32Eq, .const 1, .and, .eqz, .br_if 0,
          .localGet 1, .const 1, .store32 12, .br 1 ],
        1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams]
  iapply func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048572 oldResult))
    x upper _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    wasm_wp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_pures [wp_localGet]
    wasm_wp_next wp_call «module» 2 func2Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    iintro Hruntime
    icombine Hlow Hupper as Hscratch
    ihave Hpacked := innerScratch_merge_upper (f32Abs x) $$ Hscratch
    simp [func2Def, Function.toLocals, Function.numParams]
    iapply func2_lowered_smallStep_wp
      (iprop(pointsTo_u32 0 1048572 oldResult))
      x (packUpper32 (f32Abs x)) _
    · iintro ⟨Hresult, Hruntime, Hglobal, Hscratch⟩
      wasm_wp_return_from_call Hruntime
      simp only [List.take, List.singleton_append]
      by_cases heq :
          f32Eq (f32Abs x) (func2Result x) = true
      · iapply wp_scalarFloat2 (value := .i32 1) rfl rfl
          (by simp [evalScalarFloat2?, heq])
        inext
        wasm_wp_pures [wp_const wp_and]
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        wasm_wp_next wp_eqz (result := 0) (by decide)
        wasm_wp_pures [wp_brIfZero]
        iapply checkAbs_onePath_smallStep_wp
          (iprop(pointsTo_u64 0 1048552
            (f64Abs (f64PromoteF32 x)) ∗ runtimeModuleOwn ⟨0⟩ «module»))
          x oldResult _
        · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
          iapply_frame hone
        · iframe
      · have heqFalse :
            f32Eq (f32Abs x) (func2Result x) = false := by
          cases h : f32Eq (f32Abs x) (func2Result x) <;> simp_all
        wasm_wp_next wp_scalarFloat2 (value := .i32 0) rfl rfl
          (by simp [evalScalarFloat2?, heqFalse])
        wasm_wp_pures [wp_const wp_and]
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        wasm_wp_next wp_eqz (result := 1) (by decide)
        wasm_wp_next wp_brIf (by decide) rfl
        simp only [checkAbsInnerFrame, List.take, List.nil_append]
        iapply checkAbs_zeroPath_smallStep_wp
          (iprop(pointsTo_u64 0 1048552
            (f64Abs (f64PromoteF32 x)) ∗ runtimeModuleOwn ⟨0⟩ «module»))
          x oldResult _
        · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
          iapply_frame hzero
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
      pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hzeroSecond :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 (f32Abs x) ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
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
    wasm_wp_pures [wp_const wp_and]
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    wasm_wp_next wp_eqz (result := 0) (by decide)
    wasm_wp_pures [wp_brIfZero]
    iapply checkAbs_secondComparison_smallStep_wp
      (s := s) (E := E) (Φ := Φ)
      x (f32Abs x) oldResult _ _
    · exact hzeroSecond
    · exact hone
    · iframe
  · have heqFalse :
        f32Eq (f32Abs x) (2147483647 &&& x) = false := by
      cases h : f32Eq (f32Abs x) (2147483647 &&& x) <;> simp_all
    wasm_wp_next wp_scalarFloat2 (value := .i32 0) rfl rfl
      (by simp [evalScalarFloat2?, heqFalse])
    wasm_wp_pures [wp_const wp_and]
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    wasm_wp_next wp_eqz (result := 1) (by decide)
    wasm_wp_next wp_brIf (by decide) rfl
    simp only [checkAbsInnerFrame, List.take, List.nil_append]
    icombine Hlow Hupper as Hscratch
    ihave Hpacked := innerScratch_merge_upper (f32Abs x) $$ Hscratch
    iapply checkAbs_zeroPath_smallStep_wp
      (iprop(pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x oldResult _
    · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
      iapply_frame hzeroFirst
    · iframe

theorem checkAbs_firstComparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x upper oldResult : UInt32)
    (hzeroFirst :
      pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hzeroSecond :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 upper ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsInnerBody, 1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  simp only [checkAbsInnerBody]
  wasm_wp_pures [wp_localGet]
  wasm_wp_next wp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams]
  iapply func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048572 oldResult))
    x upper _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    wasm_wp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_pures [wp_localGet]
    wasm_wp_next wp_call «module» 9 func9Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    iintro Hruntime
    simp [func9Def, Function.toLocals, Function.numParams]
    iapply func9_context_smallStep_wp
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Abs x) ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 oldResult))
      x _ _
    · iintro ⟨HR, Hruntime⟩
      wasm_wp_return_from_call Hruntime
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
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iapply checkAbs_tail_smallStep_wp R x result [] _
  iintro ⟨HR, Hglobal, Hresult⟩
  wasm_wp_return_value
  iclear HR Hglobal Hresult
  ipureexact ⟨result, rfl⟩

theorem func10_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u64 0 1048552 0 ∗ pointsTo_u32 0 1048572 0 ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func10, 1, [], [], []⟩ : Expr Unit) @ s; E
      {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨Hscratch, Hresult, Hruntime, Hglobal⟩
  simp only [func10]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet]
  ihave HglobalLater : ▷ globalPointsToAt 0 0 (.i32 1048576) $$ [Hglobal]
  · ilater_exact Hglobal
  wasm_wp_next_bind wp_globalSet with HglobalLater => Hglobal
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
  wasm_wp_pures [wp_block]
  rw (occs := .pos [1]) [show checkAbsOuterBody =
    (.block 0 0 checkAbsInnerBody :: checkAbsZeroProg) by rfl]
  wasm_wp_pures [wp_block]
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
      (iprop(pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x 0
    iframe
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x 0
    iframe
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x 1
    iframe
  · iframe

def checkAbsConfig (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func10, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

theorem checkAbs_smallStep (x : UInt32) :
    PartiallyMeets (checkAbsConfig x)
      (fun values _store => ∃ b : UInt32, values = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
      (α := Unit) (σ := exportHeap) (globalσ := func1Globals)
      (φ := fun values => ∃ b : UInt32, values = [.i32 b])
  · simpa [checkAbsConfig, func1Config] using exportHeap_agrees
  · simpa [checkAbsConfig, func1Config] using exportHeap_inBounds
  · simpa [checkAbsConfig, func1Config] using func1Globals_agree
  · simp only [checkAbsConfig]; decide
  · intro gs
    simp only [checkAbsConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := exportHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hscratch, Hresult⟩
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    iapply_frame func10_body_smallStep_wp

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
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
        checkCopysignTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkCopysignTailProg]
  wasm_wp_pures [wp_localGet]
  ihave HresultLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) result $$ [Hresult]
  · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hresult
  wasm_wp_next wp_load32 result
    (by decide) (by decide) (by decide) (by decide) $$ HresultLater
  iintro Hresult
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_const wp_add]
  rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
  ihave HglobalLater :
      ▷ globalPointsToAt 0 0 (.i32 1048560) $$ [Hglobal]
  · ilater_exact Hglobal
  wasm_wp_next_bind wp_globalSet with HglobalLater => Hglobal
  wasm_wp_pures [wp_localGet]
  wasm_wp_return_value
  iclear HR Hglobal Hresult
  ipureexact ⟨result, rfl⟩

theorem checkCopysign_comparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x y upper oldResult : UInt32)
    (hzero :
      pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
          checkCopysignTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }})
    (hone :
      pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
          checkCopysignTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E {{ Φ }}) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 upper ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
        checkCopysignInnerBody, 1, [],
        [checkCopysignInnerFrame, checkCopysignOuterFrame], []⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  simp only [checkCopysignInnerBody]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next wp_call «module» 7 func7Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func7Def, Function.toLocals, Function.numParams]
  iapply func7_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048572 oldResult))
    x y upper _ _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    wasm_wp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_pures [wp_localGet wp_localGet]
    wasm_wp_next wp_call «module» 4 func4Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    iintro Hruntime
    simp [func4Def, Function.toLocals, Function.numParams]
    iapply func4_context_smallStep_wp
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 oldResult))
      x y _ _
    · iintro ⟨HR, Hruntime⟩
      wasm_wp_return_from_call Hruntime
      simp only [List.take, List.singleton_append]
      icases HR with ⟨Hlow, Hupper, Hglobal, Hresult⟩
      by_cases heq :
          f32Eq (f32Copysign x y) (func4Result x y) = true
      · iapply wp_scalarFloat2 (value := .i32 1) rfl rfl
          (by simp [evalScalarFloat2?, heq])
        inext
        wasm_wp_pures [wp_const wp_and]
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        wasm_wp_next wp_brIf (by decide) rfl
        simp only [checkCopysignInnerFrame, List.take, List.nil_append]
        simp only [checkCopysignOneProg]
        wasm_wp_pures [wp_localGet wp_const]
        ihave HresultLater :
            ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hresult
        wasm_wp_next wp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ HresultLater
        iintro Hresult
        wasm_wp_pures [wp_exitControl]
        simp only [checkCopysignOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 1 =
              pointsTo_u32 0 1048572 1 :=
          congrArg (fun address => pointsTo_u32 0 address 1) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 1 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply_frame hone
      · have heqFalse :
            f32Eq (f32Copysign x y) (func4Result x y) = false := by
          cases h : f32Eq (f32Copysign x y) (func4Result x y) <;> simp_all
        wasm_wp_next wp_scalarFloat2 (value := .i32 0) rfl rfl
          (by simp [evalScalarFloat2?, heqFalse])
        wasm_wp_pures [wp_const wp_and]
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        wasm_wp_pures [wp_brIfZero wp_localGet wp_const]
        ihave HresultLater :
            ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with Hresult
        wasm_wp_next wp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ HresultLater
        iintro Hresult
        wasm_wp_pures [wp_br]
        simp only [checkCopysignOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 0 =
              pointsTo_u32 0 1048572 0 :=
          congrArg (fun address => pointsTo_u32 0 address 0) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 0 $$ [Hresult]
        · rw [← hResultProp]
          iexact Hresult
        iapply_frame hzero
    · iframe
  · iframe

theorem func11_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u64 0 1048552 0 ∗ pointsTo_u32 0 1048572 0 ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0, .i32 0], []⟩,
        func11, 1, [], [], []⟩ : Expr Unit) @ s; E
      {{ values, ⌜∃ b : UInt32, values = [.i32 b]⌝ }} := by
  iintro ⟨Hscratch, Hresult, Hruntime, Hglobal⟩
  simp only [func11]
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub]
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  wasm_wp_pures [wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet]
  ihave HglobalLater : ▷ globalPointsToAt 0 0 (.i32 1048576) $$ [Hglobal]
  · ilater_exact Hglobal
  wasm_wp_next_bind wp_globalSet with HglobalLater => Hglobal
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
  wasm_wp_pures [wp_block]
  rw (occs := .pos [1]) [show checkCopysignOuterBody =
    (.block 0 0 checkCopysignInnerBody :: checkCopysignOneProg) by rfl]
  wasm_wp_pures [wp_block]
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
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x y 0
    iframe
  · iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
    iapply checkCopysign_tail_result_smallStep_wp
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x y 1
    iframe
  · iframe

def checkCopysignConfig (x y : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x, .f32 y], [.i32 0, .i32 0], []⟩,
        func11, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

theorem checkCopysign_smallStep (x y : UInt32) :
    PartiallyMeets (checkCopysignConfig x y)
      (fun values _store => ∃ b : UInt32, values = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
      (α := Unit) (σ := exportHeap) (globalσ := func1Globals)
      (φ := fun values => ∃ b : UInt32, values = [.i32 b])
  · simpa [checkCopysignConfig, func1Config] using exportHeap_agrees
  · simpa [checkCopysignConfig, func1Config] using exportHeap_inBounds
  · simpa [checkCopysignConfig, func1Config] using func1Globals_agree
  · simp only [checkCopysignConfig]; decide
  · intro gs
    simp only [checkCopysignConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := exportHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hscratch, Hresult⟩
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    iapply_frame func11_body_smallStep_wp

/-! ## TWP lifting lemmas -/

theorem twp_func5_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x : UInt32) (calls : List CallFrame) :
    WP (.running
      ⟨⟨[.f32 x], [], [.i32 x]⟩,
        [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func5, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  simp only [func5]
  iintro Hret
  wasm_twp_pures [twp_localGet]
  iapply twp_scalarFloat1 rfl rfl
  iexact Hret

theorem twp_func6_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x : UInt32) (calls : List CallFrame) :
    WP (.running
      ⟨⟨[.i32 x], [], [.f32 x]⟩,
        [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 x], [], []⟩,
        func6, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  simp only [func6]
  iintro Hret
  wasm_twp_pures [twp_localGet]
  iapply twp_scalarFloat1 rfl rfl
  iexact Hret

theorem twp_func1_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048544], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func1]
  wasm_twp_rebind twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub]
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  wasm_twp_pures [twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_scalarFloat1 rfl rfl
  ihave Hword' : pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply twp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword'
  wasm_twp_pures [twp_localGet]
  iapply twp_f32Load (f32Abs x)
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword'
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Abs x) =
        pointsTo_u32 0 1048556 (f32Abs x) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Abs x)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Abs x) $$ [Hword']
  · rw [← hWordProp]
    iexact Hword'
  iapply_frame hreturn

theorem twp_func0_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Abs x) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (f32Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func0, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func0]
  wasm_twp_pures [twp_localGet]
  iapply twp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func1_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»)) x oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    wasm_twp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    iapply_frame hreturn
  · iframe

theorem twp_func3_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 (f64Abs x) ⊢
      WP (.running
        ⟨⟨[.f64 x], [.i32 1048544], [.f64 (f64Abs x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldWord ⊢
    WP (.running
      ⟨⟨[.f64 x], [.i32 0], []⟩,
        func3, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func3]
  wasm_twp_rebind twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub]
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  wasm_twp_pures [twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_scalarFloat1 rfl rfl
  ihave Hword' : pointsTo_u64 0 ((1048544 : UInt32) + 8) oldWord $$ [Hword]
  · rw [show (1048544 : UInt32) + 8 = 1048552 by decide]
    iexact Hword
  iapply twp_f64Store oldWord
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword'
  wasm_twp_pures [twp_localGet]
  iapply twp_f64Load (f64Abs x)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword'
  have hWordProp :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) (f64Abs x) =
        pointsTo_u64 0 1048552 (f64Abs x) :=
    congrArg (fun address => pointsTo_u64 0 address (f64Abs x)) (by decide)
  ihave HwordExact : pointsTo_u64 0 1048552 (f64Abs x) $$ [Hword']
  · rw [← hWordProp]
    iexact Hword'
  iapply_frame hreturn

theorem twp_func2_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32) (oldWord : UInt64)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (func2Result x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func2, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func2]
  wasm_twp_pures [twp_localGet]
  iapply twp_scalarFloat1 rfl rfl
  iapply twp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func3_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»))
    (f64PromoteF32 x) oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    wasm_twp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    iapply twp_scalarFloat1 rfl rfl
    simp only [func2Result] at hreturn
    iapply_frame hreturn
  · iframe

theorem twp_func8_lowered_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048544],
            [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0], []⟩,
        func8, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  simp only [func8]
  wasm_twp_rebind twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub]
  rw [show (1048560 : UInt32) - 16 = 1048544 by decide]
  wasm_twp_pures [twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_scalarFloat2 rfl rfl rfl
  ihave Hword' : pointsTo_u32 0 ((1048544 : UInt32) + 12) oldWord $$ [Hword]
  · rw [show (1048544 : UInt32) + 12 = 1048556 by decide]
    iexact Hword
  iapply twp_f32Store oldWord
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword'
  wasm_twp_pures [twp_localGet]
  iapply twp_f32Load (f32Copysign x y)
    (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword'
  have hWordProp :
      pointsTo_u32 0 ((1048544 : UInt32) + 12) (f32Copysign x y) =
        pointsTo_u32 0 1048556 (f32Copysign x y) :=
    congrArg (fun address => pointsTo_u32 0 address (f32Copysign x y)) (by decide)
  ihave HwordExact : pointsTo_u32 0 1048556 (f32Copysign x y) $$ [Hword']
  · rw [← hWordProp]
    iexact Hword'
  iapply_frame hreturn

theorem twp_func7_lowered_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y oldWord : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [], [.f32 (f32Copysign x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048556 oldWord ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩,
        func7, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hglobal, Hword⟩
  simp only [func7]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_call «module» 8 func8Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func8Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func8_lowered_body_smallStep_wp
    (iprop(R ∗ runtimeModuleOwn ⟨0⟩ «module»)) x y oldWord _
  · iintro ⟨⟨HR, Hruntime⟩, Hglobal, Hword⟩
    wasm_twp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    iapply_frame hreturn
  · iframe

theorem twp_func9_context_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
      WP (.running
        ⟨⟨[.f32 x], [], [.f32 (2147483647 &&& x)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func9, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime⟩
  simp only [func9]
  wasm_twp_pures [twp_localGet]
  iapply twp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply twp_func5_body_smallStep_wp x _
  wasm_twp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_twp_pures [twp_const twp_and]
  iapply twp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm x 2147483647]
  iapply twp_func6_body_smallStep_wp (2147483647 &&& x) _
  wasm_twp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  iapply_frame hreturn

theorem twp_func4_context_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x y : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [], [.f32 (func4Result x y)]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [], []⟩,
        func4, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime⟩
  simp only [func4]
  wasm_twp_pures [twp_localGet]
  iapply twp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply twp_func5_body_smallStep_wp y _
  wasm_twp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_twp_pures [twp_const twp_and twp_localGet]
  iapply twp_call «module» 5 func5Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams]
  iapply twp_func5_body_smallStep_wp x _
  wasm_twp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  wasm_twp_pures [twp_const twp_and twp_or]
  iapply twp_call «module» 6 func6Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func6Def, Function.toLocals, Function.numParams]
  rw [UInt32.and_comm y 2147483648, UInt32.and_comm x 2147483647]
  iapply twp_func6_body_smallStep_wp
    ((2147483648 &&& y) ||| (2147483647 &&& x)) _
  wasm_twp_return_from_call Hruntime
  simp only [List.take, List.singleton_append]
  rw [← show func4Result x y =
    (2147483648 &&& y) ||| (2147483647 &&& x) by rfl]
  iapply_frame hreturn

theorem twp_checkAbs_tail_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32)
    (calls : List CallFrame)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u32 0 1048572 result ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 result], [.i32 result]⟩,
          [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsTailProg, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkAbsTailProg]
  wasm_twp_pures [twp_localGet]
  ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) result $$ [Hresult]
  · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hresult
  iapply twp_load32 result
    (by decide) (by decide) (by decide) (by decide) $$ Hresult'
  iintro Hresult'
  wasm_twp_pures [twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
  wasm_twp_rebind twp_globalSet with Hglobal
  wasm_twp_pures [twp_localGet]
  have hResultProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) result =
        pointsTo_u32 0 1048572 result :=
    congrArg (fun address => pointsTo_u32 0 address result) (by decide)
  ihave HresultExact : pointsTo_u32 0 1048572 result $$ [Hresult']
  · rw [← hResultProp]
    iexact Hresult'
  iapply_frame hreturn

theorem twp_checkAbs_zeroPath_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldResult : UInt32)
    (hcontinue :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsZeroProg, 1, [], [checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkAbsZeroProg]
  wasm_twp_pures [twp_localGet twp_const]
  ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
  · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hresult
  iapply twp_store32 oldResult
    (by decide) (by decide) (by decide) (by decide) $$ Hresult'
  iintro Hresult'
  wasm_twp_pures [twp_exitControl]
  simp only [checkAbsOuterFrame, List.take, List.nil_append]
  have hResultProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) 0 =
        pointsTo_u32 0 1048572 0 :=
    congrArg (fun address => pointsTo_u32 0 address 0) (by decide)
  ihave HresultExact : pointsTo_u32 0 1048572 0 $$ [Hresult']
  · rw [← hResultProp]
    iexact Hresult'
  iapply_frame hcontinue

theorem twp_checkAbs_onePath_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x oldResult : UInt32)
    (hcontinue :
      R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        [.localGet 1, .const 1, .store32 12, .br 1],
        1, [], [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hresult⟩
  wasm_twp_pures [twp_localGet twp_const]
  ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
  · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hresult
  iapply twp_store32 oldResult
    (by decide) (by decide) (by decide) (by decide) $$ Hresult'
  iintro Hresult'
  wasm_twp_pures [twp_br]
  simp only [checkAbsOuterFrame, List.take, List.nil_append]
  have hResultProp :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) 1 =
        pointsTo_u32 0 1048572 1 :=
    congrArg (fun address => pointsTo_u32 0 address 1) (by decide)
  ihave HresultExact : pointsTo_u32 0 1048572 1 $$ [Hresult']
  · rw [← hResultProp]
    iexact Hresult'
  iapply_frame hcontinue

theorem twp_checkAbs_secondComparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x upper oldResult : UInt32)
    (hzero :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hone :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 upper ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        [ .localGet 0, .call 0, .localGet 0, .call 2,
          .f32Eq, .const 1, .and, .eqz, .br_if 0,
          .localGet 1, .const 1, .store32 12, .br 1 ],
        1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  wasm_twp_pures [twp_localGet]
  iapply twp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams]
  iapply twp_func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048572 oldResult))
    x upper _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    wasm_twp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_twp_pures [twp_localGet]
    iapply twp_call «module» 2 func2Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    iintro Hruntime
    icombine Hlow Hupper as Hscratch
    ihave Hpacked := innerScratch_merge_upper (f32Abs x) $$ Hscratch
    simp [func2Def, Function.toLocals, Function.numParams]
    iapply twp_func2_lowered_smallStep_wp
      (iprop(pointsTo_u32 0 1048572 oldResult))
      x (packUpper32 (f32Abs x)) _
    · iintro ⟨Hresult, Hruntime, Hglobal, Hscratch⟩
      wasm_twp_return_from_call Hruntime
      simp only [List.take, List.singleton_append]
      by_cases heq :
          f32Eq (f32Abs x) (func2Result x) = true
      · iapply twp_scalarFloat2 (value := .i32 1) rfl rfl
          (by simp [evalScalarFloat2?, heq])
        wasm_twp_pures [twp_const twp_and]
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        iapply twp_eqz (result := 0) (by decide)
        wasm_twp_pures [twp_brIfZero]
        iapply twp_checkAbs_onePath_smallStep_wp
          (iprop(pointsTo_u64 0 1048552
            (f64Abs (f64PromoteF32 x)) ∗ runtimeModuleOwn ⟨0⟩ «module»))
          x oldResult _
        · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
          iapply_frame hone
        · iframe
      · have heqFalse :
            f32Eq (f32Abs x) (func2Result x) = false := by
          cases h : f32Eq (f32Abs x) (func2Result x) <;> simp_all
        iapply twp_scalarFloat2 (value := .i32 0) rfl rfl
          (by simp [evalScalarFloat2?, heqFalse])
        wasm_twp_pures [twp_const twp_and]
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        iapply twp_eqz (result := 1) (by decide)
        iapply twp_brIf (by decide) rfl
        simp only [checkAbsInnerFrame, List.take, List.nil_append]
        iapply twp_checkAbs_zeroPath_smallStep_wp
          (iprop(pointsTo_u64 0 1048552
            (f64Abs (f64PromoteF32 x)) ∗ runtimeModuleOwn ⟨0⟩ «module»))
          x oldResult _
        · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
          iapply_frame hzero
        · iframe
    · iframe
  · iframe

theorem twp_checkAbs_firstComparisonTail_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x oldResult : UInt32)
    (hzeroFirst :
      pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hzeroSecond :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hone :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 (f32Abs x) ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0],
          [.f32 (2147483647 &&& x), .f32 (f32Abs x)]⟩,
        [ .f32Eq, .const 1, .and, .eqz, .br_if 0,
          .localGet 0, .call 0, .localGet 0, .call 2,
          .f32Eq, .const 1, .and, .eqz, .br_if 0,
          .localGet 1, .const 1, .store32 12, .br 1 ],
        1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  by_cases heq : f32Eq (f32Abs x) (2147483647 &&& x) = true
  · iapply twp_scalarFloat2 (value := .i32 1) rfl rfl
      (by simp [evalScalarFloat2?, heq])
    wasm_twp_pures [twp_const twp_and]
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    iapply twp_eqz (result := 0) (by decide)
    wasm_twp_pures [twp_brIfZero]
    iapply twp_checkAbs_secondComparison_smallStep_wp
      (s := s) (E := E) (Φ := Φ)
      x (f32Abs x) oldResult _ _
    · exact hzeroSecond
    · exact hone
    · iframe
  · have heqFalse :
        f32Eq (f32Abs x) (2147483647 &&& x) = false := by
      cases h : f32Eq (f32Abs x) (2147483647 &&& x) <;> simp_all
    iapply twp_scalarFloat2 (value := .i32 0) rfl rfl
      (by simp [evalScalarFloat2?, heqFalse])
    wasm_twp_pures [twp_const twp_and]
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (by decide) rfl
    simp only [checkAbsInnerFrame, List.take, List.nil_append]
    icombine Hlow Hupper as Hscratch
    ihave Hpacked := innerScratch_merge_upper (f32Abs x) $$ Hscratch
    iapply twp_checkAbs_zeroPath_smallStep_wp
      (iprop(pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x oldResult _
    · iintro ⟨⟨Hscratch, Hruntime⟩, Hglobal, Hresult⟩
      iapply_frame hzeroFirst
    · iframe

theorem twp_checkAbs_firstComparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x upper oldResult : UInt32)
    (hzeroFirst :
      pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hzeroSecond :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hone :
      pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
          checkAbsTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 upper ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsInnerBody, 1, [],
        [checkAbsInnerFrame, checkAbsOuterFrame], []⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  simp only [checkAbsInnerBody]
  wasm_twp_pures [twp_localGet]
  iapply twp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams]
  iapply twp_func0_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048572 oldResult))
    x upper _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    wasm_twp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_twp_pures [twp_localGet]
    iapply twp_call «module» 9 func9Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    iintro Hruntime
    simp [func9Def, Function.toLocals, Function.numParams]
    iapply twp_func9_context_smallStep_wp
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Abs x) ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 oldResult))
      x _ _
    · iintro ⟨HR, Hruntime⟩
      wasm_twp_return_from_call Hruntime
      simp only [List.take, List.singleton_append]
      icases HR with ⟨Hlow, Hupper, Hglobal, Hresult⟩
      iapply twp_checkAbs_firstComparisonTail_smallStep_wp
        (s := s) (E := E) (Φ := Φ)
        x oldResult _ _ _
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hone
      · iframe
    · iframe
  · iframe

theorem twp_checkAbs_tail_result_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (R : IProp (WasmHeapGF Unit)) (x result : UInt32) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 1048560, .i32 0], []⟩,
        checkAbsTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      [{ values,
        ∀ (store : MachineStore Unit) (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜∃ b : UInt32, values = [.i32 b]⌝ }] := by
  iapply twp_checkAbs_tail_smallStep_wp R x result [] _
  iintro ⟨HR, Hglobal, Hresult⟩
  wasm_twp_terminal_value twp_returnFromFunction
  iintro %store %obs _Hstate
  iclear HR Hglobal Hresult
  ipureexact ⟨result, rfl⟩

theorem twp_func10_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u64 0 1048552 0 ∗ pointsTo_u32 0 1048572 0 ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x], [.i32 0, .i32 0], []⟩,
        func10, 1, [], [], []⟩ : Expr Unit) @ s; E
      [{ values,
        ∀ (store : MachineStore Unit) (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜∃ b : UInt32, values = [.i32 b]⌝ }] := by
  iintro ⟨Hscratch, Hresult, Hruntime, Hglobal⟩
  simp only [func10]
  wasm_twp_rebind twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub]
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  wasm_twp_pures [twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hglobal
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
  wasm_twp_pures [twp_block]
  rw (occs := .pos [1]) [show checkAbsOuterBody =
    (.block 0 0 checkAbsInnerBody :: checkAbsZeroProg) by rfl]
  wasm_twp_pures [twp_block]
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
  iapply twp_checkAbs_firstComparison_smallStep_wp
    (s := s) (E := E)
    x 0 0 _ _ _
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply twp_checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 0 1048552 (packUpper32 (f32Abs x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x 0
    iframe
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply twp_checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x 0
    iframe
  · iintro ⟨Hscratch, Hruntime, Hglobal, Hresult⟩
    iapply twp_checkAbs_tail_result_smallStep_wp (s := s) (E := E)
      (iprop(pointsTo_u64 0 1048552 (f64Abs (f64PromoteF32 x)) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x 1
    iframe
  · iframe

theorem twp_checkCopysign_tail_result_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (R : IProp (WasmHeapGF Unit)) (x y result : UInt32) :
    R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 result ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
        checkCopysignTailProg, 1, [], [], []⟩ :
        Expr Unit) @ s; E
      [{ values,
        ∀ (store : MachineStore Unit) (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜∃ b : UInt32, values = [.i32 b]⌝ }] := by
  iintro ⟨HR, Hglobal, Hresult⟩
  simp only [checkCopysignTailProg]
  wasm_twp_pures [twp_localGet]
  ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) result $$ [Hresult]
  · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
    iexact Hresult
  iapply twp_load32 result
    (by decide) (by decide) (by decide) (by decide) $$ Hresult'
  iintro Hresult'
  wasm_twp_pures [twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
  wasm_twp_rebind twp_globalSet with Hglobal
  wasm_twp_pures [twp_localGet]
  wasm_twp_terminal_value twp_returnFromFunction
  iintro %store %obs _Hstate
  iclear HR Hglobal Hresult'
  ipureexact ⟨result, rfl⟩

theorem twp_checkCopysign_comparison_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x y upper oldResult : UInt32)
    (hzero :
      pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
          checkCopysignTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }])
    (hone :
      pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗ pointsTo_u32 0 1048572 1 ⊢
      WP (.running
        ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
          checkCopysignTailProg, 1, [], [], []⟩ :
          Expr Unit) @ s; E [{ Φ }]) :
    pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048556 upper ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u32 0 1048572 oldResult ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 1048560, .i32 0], []⟩,
        checkCopysignInnerBody, 1, [],
        [checkCopysignInnerFrame, checkCopysignOuterFrame], []⟩ :
        Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
  simp only [checkCopysignInnerBody]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_call «module» 7 func7Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func7Def, Function.toLocals, Function.numParams]
  iapply twp_func7_lowered_smallStep_wp
    (iprop(pointsTo_u32 0 1048552 0 ∗ pointsTo_u32 0 1048572 oldResult))
    x y upper _ _
  · iintro ⟨⟨Hlow, Hresult⟩, Hruntime, Hglobal, Hupper⟩
    wasm_twp_return_from_call Hruntime
    simp only [List.take, List.singleton_append]
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply twp_call «module» 4 func4Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    iintro Hruntime
    simp [func4Def, Function.toLocals, Function.numParams]
    iapply twp_func4_context_smallStep_wp
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u32 0 1048572 oldResult))
      x y _ _
    · iintro ⟨HR, Hruntime⟩
      wasm_twp_return_from_call Hruntime
      simp only [List.take, List.singleton_append]
      icases HR with ⟨Hlow, Hupper, Hglobal, Hresult⟩
      by_cases heq :
          f32Eq (f32Copysign x y) (func4Result x y) = true
      · iapply twp_scalarFloat2 (value := .i32 1) rfl rfl
          (by simp [evalScalarFloat2?, heq])
        wasm_twp_pures [twp_const twp_and]
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        iapply twp_brIf (by decide) rfl
        simp only [checkCopysignInnerFrame, List.take, List.nil_append]
        simp only [checkCopysignOneProg]
        wasm_twp_pures [twp_localGet twp_const]
        ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
          iexact Hresult
        iapply twp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ Hresult'
        iintro Hresult'
        wasm_twp_pures [twp_exitControl]
        simp only [checkCopysignOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 1 =
              pointsTo_u32 0 1048572 1 :=
          congrArg (fun address => pointsTo_u32 0 address 1) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 1 $$ [Hresult']
        · rw [← hResultProp]
          iexact Hresult'
        iapply_frame hone
      · have heqFalse :
            f32Eq (f32Copysign x y) (func4Result x y) = false := by
          cases h : f32Eq (f32Copysign x y) (func4Result x y) <;> simp_all
        iapply twp_scalarFloat2 (value := .i32 0) rfl rfl
          (by simp [evalScalarFloat2?, heqFalse])
        wasm_twp_pures [twp_const twp_and]
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        wasm_twp_pures [twp_brIfZero twp_localGet twp_const]
        ihave Hresult' : pointsTo_u32 0 ((1048560 : UInt32) + 12) oldResult $$ [Hresult]
        · rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
          iexact Hresult
        iapply twp_store32 oldResult
          (by decide) (by decide) (by decide) (by decide) $$ Hresult'
        iintro Hresult'
        wasm_twp_pures [twp_br]
        simp only [checkCopysignOuterFrame, List.take, List.nil_append]
        have hResultProp :
            pointsTo_u32 0 ((1048560 : UInt32) + 12) 0 =
              pointsTo_u32 0 1048572 0 :=
          congrArg (fun address => pointsTo_u32 0 address 0) (by decide)
        ihave HresultExact : pointsTo_u32 0 1048572 0 $$ [Hresult']
        · rw [← hResultProp]
          iexact Hresult'
        iapply_frame hzero
    · iframe
  · iframe

theorem twp_func11_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset} :
    pointsTo_u64 0 1048552 0 ∗ pointsTo_u32 0 1048572 0 ∗
      runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048576) ⊢
    WP (.running
      ⟨⟨[.f32 x, .f32 y], [.i32 0, .i32 0], []⟩,
        func11, 1, [], [], []⟩ : Expr Unit) @ s; E
      [{ values,
        ∀ (store : MachineStore Unit) (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜∃ b : UInt32, values = [.i32 b]⌝ }] := by
  iintro ⟨Hscratch, Hresult, Hruntime, Hglobal⟩
  simp only [func11]
  wasm_twp_rebind twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub]
  rw [show (1048576 : UInt32) - 16 = 1048560 by decide]
  wasm_twp_pures [twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hglobal
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
  wasm_twp_pures [twp_block]
  rw (occs := .pos [1]) [show checkCopysignOuterBody =
    (.block 0 0 checkCopysignInnerBody :: checkCopysignOneProg) by rfl]
  wasm_twp_pures [twp_block]
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
  iapply twp_checkCopysign_comparison_smallStep_wp
    (s := s) (E := E)
    x y 0 0 _ _
  · iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
    iapply twp_checkCopysign_tail_result_smallStep_wp
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x y 0
    iframe
  · iintro ⟨Hlow, Hupper, Hruntime, Hglobal, Hresult⟩
    iapply twp_checkCopysign_tail_result_smallStep_wp
      (iprop(pointsTo_u32 0 1048552 0 ∗
        pointsTo_u32 0 1048556 (f32Copysign x y) ∗
        runtimeModuleOwn ⟨0⟩ «module»))
      x y 1
    iframe
  · iframe

theorem check_abs_terminatesWith (x : UInt32) :
    Wasm.SmallStep.TerminatesWith (checkAbsConfig x)
      (fun rs _store => ∃ b : UInt32, rs = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_store_terminates
    (α := Unit)
    (σ := exportHeap) (globalσ := func1Globals)
    (post := fun rs _store => ∃ b : UInt32, rs = [.i32 b])
  · simpa [checkAbsConfig, func1Config] using exportHeap_agrees
  · simpa [checkAbsConfig, func1Config] using exportHeap_inBounds
  · simpa [checkAbsConfig, func1Config] using func1Globals_agree
  · simp only [checkAbsConfig]; decide
  · intro _hlc _gs
    simp only [checkAbsConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := exportHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hscratch, Hresult⟩
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    iapply_frame twp_func10_body_smallStep_wp

theorem check_copysign_terminatesWith (x y : UInt32) :
    Wasm.SmallStep.TerminatesWith (checkCopysignConfig x y)
      (fun rs _store => ∃ b : UInt32, rs = [.i32 b]) := by
  apply wasm_smallStep_heap_globals_runtime_store_terminates
    (α := Unit)
    (σ := exportHeap) (globalσ := func1Globals)
    (post := fun rs _store => ∃ b : UInt32, rs = [.i32 b])
  · simpa [checkCopysignConfig, func1Config] using exportHeap_agrees
  · simpa [checkCopysignConfig, func1Config] using exportHeap_inBounds
  · simpa [checkCopysignConfig, func1Config] using func1Globals_agree
  · simp only [checkCopysignConfig]; decide
  · intro _hlc _gs
    simp only [checkCopysignConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hmemory := exportHeap_pointsTo $$ Hbytes
    icases Hmemory with ⟨Hscratch, Hresult⟩
    ihave Hglobal := func1Globals_pointsTo $$ Hglobals
    iapply_frame twp_func11_body_smallStep_wp

@[spec_of "rust-exported" "float_reinterpret::float_reinterpret"]
def FloatReinterpretSpec : Prop :=
  (∀ (x : UInt32),
    SmallStep.TerminatesWith (checkAbsConfig x)
      (fun rs _store => ∃ b : UInt32, rs = [.i32 b])) ∧
  (∀ (x y : UInt32),
    SmallStep.TerminatesWith (checkCopysignConfig x y)
      (fun rs _store => ∃ b : UInt32, rs = [.i32 b]))

@[proves Project.FloatReinterpret.Spec.FloatReinterpretSpec]
theorem check_reinterpret_correct : FloatReinterpretSpec :=
  ⟨check_abs_terminatesWith, check_copysign_terminatesWith⟩

end Project.FloatReinterpret.Spec
