import Project.SwapElements.Program
import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepAdequacy

/-! # Swap Elements — iris-lean small-step proof

The full generated call chain is proved directly with iris-lean `WP` over
`Wasm.SmallStep.Step`: func4 → func3 and func4 → func0 → func1 → func2.
Authoritative heap, global, and runtime ownership connects those rules to
closed operational `PartiallyMeets` theorems. Separate contracts cover
distinct and equal element addresses, so the alias case never duplicates an
exclusive byte owner. Concrete export executions also carry finite-trace
`SmallStep.TerminatesWith` witnesses from the executable step iterator.

Key memory facts after the swap:
  final_mem = (st.mem
    .write32(1048568, ptr)         -- func3: ptr spill
    .write32(1048572, len)         -- func3: len spill
    .write64(1048552, vA)          -- func2: temp = *ptr_a
    .write64(ptr + 8*i, vB)       -- func2: *ptr_a = *ptr_b
    .write64(ptr + 8*j, vA))      -- func2: *ptr_b = temp
  where vA = st.mem.read64(ptr + 8*i), vB = st.mem.read64(ptr + 8*j).

The spec's global0 and pages-bound preconditions are load-bearing here:
without `global 0 = 1048576` on entry, func4's scratch frame (`global 0 −
16`) could alias the array and the swap postcondition would be false. -/

namespace Project.SwapElements.SwapSepLogic

open Iris Iris.ProgramLogic Language.Notation Std
open Wasm Wasm.SepLogic

set_option maxRecDepth 1048576

private def func1OuterBody : Program :=
  match func1 with
  | .block _ _ body _ _ :: _ => body
  | _ => []

private def func1OuterContinuation : Program :=
  match func1 with
  | .block _ _ _ _ _ :: continuation => continuation
  | _ => []

private def func1MiddleBody : Program :=
  match func1OuterBody with
  | .block _ _ body _ _ :: _ => body
  | _ => []

private def func1MiddleContinuation : Program :=
  match func1OuterBody with
  | .block _ _ _ _ _ :: continuation => continuation
  | _ => []

private def func1InnerBody : Program :=
  match func1MiddleBody with
  | .block _ _ body _ _ :: _ => body
  | _ => []

private def func1OuterFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := func1OuterBody
    continuation := func1OuterContinuation
    belowStack := [] }

set_option maxHeartbeats 4000000 in
/-- The exact successful bounds-check prefix of generated `func1`. After
twenty-eight instruction-level transitions, `i < len` and `j < len` select the
outward branch to the real `call 2` continuation and leave `&arr[i]` in local
slot five and `&arr[j]` on the operand stack. -/
theorem func1_happyPrefix_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (ptr len i j : UInt32) (hi : i < len) (hj : j < len)
    (calls : List Wasm.SmallStep.CallFrame) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    ▷^[28] WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 addressI], [.i32 addressJ, .i32 addressI]⟩,
        [.call 2, .ret], 0, [], [func1OuterFrame], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ : Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro Htarget
  simp only [func1]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_ltU (result := 1) (by simp [hi])
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  rw [show (1 &&& 1 : UInt32) = 1 by decide]
  iapply Wasm.SmallStep.wp_eqz (value := 1) (result := 0) rfl
  inext
  iapply Wasm.SmallStep.wp_brIfZero
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_shl
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_ltU (result := 1) (by simp [hj])
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
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_shl
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  simp only [func1OuterFrame, func1OuterBody, func1OuterContinuation, func1]
  iexact Htarget

/-- The generated `call 2` transition reached by
`func1_happyPrefix_smallStep_wp`. Runtime ownership proves that function index
two is the concrete generated `func2Def`, and the installed call frame retains
the outer bounds-check frame and `func1`'s final return continuation. -/
theorem func1_call2_entry_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (ptr len i j : UInt32) (calls : List Wasm.SmallStep.CallFrame) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    let caller : Wasm.SmallStep.CallFrame :=
      { locals :=
          ⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 addressI], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [func1OuterFrame] }
    ▷ runtimeModuleOwn «module» -∗
    ▷ (runtimeModuleOwn «module» -∗
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 addressI, .i32 addressJ], [.i32 0], []⟩,
          func2, 0, [], [], caller :: calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) -∗
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 addressI], [.i32 addressJ, .i32 addressI]⟩,
        [.call 2, .ret], 0, [], [func1OuterFrame], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  simpa [func2Def, Function.toLocals, Function.numParams, ValueType.zero] using
    (Wasm.SmallStep.wp_call (α := Unit) (s := s) (E := E)
      (Φ := Φ)
      (params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604])
      (localValues := [.i32 ((i <<< (3 % 32)) + ptr)])
      (values :=
        [.i32 ((j <<< (3 % 32)) + ptr),
          .i32 ((i <<< (3 % 32)) + ptr)])
      (code := [.ret]) (arity := 0) (remainder := [])
      (controls := [func1OuterFrame]) (calls := calls)
      «module» 2 func2Def (by decide) rfl)

/-- The generated exchange leaf executed beneath `func1`'s concrete call
frame. Its final `ret` resumes `func1`, whose own final `ret` then completes
the top-level invocation. -/
theorem func2_in_func1_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    let caller : Wasm.SmallStep.CallFrame :=
      { locals :=
          ⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 addressI], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [func1OuterFrame] }
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 addressI oldA ∗ pointsTo_u64 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 addressI, .i32 addressJ], [.i32 0], []⟩,
        func2, 0, [], [], caller :: calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨HR, Hresources⟩
  simp only [func2]
  iapply Wasm.SmallStep.wp_swapElementsFunc2Prefix
    ((i <<< (3 % 32)) + ptr) ((j <<< (3 % 32)) + ptr)
    oldScratch oldA oldB hroomI hroomJ
  isplitl [Hresources]
  · iexact Hresources
  · inext
    iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.nil_append]
    iapply hreturn
    iframe

/-- Equal-index counterpart of `func2_in_func1_context_smallStep_wp`. The
callee receives the same pointer twice, so one array-word owner is threaded
sequentially through both loads and stores. -/
theorem func2Alias_in_func1_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldValue ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    let address := (i <<< (3 % 32)) + ptr
    R ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗ pointsTo_u64 address oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 address, .i32 address], [.i32 0], []⟩,
        func2, 0, [], [], {
          locals :=
            ⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
              [.i32 address], []⟩
          continuation := [.ret]
          resultArity := 0
          callerRemainder := []
          control := [func1OuterFrame] } :: calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨HR, Hresources⟩
  simp only [func2]
  iapply Wasm.SmallStep.wp_swapElementsFunc2AliasPrefix
    ((i <<< (3 % 32)) + ptr) oldScratch oldValue hroom
  isplitl [Hresources]
  · iexact Hresources
  · inext
    iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.nil_append]
    iapply hreturn
    iframe

/-- Successful equal-index path of the generated bounds-checking wrapper. -/
theorem func1_alias_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldValue ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hresources⟩
  iapply func1_happyPrefix_smallStep_wp ptr len i i hi hi calls
  inext
  iapply func1_call2_entry_smallStep_wp ptr len i i calls $$ Hruntime
  inext
  iintro Hruntime
  iapply func2Alias_in_func1_context_smallStep_wp
    (iprop% R ∗ runtimeModuleOwn «module»)
    ptr len i oldScratch oldValue hroom calls
  · iintro ⟨⟨HR, Hruntime⟩, Hresources⟩
    iapply hreturn
    iframe
  · iframe

/-- Call-stack-polymorphic happy path of generated `func1`. The theorem stops
at `func1`'s own final return, allowing callers to choose whether that return
completes the execution or resumes another generated frame. -/
theorem func1_happy_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 addressI oldA ∗ pointsTo_u64 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ : Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨HR, Hruntime, Hresources⟩
  iapply func1_happyPrefix_smallStep_wp ptr len i j hi hj calls
  inext
  iapply func1_call2_entry_smallStep_wp ptr len i j calls $$ Hruntime
  inext
  iintro Hruntime
  iapply func2_in_func1_context_smallStep_wp
    (iprop% R ∗ runtimeModuleOwn «module»)
    ptr len i j oldScratch oldA oldB hroomI hroomJ calls
  · iintro ⟨⟨HR, Hruntime⟩, Hresources⟩
    iapply hreturn
    iframe
  · iframe

/-- End-to-end happy path of generated `func1`: both bounds checks succeed,
the physical-runtime-checked direct call enters `func2`, the three words are
exchanged, and both administrative returns are discharged. -/
theorem func1_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 addressI oldA ∗ pointsTo_u64 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u64 addressI oldB ∗ pointsTo_u64 addressJ oldA }} := by
  dsimp only
  iintro Hresources
  iapply func1_happy_context_smallStep_wp (iprop(True))
    ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ []
  iintro ⟨_Htrue, Hruntime, Hresources⟩
  iclear Hruntime
  iapply Wasm.SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · iexact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

/-- The generated `func0` forwarding wrapper, composed through its real direct
call frame. This remains contextual so the exported wrapper can suspend above
it without duplicating any semantics. -/
theorem func0_happy_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
        func0, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hresources⟩
  simp only [func0]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp only [func1Def, Function.toLocals, Function.numParams,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.take, List.drop,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.map, ValueType.zero]
  iapply func1_happy_context_smallStep_wp R
    ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ _
  · iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.nil_append]
    iapply hreturn
    iexact Hresources
  · iframe

/-- Equal-index path of the generated forwarding wrapper. -/
theorem func0_alias_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldValue ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
        func0, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hresources⟩
  simp only [func0]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp only [func1Def, Function.toLocals, Function.numParams,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.take, List.drop,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.map, ValueType.zero]
  iapply func1_alias_context_smallStep_wp R
    ptr len i oldScratch oldValue hi hroom _
  · iintro Hresources
    iapply Wasm.SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.nil_append]
    iapply hreturn
    iexact Hresources
  · iframe

/-- Top-level equal-index forwarding-wrapper contract. -/
theorem func0_alias_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
        func0, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldValue ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue }} := by
  iintro Hresources
  iapply func0_alias_context_smallStep_wp (iprop(True))
    ptr len i oldScratch oldValue hi hroom []
  · iintro ⟨_Htrue, Hruntime, Hresources⟩
    iclear Hruntime
    iapply Wasm.SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    isplitr
    · ipureintro
      rfl
    · iexact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

/-- Closed-WP form of the generated forwarding wrapper. -/
theorem func0_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
        func0, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldA }} := by
  iintro Hresources
  iapply func0_happy_context_smallStep_wp (iprop(True))
    ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ []
  iintro ⟨_Htrue, Hruntime, Hresources⟩
  iclear Hruntime
  iapply Wasm.SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · iexact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

/-- Small-step Iris proof for the generated `func2` exchange leaf. Global 0
selects its scratch frame, while authoritative eight-byte ownership connects
all three physical words to the operational `load64`/`store64` steps. -/
theorem func2_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296) :
    globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ptrA oldA ∗ pointsTo_u64 ptrB oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        func2, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048560) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u64 ptrA oldB ∗ pointsTo_u64 ptrB oldA }} := by
  simpa only [func2] using
    (Wasm.SmallStep.wp_swapElementsFunc2
      (α := Unit) (s := s) (E := E)
      ptrA ptrB oldScratch oldA oldB hroomA hroomB)

/-- Small-step Iris proof for the generated `func3` leaf. This is the first
downstream swap proof that uses iris-lean's `WP` over `Wasm.SmallStep.Step`;
the legacy theorem below remains temporarily because it additionally proves
total termination and a large physical framing postcondition. -/
theorem func3_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (oldPtr oldLen ptr len : UInt32)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u32 1048568 oldPtr ∗ pointsTo_u32 1048572 oldLen ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hptr, Hlen⟩
  simp only [func3]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HlenLater :
      ▷ pointsTo_u32 ((1048568 : UInt32) + 4) oldLen $$ [Hlen]
  · inext
    rw [show (1048568 : UInt32) + 4 = 1048572 from rfl]
    iexact Hlen
  iapply Wasm.SmallStep.wp_store32 oldLen rfl rfl rfl rfl $$ HlenLater
  inext
  iintro Hlen
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HptrLater :
      ▷ pointsTo_u32 ((1048568 : UInt32) + 0) oldPtr $$ [Hptr]
  · inext
    rw [UInt32.add_zero]
    iexact Hptr
  iapply Wasm.SmallStep.wp_store32 oldPtr rfl rfl rfl rfl $$ HptrLater
  inext
  iintro Hptr
  iapply hreturn
  rw [UInt32.add_zero,
    ← show (1048568 : UInt32) + 4 = 1048572 from rfl]
  iframe

theorem func3_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (oldPtr oldLen ptr len : UInt32) :
    pointsTo_u32 1048568 oldPtr ∗ pointsTo_u32 1048572 oldLen ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len }} := by
  simpa only [func3] using
    (Wasm.SmallStep.wp_swapElementsFunc3
      (α := Unit) (s := s) (E := E) oldPtr oldLen ptr len)

/-- Successful exported path through the generated stack frame, spill helper,
forwarding wrapper, bounds checks, and exchange leaf. The postcondition keeps
the complete touched footprint so the subsequent adequacy theorem can connect
every ghost cell back to physical Wasm memory. -/
theorem func4_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (ptr len i j oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u32 1048568 oldSpillPtr ∗
      pointsTo_u32 1048572 oldSpillLen ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048576) ∗
        pointsTo_u64 1048552 oldA ∗
        pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldA }} := by
  iintro ⟨Hruntime, Hglobal, Hscratch, HspillPtr, HspillLen, HA, HB⟩
  simp only [func4]
  iapply Wasm.SmallStep.wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_sub
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HglobalLater : ▷ globalPointsTo 0 (.i32 1048576) $$ [Hglobal]
  · inext
    iexact Hglobal
  iapply Wasm.SmallStep.wp_globalSet $$ HglobalLater
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_const
  inext
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
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams]
  iapply func3_context_smallStep_wp
    (iprop% runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB)
    oldSpillPtr oldSpillLen ptr len _
  · iintro ⟨Hrest, HspillPtr, HspillLen⟩
    icases Hrest with ⟨Hruntime, Hglobal, Hscratch, HA, HB⟩
    iapply Wasm.SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.nil_append]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HlenLater :
        ▷ pointsTo_u32 ((1048560 : UInt32) + 12) len $$ [HspillLen]
    · inext
      rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
      iexact HspillLen
    iapply Wasm.SmallStep.wp_load32 len
      (by decide) (by decide) (by decide) (by decide) $$ HlenLater
    inext
    iintro HspillLen
    iapply Wasm.SmallStep.wp_localSet rfl
    inext
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HptrLater :
        ▷ pointsTo_u32 ((1048560 : UInt32) + 8) ptr $$ [HspillPtr]
    · inext
      rw [show (1048560 : UInt32) + 8 = 1048568 by decide]
      iexact HspillPtr
    iapply Wasm.SmallStep.wp_load32 ptr
      (by decide) (by decide) (by decide) (by decide) $$ HptrLater
    inext
    iintro HspillPtr
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams]
    iapply func0_happy_context_smallStep_wp
      (iprop% pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len)
      ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ _
    · iintro ⟨⟨HspillPtr, HspillLen⟩,
        Hruntime, Hglobal, Hscratch, HA, HB⟩
      iapply Wasm.SmallStep.wp_returnFromCallExplicit
      inext
      simp only [List.take, List.nil_append]
      iapply Wasm.SmallStep.wp_localGet rfl
      inext
      iapply Wasm.SmallStep.wp_const
      inext
      iapply Wasm.SmallStep.wp_add
      inext
      ihave HglobalLater :
          ▷ globalPointsTo 0 (.i32 1048560) $$ [Hglobal]
      · inext
        iexact Hglobal
      iapply Wasm.SmallStep.wp_globalSet $$ HglobalLater
      inext
      iintro Hglobal
      rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
      rw [show (3 % 32 : UInt32) = 3 by decide]
      iapply Wasm.SmallStep.wp_returnFromFunction
      inext
      iapply wp_value'
      isplitr
      · ipureintro
        rfl
      · iframe
    · rw [show (3 % 32 : UInt32) = 3 by decide]
      iframe
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iframe

/-- Equal-index exported path. The generated stack-frame mechanics are
identical to `func4_happy_smallStep_wp`, but the nested exchange uses the
one-cell alias contract. -/
theorem func4_alias_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (ptr len i oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 1048576) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u32 1048568 oldSpillPtr ∗
      pointsTo_u32 1048572 oldSpillLen ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsTo 0 (.i32 1048576) ∗
        pointsTo_u64 1048552 oldValue ∗
        pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len ∗
        pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue }} := by
  iintro ⟨Hruntime, Hglobal, Hscratch, HspillPtr, HspillLen, Hcell⟩
  simp only [func4]
  iapply Wasm.SmallStep.wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_sub
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HglobalLater : ▷ globalPointsTo 0 (.i32 1048576) $$ [Hglobal]
  · inext
    iexact Hglobal
  iapply Wasm.SmallStep.wp_globalSet $$ HglobalLater
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_const
  inext
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
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams]
  iapply func3_context_smallStep_wp
    (iprop% runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 1048560) ∗
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue)
    oldSpillPtr oldSpillLen ptr len _
  · iintro ⟨Hrest, HspillPtr, HspillLen⟩
    icases Hrest with ⟨Hruntime, Hglobal, Hscratch, Hcell⟩
    iapply Wasm.SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.nil_append]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HlenLater :
        ▷ pointsTo_u32 ((1048560 : UInt32) + 12) len $$ [HspillLen]
    · inext
      rw [show (1048560 : UInt32) + 12 = 1048572 by decide]
      iexact HspillLen
    iapply Wasm.SmallStep.wp_load32 len
      (by decide) (by decide) (by decide) (by decide) $$ HlenLater
    inext
    iintro HspillLen
    iapply Wasm.SmallStep.wp_localSet rfl
    inext
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HptrLater :
        ▷ pointsTo_u32 ((1048560 : UInt32) + 8) ptr $$ [HspillPtr]
    · inext
      rw [show (1048560 : UInt32) + 8 = 1048568 by decide]
      iexact HspillPtr
    iapply Wasm.SmallStep.wp_load32 ptr
      (by decide) (by decide) (by decide) (by decide) $$ HptrLater
    inext
    iintro HspillPtr
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams]
    iapply func0_alias_context_smallStep_wp
      (iprop% pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len)
      ptr len i oldScratch oldValue hi hroom _
    · iintro ⟨⟨HspillPtr, HspillLen⟩,
        Hruntime, Hglobal, Hscratch, Hcell⟩
      iapply Wasm.SmallStep.wp_returnFromCallExplicit
      inext
      simp only [List.take, List.nil_append]
      iapply Wasm.SmallStep.wp_localGet rfl
      inext
      iapply Wasm.SmallStep.wp_const
      inext
      iapply Wasm.SmallStep.wp_add
      inext
      ihave HglobalLater :
          ▷ globalPointsTo 0 (.i32 1048560) $$ [Hglobal]
      · inext
        iexact Hglobal
      iapply Wasm.SmallStep.wp_globalSet $$ HglobalLater
      inext
      iintro Hglobal
      rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
      rw [show (3 % 32 : UInt32) = 3 by decide]
      iapply Wasm.SmallStep.wp_returnFromFunction
      inext
      iapply wp_value'
      isplitr
      · ipureintro
        rfl
      · iframe
    · rw [show (3 % 32 : UInt32) = 3 by decide]
      iframe
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iframe

/-! ## Parameterized authoritative export contract -/

def func4ConfigFromStore (wasm : Store Unit)
    (ptr len i j : UInt32) : Wasm.SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := wasm } }

/-- Fully parameterized distinct-address partial correctness. The footprint
decomposition is the separation-logic form of disjointness: it is impossible
to supply two exclusive `u64` owners for overlapping bytes. -/
theorem func4_distinct_store_partiallyMeets
    (wasm : Store Unit) (ptr len i j : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ wasm.mem)
    (hinBounds : heapAddressesInBounds σ wasm.mem)
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u32 1048568 oldSpillPtr ∗
      pointsTo_u32 1048572 oldSpillLen ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB)
    (hglobalOwn : ∀ [WasmGlobalGS],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576)) :
    Wasm.SmallStep.PartiallyMeets
      (func4ConfigFromStore wasm ptr len i j)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldB ∧
          store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr) = oldA) := by
  let addressI := (i <<< (3 % 32)) + ptr
  let addressJ := (j <<< (3 % 32)) + ptr
  have hroomI' : addressI.toNat + 8 ≤ 4294967296 := by
    simpa [addressI] using hroomI
  have hroomJ' : addressJ.toNat + 8 ≤ 4294967296 := by
    simpa [addressJ] using hroomJ
  have hi1 : (addressI + 1).toNat = addressI.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 1
      (by omega) (by omega)
  have hi2 : (addressI + 2).toNat = addressI.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 2 (by omega) (by omega)
  have hi3 : (addressI + 3).toNat = addressI.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 3 (by omega) (by omega)
  have hi4 : (addressI + 4).toNat = addressI.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 4 (by omega) (by omega)
  have hi5 : (addressI + 5).toNat = addressI.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 5 (by omega) (by omega)
  have hi6 : (addressI + 6).toNat = addressI.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 6 (by omega) (by omega)
  have hi7 : (addressI + 7).toNat = addressI.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 7 (by omega) (by omega)
  have hj1 : (addressJ + 1).toNat = addressJ.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 1 (by omega) (by omega)
  have hj2 : (addressJ + 2).toNat = addressJ.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 2 (by omega) (by omega)
  have hj3 : (addressJ + 3).toNat = addressJ.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 3 (by omega) (by omega)
  have hj4 : (addressJ + 4).toNat = addressJ.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 4 (by omega) (by omega)
  have hj5 : (addressJ + 5).toNat = addressJ.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 5 (by omega) (by omega)
  have hj6 : (addressJ + 6).toNat = addressJ.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 6 (by omega) (by omega)
  have hj7 : (addressJ + 7).toNat = addressJ.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 7 (by omega) (by omega)
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets.{0}
      (α := Unit) (σ := σ) (globalσ := globalσ)
  · exact hagree
  · exact hinBounds
  · exact hglobals
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hresources := hresources $$ Hheap
    ihave Hglobal := hglobalOwn $$ Hglobals
    icases Hresources with
      ⟨Hscratch, HspillPtr, HspillLen, HA, HB⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsTo 0 (.i32 1048576) ∗
          pointsTo_u64 1048552 oldA ∗
          pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len ∗
          pointsTo_u64 addressI oldB ∗ pointsTo_u64 addressJ oldA) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 addressI = oldB ∧
            store.wasm.mem.read64 addressJ = oldA⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, HA, HB⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts_frame
        store 0 [] 0 addressI oldB hi1 hi2 hi3 hi4 hi5 hi6 hi7 $$
          [$Hstate $HA] with ⟨Hstate, _HA, %HfactsI⟩
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 addressJ oldA hj1 hj2 hj3 hj4 hj5 hj6 hj7 $$
          [$Hstate $HB] with %HfactsJ
      ipureintro
      exact ⟨hvalues, HfactsI.1, HfactsJ.1⟩
    iapply wp_mono hpost
    simp only [func4ConfigFromStore]
    iapply func4_happy_smallStep_wp
      ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
      hi hj hroomI hroomJ
    iframe

/-- Fully parameterized equal-index partial correctness.  This version needs
only one exclusive array-word owner and proves that the reached physical word
is unchanged. -/
theorem func4_alias_store_partiallyMeets
    (wasm : Store Unit) (ptr len i : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldValue : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ wasm.mem)
    (hinBounds : heapAddressesInBounds σ wasm.mem)
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u32 1048568 oldSpillPtr ∗
      pointsTo_u32 1048572 oldSpillLen ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldValue)
    (hglobalOwn : ∀ [WasmGlobalGS],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576)) :
    Wasm.SmallStep.PartiallyMeets
      (func4ConfigFromStore wasm ptr len i i)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldValue) := by
  let address := (i <<< (3 % 32)) + ptr
  have hroom' : address.toNat + 8 ≤ 4294967296 := by
    simpa [address] using hroom
  have h1 : (address + 1).toNat = address.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap address 1 (by omega) (by omega)
  have h2 : (address + 2).toNat = address.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap address 2 (by omega) (by omega)
  have h3 : (address + 3).toNat = address.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap address 3 (by omega) (by omega)
  have h4 : (address + 4).toNat = address.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap address 4 (by omega) (by omega)
  have h5 : (address + 5).toNat = address.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap address 5 (by omega) (by omega)
  have h6 : (address + 6).toNat = address.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap address 6 (by omega) (by omega)
  have h7 : (address + 7).toNat = address.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap address 7 (by omega) (by omega)
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets.{0}
      (α := Unit) (σ := σ) (globalσ := globalσ)
  · exact hagree
  · exact hinBounds
  · exact hglobals
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hresources := hresources $$ Hheap
    ihave Hglobal := hglobalOwn $$ Hglobals
    icases Hresources with
      ⟨Hscratch, HspillPtr, HspillLen, Hcell⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsTo 0 (.i32 1048576) ∗
          pointsTo_u64 1048552 oldValue ∗
          pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len ∗
          pointsTo_u64 address oldValue) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.mem.read64 address = oldValue⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, Hcell⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 address oldValue h1 h2 h3 h4 h5 h6 h7 $$
          [$Hstate $Hcell] with %Hfacts
      ipureintro
      exact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    simp only [func4ConfigFromStore]
    iapply func4_alias_smallStep_wp
      ptr len i oldSpillPtr oldSpillLen oldScratch oldValue hi hroom
    iframe

/-! ## Closed authoritative small-step execution of the spill helper -/

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

def func3Config (ptr len : UInt32) : Wasm.SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

def func3Heap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 1048568 0) 1048572 0

private def func3Mem (memory : Mem) : Mem :=
  (memory.write32 1048568 0).write32 1048572 0

private theorem func3_initialMem_eq :
    func3Mem («module».initialStore : Store Unit).mem =
      («module».initialStore : Store Unit).mem := by
  unfold func3Mem
  rw [Mem.write32_eq_self (by decide) (by decide) (by decide) (by decide)]
  rw [Mem.write32_eq_self (by decide) (by decide) (by decide) (by decide)]

theorem func3Heap_agrees (ptr len : UInt32) :
    heapAgreesWithMem func3Heap (func3Config ptr len).store.wasm.mem := by
  change heapAgreesWithMem func3Heap
    («module».initialStore : Store Unit).mem
  rw [← func3_initialMem_eq]
  unfold func3Heap func3Mem
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  exact emptyHeap_agrees _

theorem func3Heap_inBounds (ptr len : UInt32) :
    heapAddressesInBounds func3Heap
      (func3Config ptr len).store.wasm.mem := by
  change heapAddressesInBounds func3Heap
    («module».initialStore : Store Unit).mem
  rw [← func3_initialMem_eq]
  unfold func3Heap func3Mem
  apply store32_inBounds <;> try rfl
  · apply store32_inBounds <;> try rfl
    · exact emptyHeap_inBounds _
    · decide
  · decide

theorem func3Heap_pointsTo [WasmHeapGS] :
    ([∗map] address ↦ value ∈ func3Heap,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 1048568 0 ∗ pointsTo_u32 1048572 0 := by
  unfold func3Heap
  iintro Hheap
  ihave Houter := store32Heap_pointsTo
    (store32Heap ∅ 1048568 0) 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Houter with ⟨Hlen, Hheap⟩
  ihave Hinner := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 1048568 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hinner with ⟨Hptr, Hempty⟩
  iframe

/-- The spill helper's existing instruction proof, closed through iris-lean
adequacy and the authoritative physical byte interpretation. -/
theorem func3_smallStep (ptr len : UInt32) :
    Wasm.SmallStep.PartiallyMeets (func3Config ptr len)
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.adequate_to_partiallyMeets
  apply Wasm.SmallStep.wasm_smallStep_heap_adequacy.{0}
    (α := Unit) (σ := func3Heap)
    (φ := fun values => values = [])
  · exact func3Heap_agrees ptr len
  · exact func3Heap_inBounds ptr len
  · intro gs
    iintro Hheap
    ihave Hwords := func3Heap_pointsTo $$ Hheap
    icases Hwords with ⟨Hptr, Hlen⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo_u32 1048568 ptr ∗ pointsTo_u32 1048572 len) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hptr, _Hlen⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    simp only [func3Config]
    iapply func3_smallStep_wp (s := Stuckness.NotStuck) (E := ⊤)
      0 0 ptr len
    iframe

/-! ## Closed exported two-element example -/

def func4ExampleHeap : WasmHeapMap (Option UInt8) :=
  store64Heap
    (store64Heap
      (store32Heap
        (store32Heap (store64Heap ∅ 1048552 0) 1048568 0)
        1048572 0)
      0 11)
    8 22

private def func4ExampleMem (memory : Mem) : Mem :=
  ((((memory.write64 1048552 0).write32 1048568 0).write32 1048572 0
    ).write64 0 11).write64 8 22

def func4ExampleConfig : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i32 0, .i32 2, .i32 0, .i32 1],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := { initial with mem := func4ExampleMem initial.mem } } }

def func4ExampleGlobals : WasmGlobalMap Value :=
  insert ∅ 0 (.i32 1048576)

theorem func4ExampleHeap_agrees :
    heapAgreesWithMem func4ExampleHeap
      func4ExampleConfig.store.wasm.mem := by
  unfold func4ExampleHeap func4ExampleConfig func4ExampleMem
  apply store64_sound <;> try rfl
  apply store64_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store64_sound <;> try rfl
  exact emptyHeap_agrees _

theorem func4ExampleHeap_inBounds :
    heapAddressesInBounds func4ExampleHeap
      func4ExampleConfig.store.wasm.mem := by
  unfold func4ExampleHeap func4ExampleConfig func4ExampleMem
  apply store64_inBounds <;> try rfl
  · apply store64_inBounds <;> try rfl
    · apply store32_inBounds <;> try rfl
      · apply store32_inBounds <;> try rfl
        · apply store64_inBounds <;> try rfl
          · exact emptyHeap_inBounds _
          · decide
        · decide
      · decide
    · decide
  · decide

theorem func4ExampleGlobals_agree :
    globalHeapAgrees func4ExampleGlobals
      func4ExampleConfig.store.wasm.globals := by
  intro index value hget
  simp only [func4ExampleGlobals] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (Ne.symm hindex), get?_empty] at hget
    contradiction

theorem func4ExampleHeap_pointsTo [WasmHeapGS] :
    ([∗map] address ↦ value ∈ func4ExampleHeap,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 0 ∗
      pointsTo_u32 1048568 0 ∗ pointsTo_u32 1048572 0 ∗
      pointsTo_u64 0 11 ∗ pointsTo_u64 8 22 := by
  unfold func4ExampleHeap
  iintro Hheap
  ihave H8 := store64Heap_pointsTo _ 8 22
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases H8 with ⟨H8, Hheap⟩
  ihave H0 := store64Heap_pointsTo _ 0 11
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, Hheap⟩
  ihave Hlen := store32Heap_pointsTo _ 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hlen with ⟨Hlen, Hheap⟩
  ihave Hptr := store32Heap_pointsTo _ 1048568 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hptr with ⟨Hptr, Hheap⟩
  ihave Hscratch := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases Hscratch with ⟨Hscratch, Hempty⟩
  iframe

theorem func4ExampleGlobals_pointsTo [WasmGlobalGS] :
    ([∗map] index ↦ value ∈ func4ExampleGlobals,
      globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576) := by
  unfold func4ExampleGlobals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty 0)).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

/-- The real exported swap executes under the authoritative small-step
semantics on a concrete two-element array and returns normally. -/
theorem func4Example_smallStep :
    Wasm.SmallStep.PartiallyMeets func4ExampleConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
    (α := Unit) (σ := func4ExampleHeap)
    (globalσ := func4ExampleGlobals)
    (φ := fun values => values = [])
  · exact func4ExampleHeap_agrees
  · exact func4ExampleHeap_inBounds
  · exact func4ExampleGlobals_agree
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hwords := func4ExampleHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    icases Hwords with ⟨Hscratch, HspillPtr, HspillLen, H0, H8⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsTo 0 (.i32 1048576) ∗
          pointsTo_u64 1048552 11 ∗
          pointsTo_u32 1048568 0 ∗ pointsTo_u32 1048572 2 ∗
          pointsTo_u64 0 22 ∗ pointsTo_u64 8 11) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hresources⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    simp only [func4ExampleConfig]
    have hfunc4 := func4_happy_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 2 0 1 0 0 0 11 22
      (by decide) (by decide) (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide,
      show ((1 : UInt32) <<< (3 % 32)) + 0 = 8 by decide] at hfunc4
    iapply hfunc4
    iframe

/-- State-sensitive adequacy for the distinct-index export example proves
both sides of the physical swap in the reached `MachineStore`. -/
theorem func4Example_store_smallStep :
    Wasm.SmallStep.PartiallyMeets func4ExampleConfig
      (fun values store =>
        values = [] ∧ store.wasm.mem.read64 0 = 22 ∧
          store.wasm.mem.read64 8 = 11) := by
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets.{0}
      (α := Unit) (σ := func4ExampleHeap)
      (globalσ := func4ExampleGlobals)
  · exact func4ExampleHeap_agrees
  · exact func4ExampleHeap_inBounds
  · exact func4ExampleGlobals_agree
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hwords := func4ExampleHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    icases Hwords with ⟨Hscratch, HspillPtr, HspillLen, H0, H8⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsTo 0 (.i32 1048576) ∗
          pointsTo_u64 1048552 11 ∗
          pointsTo_u32 1048568 0 ∗ pointsTo_u32 1048572 2 ∗
          pointsTo_u64 0 22 ∗ pointsTo_u64 8 11) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 0 = 22 ∧
            store.wasm.mem.read64 8 = 11⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, H0, H8⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts_frame
        store 0 [] 0 0 22
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 8 11
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts8.1⟩
    iapply wp_mono hpost
    simp only [func4ExampleConfig]
    have hfunc4 := func4_happy_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 2 0 1 0 0 0 11 22
      (by decide) (by decide) (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide,
      show ((1 : UInt32) <<< (3 % 32)) + 0 = 8 by decide] at hfunc4
    iapply hfunc4
    iframe

/-- Executable finite-trace witness complementing the Iris partial-correctness
proof for the distinct-index export example. -/
theorem func4Example_terminates :
    Wasm.SmallStep.TerminatesWith func4ExampleConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.runSteps_values_terminates (fuel := 200)
  native_decide

def func4AliasHeap : WasmHeapMap (Option UInt8) :=
  store64Heap
    (store32Heap
      (store32Heap (store64Heap ∅ 1048552 0) 1048568 0)
      1048572 0)
    0 42

private def func4AliasMem (memory : Mem) : Mem :=
  (((memory.write64 1048552 0).write32 1048568 0).write32 1048572 0
    ).write64 0 42

def func4AliasConfig : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i32 0, .i32 1, .i32 0, .i32 0],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := { initial with mem := func4AliasMem initial.mem } } }

theorem func4AliasHeap_agrees :
    heapAgreesWithMem func4AliasHeap
      func4AliasConfig.store.wasm.mem := by
  unfold func4AliasHeap func4AliasConfig func4AliasMem
  apply store64_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store32_sound <;> try rfl
  apply store64_sound <;> try rfl
  exact emptyHeap_agrees _

theorem func4AliasHeap_inBounds :
    heapAddressesInBounds func4AliasHeap
      func4AliasConfig.store.wasm.mem := by
  unfold func4AliasHeap func4AliasConfig func4AliasMem
  apply store64_inBounds <;> try rfl
  · apply store32_inBounds <;> try rfl
    · apply store32_inBounds <;> try rfl
      · apply store64_inBounds <;> try rfl
        · exact emptyHeap_inBounds _
        · decide
      · decide
    · decide
  · decide

theorem func4AliasHeap_pointsTo [WasmHeapGS] :
    ([∗map] address ↦ value ∈ func4AliasHeap,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 0 ∗
      pointsTo_u32 1048568 0 ∗ pointsTo_u32 1048572 0 ∗
      pointsTo_u64 0 42 := by
  unfold func4AliasHeap
  iintro Hheap
  ihave Hcell := store64Heap_pointsTo _ 0 42
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases Hcell with ⟨Hcell, Hheap⟩
  ihave Hlen := store32Heap_pointsTo _ 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hlen with ⟨Hlen, Hheap⟩
  ihave Hptr := store32Heap_pointsTo _ 1048568 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hptr with ⟨Hptr, Hheap⟩
  ihave Hscratch := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases Hscratch with ⟨Hscratch, Hempty⟩
  iframe

/-- The exported wrapper also closes in the equal-index case from one array
word of authoritative ownership. -/
theorem func4Alias_smallStep :
    Wasm.SmallStep.PartiallyMeets func4AliasConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
    (α := Unit) (σ := func4AliasHeap)
    (globalσ := func4ExampleGlobals)
    (φ := fun values => values = [])
  · exact func4AliasHeap_agrees
  · exact func4AliasHeap_inBounds
  · exact func4ExampleGlobals_agree
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hwords := func4AliasHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    icases Hwords with ⟨Hscratch, HspillPtr, HspillLen, Hcell⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsTo 0 (.i32 1048576) ∗
          pointsTo_u64 1048552 42 ∗
          pointsTo_u32 1048568 0 ∗ pointsTo_u32 1048572 1 ∗
          pointsTo_u64 0 42) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hresources⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    simp only [func4AliasConfig]
    have halias := func4_alias_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 1 0 0 0 0 42 (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide] at halias
    iapply halias
    iframe

/-- State-sensitive adequacy for the exported equal-index case: the physical
array word in the reached `MachineStore` is unchanged. -/
theorem func4Alias_store_smallStep :
    Wasm.SmallStep.PartiallyMeets func4AliasConfig
      (fun values store =>
        values = [] ∧ store.wasm.mem.read64 0 = 42) := by
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets.{0}
      (α := Unit) (σ := func4AliasHeap)
      (globalσ := func4ExampleGlobals)
  · exact func4AliasHeap_agrees
  · exact func4AliasHeap_inBounds
  · exact func4ExampleGlobals_agree
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hwords := func4AliasHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    icases Hwords with ⟨Hscratch, HspillPtr, HspillLen, Hcell⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsTo 0 (.i32 1048576) ∗
          pointsTo_u64 1048552 42 ∗
          pointsTo_u32 1048568 0 ∗ pointsTo_u32 1048572 1 ∗
          pointsTo_u64 0 42) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 0 = 42⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, Hcell⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 0 42
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hcell] with %Hfacts
      ipureintro
      exact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    simp only [func4AliasConfig]
    have halias := func4_alias_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 1 0 0 0 0 42 (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide] at halias
    iapply halias
    iframe

/-- Executable finite-trace witness for the equal-index export example. -/
theorem func4Alias_terminates :
    Wasm.SmallStep.TerminatesWith func4AliasConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.runSteps_values_terminates (fuel := 200)
  native_decide

/-! ## Closed equal-index example -/

def func0AliasHeap : WasmHeapMap (Option UInt8) :=
  store64Heap (store64Heap ∅ 1048552 0) 0 42

def func0AliasConfig : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i32 0, .i32 1, .i32 0, .i32 0], [], []⟩,
        func0, 0, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm :=
          { initial with
            mem := (initial.mem.write64 1048552 0).write64 0 42
            globals := { globals := [Value.i32 1048560] } } } }

def func0AliasGlobals : WasmGlobalMap Value :=
  insert ∅ 0 (.i32 1048560)

theorem func0AliasHeap_agrees :
    heapAgreesWithMem func0AliasHeap
      func0AliasConfig.store.wasm.mem := by
  unfold func0AliasHeap func0AliasConfig
  apply store64_sound <;> try rfl
  apply store64_sound <;> try rfl
  exact emptyHeap_agrees _

theorem func0AliasHeap_inBounds :
    heapAddressesInBounds func0AliasHeap
      func0AliasConfig.store.wasm.mem := by
  unfold func0AliasHeap func0AliasConfig
  apply store64_inBounds <;> try rfl
  · apply store64_inBounds <;> try rfl
    · exact emptyHeap_inBounds _
    · decide
  · decide

theorem func0AliasGlobals_agree :
    globalHeapAgrees func0AliasGlobals
      func0AliasConfig.store.wasm.globals := by
  intro index value hget
  simp only [func0AliasGlobals] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (Ne.symm hindex), get?_empty] at hget
    contradiction

theorem func0AliasHeap_pointsTo [WasmHeapGS] :
    ([∗map] address ↦ value ∈ func0AliasHeap,
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 0 ∗ pointsTo_u64 0 42 := by
  unfold func0AliasHeap
  iintro Hheap
  ihave Hcell := store64Heap_pointsTo _ 0 42
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases Hcell with ⟨Hcell, Hheap⟩
  ihave Hscratch := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases Hscratch with ⟨Hscratch, Hempty⟩
  iframe

theorem func0AliasGlobals_pointsTo [WasmGlobalGS] :
    ([∗map] index ↦ value ∈ func0AliasGlobals,
      globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048560) := by
  unfold func0AliasGlobals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty 0)).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

/-- Same-index swapping is a real one-cell execution, not a degenerate proof
that duplicates exclusive ownership. -/
theorem func0Alias_smallStep :
    Wasm.SmallStep.PartiallyMeets func0AliasConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets.{0}
    (α := Unit) (σ := func0AliasHeap)
    (globalσ := func0AliasGlobals)
    (φ := fun values => values = [])
  · exact func0AliasHeap_agrees
  · exact func0AliasHeap_inBounds
  · exact func0AliasGlobals_agree
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hwords := func0AliasHeap_pointsTo $$ Hheap
    ihave Hglobal := func0AliasGlobals_pointsTo $$ Hglobals
    icases Hwords with ⟨Hscratch, Hcell⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsTo 0 (.i32 1048560) ∗
          pointsTo_u64 1048552 42 ∗ pointsTo_u64 0 42) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hresources⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    simp only [func0AliasConfig]
    have halias := func0_alias_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 1 0 0 42 (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide] at halias
    iapply halias
    iframe

/- The former custom `wp_wasm`/big-step proof block lived below this point.
It is retained temporarily as commented migration history while the public
`TerminatesWith` statement in `Spec.lean` is moved to the finite-trace
small-step API. It is no longer elaborated and no legacy SepLogic module is
imported by this file.

-- func3 spills ptr/len into the 8-byte slot at [1048568, 1048575]
-- body: write32(1048572, len) then write32(1048568, ptr)
set_option maxHeartbeats 4000000 in
private theorem func3_terminates (env : HostEnv Unit) (st : Store Unit)
    (ptr len : UInt32)
    (hpg : (1048576 : Nat) ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 3 st
      [.i32 (1048652 : UInt32), .i32 len, .i32 ptr, .i32 (1048568 : UInt32)]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read32 (1048568 : UInt32) = ptr
        ∧ st'.mem.read32 (1048572 : UInt32) = len
        ∧ ∀ a : UInt32, (1048576 : Nat) ≤ a.toNat →
            st'.mem.read64 a = st.mem.read64 a) := by
  have himp : «module».imports[3]? = none := rfl
  have hf : «module».funcs[3 - «module».imports.length]? = some func3Def := rfl
  have hwp : wp_wasm_prop «module» st
      (func3Def.toLocals ([.i32 (1048652 : UInt32), .i32 len, .i32 ptr,
                           .i32 (1048568 : UInt32)].take func3Def.numParams).reverse)
      func3Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read32 (1048568 : UInt32) = ptr
        ∧ st'.mem.read32 (1048572 : UInt32) = len
        ∧ ∀ a : UInt32, (1048576 : Nat) ≤ a.toNat →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wasm_heap_adequacy
    intro inst
    let m₁ := st.mem.write32 ((1048568 : UInt32) + (4 : UInt32)) len
    let m₂ := m₁.write32 ((1048568 : UInt32) + (0 : UInt32)) ptr
    have hm₁ : m₁ = st.mem.write32 ((1048568 : UInt32) + (4 : UInt32)) len := rfl
    have hm₂ : m₂ = m₁.write32 ((1048568 : UInt32) + (0 : UInt32)) ptr := rfl
    have hpages : m₂.pages = st.mem.pages := by
      simp only [hm₂, hm₁, Mem.write32_pages]
    have hread_1568 : m₂.read32 (1048568 : UInt32) = ptr := by
      simp only [hm₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      exact Mem.read32_write32_same m₁ (1048568 : UInt32) ptr
    have hread_1572 : m₂.read32 (1048572 : UInt32) = len := by
      simp only [hm₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      rw [Mem.read32_write32_disjoint m₁ (1048568 : UInt32) (1048572 : UInt32) ptr
            (Or.inr (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl,
                                   show (1048572 : UInt32).toNat = 1048572 from rfl]; omega))]
      simp only [hm₁, show (1048568 : UInt32) + (4 : UInt32) = (1048572 : UInt32) from rfl]
      exact Mem.read32_write32_same st.mem (1048572 : UInt32) len
    have hread_ne : ∀ a : UInt32, (1048576 : Nat) ≤ a.toNat →
        m₂.read64 a = st.mem.read64 a := by
      intro a ha
      simp only [hm₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      rw [Mem.read64_write32_disjoint m₁ a (1048568 : UInt32) ptr
            (Or.inl (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl]; omega))]
      simp only [hm₁, show (1048568 : UInt32) + (4 : UInt32) = (1048572 : UInt32) from rfl]
      rw [Mem.read64_write32_disjoint st.mem a (1048572 : UInt32) len
            (Or.inl (by simp only [show (1048572 : UInt32).toNat = 1048572 from rfl]; omega))]
    show ⊢ wp_wasm «module» st
      { params := [.i32 (1048568 : UInt32), .i32 ptr, .i32 len, .i32 (1048652 : UInt32)],
        locals := [], values := [] }
      [.localGet 0, .localGet 2, .store32 (4 : UInt32),
       .localGet 0, .localGet 1, .store32 (0 : UInt32), .ret] env _
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_store32 rfl
        (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl,
                       show (4 : UInt32).toNat = 4 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_store32 rfl
        (by simp only [Mem.write32_pages,
                       show (1048568 : UInt32).toNat = 1048568 from rfl,
                       show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    exact wp_wasm_ret ⟨rfl, rfl, hpages, hread_1568, hread_1572, hread_ne⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

-- func2: the actual swap via scratch at 1048552 (global0 = 1048560 at call time)
set_option maxHeartbeats 4000000 in
private theorem func2_terminates (env : HostEnv Unit) (st : Store Unit)
    (ptr_a ptr_b : UInt32)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32)))
    (hpg_scratch : (1048560 : Nat) ≤ st.mem.pages * 65536)
    (hpg_a : ptr_a.toNat + 8 ≤ st.mem.pages * 65536)
    (hpg_b : ptr_b.toNat + 8 ≤ st.mem.pages * 65536)
    -- ptr_a and ptr_b are both above the scratch region [1048544,1048559]
    (hge_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hge_b : (1048560 : Nat) ≤ ptr_b.toNat)
    -- either equal or 8-byte disjoint (guaranteed by 8-byte array stride)
    (hdisj : ptr_a = ptr_b ∨
             ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat) :
    TerminatesWith env «module» 2 st [.i32 ptr_b, .i32 ptr_a]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 ptr_a = st.mem.read64 ptr_b
        ∧ st'.mem.read64 ptr_b = st.mem.read64 ptr_a
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  have himp : «module».imports[2]? = none := rfl
  have hf : «module».funcs[2 - «module».imports.length]? = some func2Def := rfl
  have hwp : wp_wasm_prop «module» st
      (func2Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func2Def.numParams).reverse)
      func2Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 ptr_a = st.mem.read64 ptr_b
        ∧ st'.mem.read64 ptr_b = st.mem.read64 ptr_a
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wasm_heap_adequacy
    intro inst
    -- pre-prove memory postcondition on the exact write64 chain used by the wp steps
    -- addresses: 1048560-16+8, ptr_a+0, ptr_b+0 (offset immediates not yet reduced)
    have h1552_nat : (1048552 : UInt32).toNat = 1048552 := rfl
    have hne_a : (1048552 : UInt32).toNat + 8 ≤ ptr_a.toNat := by omega
    have hne_b : (1048552 : UInt32).toNat + 8 ≤ ptr_b.toNat := by omega
    have ha0 : ptr_a + (0 : UInt32) = ptr_a := by simp
    have hb0 : ptr_b + (0 : UInt32) = ptr_b := by simp
    have h1552eq : ((1048560 : UInt32) - 16 + 8) = (1048552 : UInt32) := rfl
    let m₁ := st.mem.write64 ((1048560 : UInt32) - 16 + 8) (st.mem.read64 (ptr_a + 0))
    let m₂ := m₁.write64 (ptr_a + 0) (m₁.read64 (ptr_b + 0))
    let m₃ := m₂.write64 (ptr_b + 0) (m₂.read64 ((1048560 : UInt32) - 16 + 8))
    have hm₁ : m₁ = st.mem.write64 ((1048560 : UInt32) - 16 + 8) (st.mem.read64 (ptr_a + 0)) := rfl
    have hm₂ : m₂ = m₁.write64 (ptr_a + 0) (m₁.read64 (ptr_b + 0)) := rfl
    have hm₃ : m₃ = m₂.write64 (ptr_b + 0) (m₂.read64 ((1048560 : UInt32) - 16 + 8)) := rfl
    have hpages : m₃.pages = st.mem.pages := by
      simp only [hm₃, hm₂, hm₁, Mem.write64_pages]
    have hread_a : m₃.read64 ptr_a = st.mem.read64 ptr_b := by
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rcases hdisj with rfl | h | h
      · rw [Mem.read64_write64_same,
            Mem.read64_write64_disjoint _ ptr_a _ _ (Or.inl hne_a),
            Mem.read64_write64_same]
      · rw [Mem.read64_write64_disjoint _ ptr_b _ _ (Or.inl h),
            Mem.read64_write64_same,
            Mem.read64_write64_disjoint _ (1048552 : UInt32) _ _ (Or.inr hne_b)]
      · rw [Mem.read64_write64_disjoint _ ptr_b _ _ (Or.inr h),
            Mem.read64_write64_same,
            Mem.read64_write64_disjoint _ (1048552 : UInt32) _ _ (Or.inr hne_b)]
    have hread_b : m₃.read64 ptr_b = st.mem.read64 ptr_a := by
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rw [Mem.read64_write64_same,
          Mem.read64_write64_disjoint _ ptr_a _ _ (Or.inl hne_a),
          Mem.read64_write64_same]
    have hread_ne : ∀ a : UInt32,
        (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
        (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
        (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
        m₃.read64 a = st.mem.read64 a := by
      intro a h1 h2 h3
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rw [Mem.read64_write64_disjoint _ ptr_b _ _ h2,
          Mem.read64_write64_disjoint _ ptr_a _ _ h1,
          Mem.read64_write64_disjoint _ (1048552 : UInt32) _ _
            (by rcases h3 with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))]
    show ⊢ wp_wasm «module» st
      { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)], values := [] }
      [.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2, .localGet 0,
       .load64 (0 : UInt32), .store64 (8 : UInt32), .localGet 0, .localGet 1,
       .load64 (0 : UInt32), .store64 (0 : UInt32), .localGet 1, .localGet 2,
       .load64 (8 : UInt32), .store64 (0 : UInt32), .ret] env _
    refine wp_wasm_globalGet hg0 (ghost_id ?_)
    refine wp_wasm_const (16 : UInt32) (ghost_id ?_)
    refine wp_wasm_sub rfl (ghost_id ?_)
    refine wp_wasm_localSet rfl rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_load64 rfl
        (by simp only [show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_store64 rfl
        (by simp only [show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                       show (8 : UInt32).toNat = 8 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_load64 rfl
        (by simp only [Mem.write64_pages, show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_store64 rfl
        (by simp only [Mem.write64_pages, show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_load64 rfl
        (by simp only [Mem.write64_pages,
                       show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                       show (8 : UInt32).toNat = 8 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_store64 rfl
        (by simp only [Mem.write64_pages, show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    exact wp_wasm_ret ⟨rfl, rfl, hpages, hread_a, hread_b, hread_ne⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

-- func1: bounds-check i < len and j < len, compute addresses, call func2.
-- The three nested bounds-check blocks exit via an outward break on the
-- happy path (`br_if 1` → `Break 1`), which is outside the block rule's
-- Fallthrough/Break-0 shape — so the block section is traced once at the
-- exec level and hopped over with `wp_wasm_prop_of_exec_eq`; the call is
-- then composed with `wp_wasm_prop_call`.
private theorem func1_terminates_sw (env : HostEnv Unit) (st : Store Unit)
    (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hpg : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hpages_bound : st.mem.pages * 65536 ≤ 4294967296)
    (hptr : (1048576 : Nat) ≤ ptr.toNat)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32))) :
    TerminatesWith env «module» 1 st
      [.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  have hi_nat : i.toNat < len.toNat := hi
  have hj_nat : j.toNat < len.toNat := hj
  have helemI : (elemAddr ptr i).toNat = ptr.toNat + 8 * i.toNat :=
    elemAddr_toNat ptr i (by omega)
  have helemJ : (elemAddr ptr j).toNat = ptr.toNat + 8 * j.toNat :=
    elemAddr_toNat ptr j (by omega)
  have hpg_a : (elemAddr ptr i).toNat + 8 ≤ st.mem.pages * 65536 := by
    rw [helemI]; omega
  have hpg_b : (elemAddr ptr j).toNat + 8 ≤ st.mem.pages * 65536 := by
    rw [helemJ]; omega
  have hge_a : (1048560 : Nat) ≤ (elemAddr ptr i).toNat := by rw [helemI]; omega
  have hge_b : (1048560 : Nat) ≤ (elemAddr ptr j).toNat := by rw [helemJ]; omega
  have hdisj : elemAddr ptr i = elemAddr ptr j ∨
               (elemAddr ptr i).toNat + 8 ≤ (elemAddr ptr j).toNat ∨
               (elemAddr ptr j).toNat + 8 ≤ (elemAddr ptr i).toNat := by
    rcases eq_or_ne i j with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr (elemAddr_disjoint ptr i j (by omega) (by omega) hne)
  have himp₁ : «module».imports[1]? = none := rfl
  have hf₁ : «module».funcs[1 - «module».imports.length]? = some func1Def := rfl
  -- the address arithmetic the codegen emits, in the form the exec trace
  -- produces (`3 % 32` already reduced to `3` by the simp normal form)
  have haddr : ∀ k : UInt32, k <<< (3 : UInt32) + ptr = elemAddr ptr k := fun k => by
    simpa using elemAddr_of_shl ptr k
  have hwp : wp_wasm_prop «module» st
      (func1Def.toLocals ([.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len,
                           .i32 ptr].take func1Def.numParams).reverse)
      func1Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wp_wasm_prop_of_exec_eq (K := 4) (c := 3) (st' := st)
        (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 (1048604 : UInt32)],
                      locals := [.i32 (elemAddr ptr i)],
                      values := [.i32 (elemAddr ptr j), .i32 (elemAddr ptr i)] })
        (prog' := [.call 2, .ret])
    · intro fuel
      show exec (fuel + 4) «module» st
        { params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 (1048604 : UInt32)],
          locals := [.i32 (0 : UInt32)], values := [] }
        func1 env = _
      simp only [func1]
      simp [exec, execOne.eq_def, Locals.get, Locals.set?, hi, hj, haddr]
      -- both sides are now matches over the same `run` of func2; the block
      -- wrapper on the left only differs syntactically, so split on the result
      rcases run (fuel + 2) «module» 2 st
          [.i32 (elemAddr ptr j), .i32 (elemAddr ptr i)] env <;> rfl
    · apply wp_wasm_prop_call
      refine (func2_terminates env st (elemAddr ptr i) (elemAddr ptr j)
          hg0 (by omega) hpg_a hpg_b hge_a hge_b hdisj).mono ?_
      rintro st' vs ⟨rfl, hglob2, hpages2, hrA2, hrB2, hother2⟩
      refine ⟨1, ?_⟩
      simp only [exec, execOne]
      exact ⟨trivial, hglob2, hpages2, hrA2, hrB2, hother2⟩
  exact wp_wasm_prop_to_TerminatesWith hf₁ himp₁ rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

-- func0: simple wrapper that forwards to func1; a one-hop prefix
-- (five pushes) then `wp_wasm_prop_call`.
private theorem func0_terminates_sw (env : HostEnv Unit) (st : Store Unit)
    (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hpg : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hpages_bound : st.mem.pages * 65536 ≤ 4294967296)
    (hptr : (1048576 : Nat) ≤ ptr.toNat)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32))) :
    TerminatesWith env «module» 0 st
      [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  have himp : «module».imports[0]? = none := rfl
  have hf : «module».funcs[0 - «module».imports.length]? = some func0Def := rfl
  have hwp : wp_wasm_prop «module» st
      (func0Def.toLocals ([.i32 j, .i32 i, .i32 len, .i32 ptr].take
        func0Def.numParams).reverse)
      func0Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := st)
        (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
                      locals := [],
                      values := [.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len,
                                 .i32 ptr] })
        (prog' := [.call 1, .ret])
    · intro fuel
      show exec (fuel + 1) «module» st
        { params := [.i32 ptr, .i32 len, .i32 i, .i32 j], locals := [], values := [] }
        func0 env = _
      simp only [func0]
      simp [exec, execOne.eq_def, Locals.get]
    · apply wp_wasm_prop_call
      refine (func1_terminates_sw env st ptr len i j hi hj hpg hpages_bound
          hptr hg0).mono ?_
      rintro st' vs ⟨rfl, hglob1, hpages1, hrA1, hrB1, hother1⟩
      refine ⟨1, ?_⟩
      simp only [exec, execOne]
      exact ⟨trivial, hglob1, hpages1, hrA1, hrB1, hother1⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

/-! ## Top-level spec -/

set_option maxRecDepth 1048576 in
@[proves Project.SwapElements.Spec.SwapElementsSpec]
theorem swap_spec_sep : SwapElementsSpec := by
  intro env st ptr len i j hi hj hbound hptr hpages hg0
  have hpages_bound : st.mem.pages * 65536 ≤ 4294967296 := by omega
  have himp₄ : «module».imports[4]? = none := rfl
  have hf₄ : «module».funcs[4 - «module».imports.length]? = some func4Def := rfl
  -- Shadow-stack descend: global0 goes from 1048576 → 1048560
  let stg : Store Unit :=
    { st with globals := { st.globals with globals := st.globals.globals.set 0 (.i32 1048560) } }
  have hpg3 : (1048576 : Nat) ≤ stg.mem.pages * 65536 := by simp only [stg]; omega
  -- Helper for helemI/helemJ/helemK proofs
  have helem_toNat : ∀ k : UInt32, k < len →
      (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat := by
    intro k hk
    have hk_nat : k.toNat < len.toNat := hk
    exact elemAddr_toNat ptr k (by omega)
  have helemI := helem_toNat i hi
  have helemJ := helem_toNat j hj
  have hwp : wp_wasm_prop «module» st
      (func4Def.toLocals ([.i32 j, .i32 i, .i32 len, .i32 ptr].take
        func4Def.numParams).reverse)
      func4Def.body env
      (fun st' rs =>
        rs = []
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ k : UInt32, k < len → k ≠ i → k ≠ j →
            st'.mem.read64 (elemAddr ptr k) = st.mem.read64 (elemAddr ptr k)) := by
    -- hop 1: frame setup (globalGet/sub/globalSet, spill args) up to `call 3`
    apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := stg)
        (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
                      locals := [.i32 (1048560 : UInt32), .i32 (1048652 : UInt32),
                                 .i32 (0 : UInt32)],
                      values := [.i32 (1048652 : UInt32), .i32 len, .i32 ptr,
                                 .i32 (1048568 : UInt32)] })
        (prog' := [.call 3, .localGet 4, .load32 (12 : UInt32), .localSet 6,
                   .localGet 4, .load32 (8 : UInt32), .localGet 6, .localGet 2,
                   .localGet 3, .call 0, .localGet 4, .const (16 : UInt32), .add,
                   .globalSet 0, .ret])
    · intro fuel
      show exec (fuel + 1) «module» st
        { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
          locals := [.i32 (0 : UInt32), .i32 (0 : UInt32), .i32 (0 : UInt32)],
          values := [] }
        func4 env = _
      simp only [func4]
      simp [exec, execOne.eq_def, Locals.get, Locals.set?, hg0, stg]
    · apply wp_wasm_prop_call
      refine (func3_terminates env stg ptr len hpg3).mono ?_
      rintro st3 vs ⟨rfl, hglob3, hpages3, hread3_1568, hread3_1572, hread3_ne⟩
      -- Derive global0 = 1048560 in st3 (func3 preserved globals; globals is a List)
      have hg0_3 : st3.globals.globals[0]? = some (.i32 (1048560 : UInt32)) := by
        rw [hglob3]
        simp only [stg]
        match hnn : st.globals.globals with
        | [] => simp [hnn] at hg0
        | _ :: _ => simp [List.set]
      have hst3_pages : st3.mem.pages = st.mem.pages := by rw [hpages3]
      have hpg_st3 : ¬ (st3.mem.pages * 65536 < (1048576 : Nat)) := by
        rw [hst3_pages]; omega
      have hpg_st3_lo : ¬ (st3.mem.pages * 65536 < (1048572 : Nat)) := by
        rw [hst3_pages]; omega
      -- hop 2: read the fat pointer back up to `call 0`
      apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := st3)
          (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
                        locals := [.i32 (1048560 : UInt32), .i32 (1048652 : UInt32),
                                   .i32 len],
                        values := [.i32 j, .i32 i, .i32 len, .i32 ptr] })
          (prog' := [.call 0, .localGet 4, .const (16 : UInt32), .add,
                     .globalSet 0, .ret])
      · intro fuel
        simp [exec, execOne.eq_def, Locals.get, Locals.set?,
              hread3_1568, hread3_1572, hpg_st3, hpg_st3_lo]
      · apply wp_wasm_prop_call
        refine (func0_terminates_sw env st3 ptr len i j hi hj
            (by rw [hst3_pages]; exact hbound)
            (by rw [hst3_pages]; exact hpages_bound)
            hptr hg0_3).mono ?_
        rintro st0 vs ⟨rfl, hglob0, hpages0, hrA0, hrB0, hother0⟩
        have hg0_st0 : st0.globals.globals[0]? = some (.i32 (1048560 : UInt32)) :=
          hglob0 ▸ hg0_3
        -- frame teardown: restore global0 = 1048576, then return.
        -- Assemble the spec postcondition from func0's swap facts and
        -- func3's frame-write framing.
        refine ⟨1, ?_⟩
        simp [exec, execOne.eq_def, Locals.get, hg0_st0]
        refine ⟨?_, ?_, ?_⟩
        · -- read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j):
          -- func0 swapped relative to st3; func3's two store32s at
          -- [1048568,1048576) don't touch array addresses (≥ 1048576);
          -- stg.mem = st.mem (globals-only change)
          rw [hrA0, hread3_ne (elemAddr ptr j) (by rw [helemJ]; omega)]
        · rw [hrB0, hread3_ne (elemAddr ptr i) (by rw [helemI]; omega)]
        · intro k hk hki hkj
          have helemK := helem_toNat k hk
          trans st3.mem.read64 (elemAddr ptr k)
          · apply hother0
            · -- disjoint with elemAddr ptr i
              rcases Nat.lt_or_ge k.toNat i.toNat with h | h
              · left; rw [helemK, helemI]; omega
              · rcases Nat.eq_or_lt_of_le h with heq | hlt
                · exact absurd (UInt32.toNat.inj heq.symm) hki
                · right; rw [helemK, helemI]; omega
            · -- disjoint with elemAddr ptr j
              rcases Nat.lt_or_ge k.toNat j.toNat with h | h
              · left; rw [helemK, helemJ]; omega
              · rcases Nat.eq_or_lt_of_le h with heq | hlt
                · exact absurd (UInt32.toNat.inj heq.symm) hkj
                · right; rw [helemK, helemJ]; omega
            · -- above scratch region
              right; rw [helemK]; omega
          · rw [hread3_ne (elemAddr ptr k) (by rw [helemK]; omega)]
  exact wp_wasm_prop_to_TerminatesWith hf₄ himp₄ rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp
-/

end Project.SwapElements.SwapSepLogic
