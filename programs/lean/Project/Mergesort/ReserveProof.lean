import Project.Mergesort.FormatProof
import Project.Mergesort.VectorProof

/-!
# Generated `Vec<u64>::reserve` (`func100`) segment contracts

The collect growth loop stops exactly at the generated reserve call
`.call 102` (local `func100`, see
`InputIteratorProof.vecExtendLoop_grow_to_reserve_twp`).  `func100` itself is
a thin arithmetic wrapper: it loads the vector length and capacity, decides
whether the request still fits, and otherwise forwards
`(vecPtr, len, additional, 8, 8)` to the amortized-grow wrapper `func104`
(call immediate `106`).  That grow core in turn reaches
`func117 → func114 → dlmalloc`; it is the single remaining seam of the
reserve path.

This file proves everything of `func100` around that one seam totally:

* `reserveNoGrow_body_twp` / `reserveNoGrow_call_twp` — the complete
  fast path (`additional ≤ capacity - len`): the function is a no-op on the
  vector and cannot trap;
* `reserve_body_to_grow_twp` / `reserve_call_to_grow_twp` — the grow path
  from entry (respectively from the caller's `.call 102`) up to exactly the
  generated `.call 106` boundary, with the boundary state fully explicit;
* `reserveGrow_finish_body_twp` / `reserveGrow_finish_call_twp` — the
  remaining epilogue from the state in which `.call 106` has returned back
  to the caller of `.call 102`.

The two call-level segment rules compose linearly around a future total
contract for `.call 106` (`func104` with arguments
`[.i32 8, .i32 8, .i32 additional, .i32 len, .i32 vecPtr]` on the stack,
top first); `vecReserveGrow_call_twp` performs exactly this composition,
parameterized by that missing grow-core entailment.
-/

namespace Project.Mergesort.ReserveProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.FormatProof
open Project.Mergesort.VectorProof

/-! ## Function-index boundaries -/

/-- Local `func100` is the generated `Vec<u64>::reserve`; its call immediate
is `102`. -/
theorem vecReserve_index : «module».funcs[100]? = some func100Def := by rfl

/-- Local `func104` is the amortized grow wrapper reached from `func100`;
its call immediate is `106`. -/
theorem growAmortizedWrapper_index :
    «module».funcs[104]? = some func104Def := by rfl

/-! ## Shape of the generated reserve body -/

/-- Everything of `func100` after the shadow-stack frame prologue and the
capacity snapshot: the needs-grow guard and the forwarded grow call. -/
def reserveBlockBody : Program :=
  [ .localGet 1, .localGet 2, .load32 (12 : UInt32), .localGet 3, .sub,
    .gtU, .const (1 : UInt32), .and, .eqz, .br_if 0,
    .const (8 : UInt32), .localSet 4,
    .localGet 0, .localGet 3, .localGet 1, .localGet 4, .localGet 4,
    .call 106 ]

/-- The frame-restoring epilogue of `func100`. -/
def reserveEpilogue : Program :=
  [ .localGet 2, .const (16 : UInt32), .add, .globalSet 0, .ret ]

/-- The single remaining linear call boundary of the reserve path: the
generated amortized-grow call. -/
def reserveGrowSeam : Program := [ .call 106 ]

theorem func100_shape :
    func100 =
      [ .globalGet 0, .const (16 : UInt32), .sub, .localSet 2,
        .localGet 2, .globalSet 0,
        .localGet 0, .load32 (8 : UInt32), .localSet 3,
        .localGet 2, .localGet 0, .load32 (0 : UInt32),
        .store32 (12 : UInt32),
        .block 0 0 reserveBlockBody ] ++ reserveEpilogue := rfl

theorem reserveBlockBody_seam :
    reserveBlockBody = reserveBlockBody.take 17 ++ reserveGrowSeam := rfl

/-- The control frame that is on the stack while `reserveBlockBody` runs. -/
def reserveBlockFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := reserveBlockBody
    continuation := reserveEpilogue
    belowStack := [] }

/-- The call frame that `.call 102` pushes for `func100`. -/
def reserveCallFrame (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) : CallFrame :=
  { locals := { callerLocals with values := stack }
    continuation := code
    resultArity := arity
    callerRemainder := remainder
    control := controls }

/-! ## Small resource-shape helpers -/

private theorem pointsTo_u32_add_zero [WasmHeapGS]
    (address value : UInt32) :
    pointsTo_u32 address value ⊢ pointsTo_u32 (address + 0) value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u32_remove_zero [WasmHeapGS]
    (address value : UInt32) :
    pointsTo_u32 (address + 0) value ⊢ pointsTo_u32 address value := by
  rw [UInt32.add_zero]

private theorem globalPointsTo_i32_congr [WasmSmallStepGS hlc]
    (index : Nat) (lhs rhs : UInt32) (h : lhs = rhs) :
    globalPointsTo index (.i32 lhs) ⊢ globalPointsTo index (.i32 rhs) := by
  rw [h]

/-! ## Fast path: the request still fits -/

/-- Exact total body rule for `func100` when no growth is needed
(`additional ≤ capacity - len`, computed in wrapping `UInt32` arithmetic
exactly as the generated guard does).  The vector descriptor words are
untouched and the shadow stack pointer is restored. -/
theorem reserveNoGrow_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr additional stackTop capacity len old12 : UInt32)
    (hfast : ¬ capacity - len < additional)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hvecRoom : vecPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 vecPtr capacity ∗
      pointsTo_u32 (vecPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 vecPtr capacity -∗
        pointsTo_u32 (vecPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) capacity -∗
        WP (.running
          ⟨⟨[.i32 vecPtr, .i32 additional],
              [.i32 (stackTop - 16), .i32 len, .i32 0], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr, .i32 additional], [.i32 0, .i32 0, .i32 0], []⟩,
        func100, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  obtain ⟨hv00, hv01, hv02, hv03⟩ :=
    descriptorSlot32Facts vecPtr 0 12 hvecRoom (by decide)
  obtain ⟨hv80, hv81, hv82, hv83⟩ :=
    descriptorSlot32Facts vecPtr 8 12 hvecRoom (by decide)
  iintro ⟨Hglobal, Hcapacity, Hlen, Hframe12, Hdone⟩
  simp only [func100]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_load32 len (by simpa using hv80) (by simpa using hv81)
    (by simpa using hv82) (by simpa using hv83) $$ Hlen
  iintro Hlen
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HcapacityAt : pointsTo_u32 (vecPtr + 0) capacity $$ [Hcapacity]
  · iapply pointsTo_u32_add_zero
    iexact Hcapacity
  iapply twp_load32 capacity (by simp) (by simpa using hv01)
    (by simpa using hv02) (by simpa using hv03) $$ HcapacityAt
  iintro HcapacityAt
  iapply twp_store32 old12 (by simpa using hf120) (by simpa using hf121)
    (by simpa using hf122) (by simpa using hf123) $$ Hframe12
  iintro Hframe12
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 capacity (by simpa using hf120) (by simpa using hf121)
    (by simpa using hf122) (by simpa using hf123) $$ Hframe12
  iintro Hframe12
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_gtU (result := 0) (by simp [hfast])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (condition := 1) (depth := 0) (by decide) rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave HglobalRestored : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · iapply globalPointsTo_i32_congr 0
      (16 + (stackTop - 16)) stackTop (by bv_decide)
    iexact Hglobal
  ihave HcapacityBase : pointsTo_u32 vecPtr capacity $$ [HcapacityAt]
  · iapply pointsTo_u32_remove_zero
    iexact HcapacityAt
  iapply Hdone $$ HglobalRestored HcapacityBase Hlen Hframe12

/-- Composable total call rule for the reserve fast path at absolute Wasm
index `102`. -/
theorem reserveNoGrow_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr additional stackTop capacity len old12 : UInt32)
    (hfast : ¬ capacity - len < additional)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hvecRoom : vecPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 vecPtr capacity ∗
      pointsTo_u32 (vecPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 vecPtr capacity -∗
        pointsTo_u32 (vecPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) capacity -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 additional, .i32 vecPtr] ++ stack },
        .call 102 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hcapacity, Hlen, Hframe12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 102 func100Def
      (by decide) vecReserve_index $$ Hruntime
  iintro Hruntime
  simp [func100Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := reserveNoGrow_body_twp (α := α)
    vecPtr additional stackTop capacity len old12 hfast hframeRoom hvecRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hcapacity]
  · iexact Hcapacity
  isplitl [Hlen]
  · iexact Hlen
  isplitl [Hframe12]
  · iexact Hframe12
  iintro Hglobal Hcapacity Hlen Hframe12
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hcapacity Hlen Hframe12

/-! ## Grow path: entry to the amortized-grow seam -/

/-- Exact total segment rule for `func100` on the grow path
(`capacity - len < additional`): from function entry to exactly the
generated `.call 106`.  The boundary state is fully explicit; the stack
holds `func104`'s five arguments (top first: element size `8`, alignment
`8`, `additional`, `len`, `vecPtr`), and the shadow stack pointer is at
`func100`'s own frame `stackTop - 16`. -/
theorem reserve_body_to_grow_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr additional stackTop capacity len old12 : UInt32)
    (hgrow : capacity - len < additional)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hvecRoom : vecPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 vecPtr capacity ∗
      pointsTo_u32 (vecPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        pointsTo_u32 vecPtr capacity -∗
        pointsTo_u32 (vecPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) capacity -∗
        WP (.running
          ⟨⟨[.i32 vecPtr, .i32 additional],
              [.i32 (stackTop - 16), .i32 len, .i32 8],
              [.i32 8, .i32 8, .i32 additional, .i32 len, .i32 vecPtr]⟩,
            reserveGrowSeam, 0, [], [reserveBlockFrame], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr, .i32 additional], [.i32 0, .i32 0, .i32 0], []⟩,
        func100, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  obtain ⟨hv00, hv01, hv02, hv03⟩ :=
    descriptorSlot32Facts vecPtr 0 12 hvecRoom (by decide)
  obtain ⟨hv80, hv81, hv82, hv83⟩ :=
    descriptorSlot32Facts vecPtr 8 12 hvecRoom (by decide)
  simp only [reserveGrowSeam, reserveBlockFrame, reserveBlockBody,
    reserveEpilogue]
  iintro ⟨Hglobal, Hcapacity, Hlen, Hframe12, Hdone⟩
  simp only [func100]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_load32 len (by simpa using hv80) (by simpa using hv81)
    (by simpa using hv82) (by simpa using hv83) $$ Hlen
  iintro Hlen
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HcapacityAt : pointsTo_u32 (vecPtr + 0) capacity $$ [Hcapacity]
  · iapply pointsTo_u32_add_zero
    iexact Hcapacity
  iapply twp_load32 capacity (by simp) (by simpa using hv01)
    (by simpa using hv02) (by simpa using hv03) $$ HcapacityAt
  iintro HcapacityAt
  iapply twp_store32 old12 (by simpa using hf120) (by simpa using hf121)
    (by simpa using hf122) (by simpa using hf123) $$ Hframe12
  iintro Hframe12
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 capacity (by simpa using hf120) (by simpa using hf121)
    (by simpa using hf122) (by simpa using hf123) $$ Hframe12
  iintro Hframe12
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_gtU (result := 1) (by simp [hgrow])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HcapacityBase : pointsTo_u32 vecPtr capacity $$ [HcapacityAt]
  · iapply pointsTo_u32_remove_zero
    iexact HcapacityAt
  iapply Hdone $$ Hglobal HcapacityBase Hlen Hframe12

/-- Composable segment rule from the caller's `.call 102` to exactly the
generated `.call 106` grow seam, mirroring the boundary state left by
`InputIteratorProof.vecExtendLoop_grow_to_reserve_twp`. -/
theorem reserve_call_to_grow_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr additional stackTop capacity len old12 : UInt32)
    (hgrow : capacity - len < additional)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hvecRoom : vecPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 vecPtr capacity ∗
      pointsTo_u32 (vecPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        pointsTo_u32 vecPtr capacity -∗
        pointsTo_u32 (vecPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) capacity -∗
        WP (.running
          ⟨⟨[.i32 vecPtr, .i32 additional],
              [.i32 (stackTop - 16), .i32 len, .i32 8],
              [.i32 8, .i32 8, .i32 additional, .i32 len, .i32 vecPtr]⟩,
            reserveGrowSeam, 0, [], [reserveBlockFrame],
            reserveCallFrame callerLocals stack code arity remainder
              controls :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 additional, .i32 vecPtr] ++ stack },
        .call 102 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [reserveCallFrame]
  iintro ⟨Hruntime, Hglobal, Hcapacity, Hlen, Hframe12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 102 func100Def
      (by decide) vecReserve_index $$ Hruntime
  iintro Hruntime
  simp [func100Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := reserve_body_to_grow_twp (α := α)
    vecPtr additional stackTop capacity len old12 hgrow hframeRoom hvecRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hcapacity]
  · iexact Hcapacity
  isplitl [Hlen]
  · iexact Hlen
  isplitl [Hframe12]
  · iexact Hframe12
  iintro Hglobal Hcapacity Hlen Hframe12
  iapply Hdone $$ Hruntime Hglobal Hcapacity Hlen Hframe12

/-! ## Grow path: from the returned seam back to the caller -/

/-- Exact total segment rule for `func100`'s epilogue: from the state in
which `.call 106` has just returned (empty block continuation) to the
generated `[.ret]`.  The shadow stack pointer is restored to `stackTop`;
`.call 106` leaves it at `func100`'s frame, so the premise takes it there. -/
theorem reserveGrow_finish_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr additional stackTop len : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 (stackTop - 16)) ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        WP (.running
          ⟨⟨[.i32 vecPtr, .i32 additional],
              [.i32 (stackTop - 16), .i32 len, .i32 8], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr, .i32 additional],
          [.i32 (stackTop - 16), .i32 len, .i32 8], []⟩,
        [], 0, [], [reserveBlockFrame], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [reserveBlockFrame, reserveBlockBody, reserveEpilogue]
  iintro ⟨Hglobal, Hdone⟩
  iapply twp_exitControl (by decide)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave HglobalRestored : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · iapply globalPointsTo_i32_congr 0
      (16 + (stackTop - 16)) stackTop (by bv_decide)
    iexact Hglobal
  iapply Hdone $$ HglobalRestored

/-- Composable epilogue rule: from the returned `.call 106` seam all the way
back into the continuation of the caller of `.call 102`. -/
theorem reserveGrow_finish_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr additional stackTop len : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 (stackTop - 16)) ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr, .i32 additional],
          [.i32 (stackTop - 16), .i32 len, .i32 8], []⟩,
        [], 0, [], [reserveBlockFrame],
        reserveCallFrame callerLocals stack code arity remainder
          controls :: calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [reserveCallFrame]
  iintro ⟨Hglobal, Hdone⟩
  iapply reserveGrow_finish_body_twp (α := α) vecPtr additional stackTop len
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hglobal

/-! ## The composed reserve contract, parameterized by the grow core

`Pre`/`Post` abstract the grow-core footprint (allocator state, the new
data array, the rewritten capacity and data descriptor slots, …).  The
`growCore` hypothesis is the one missing total contract of the reserve
path: generated local `func104` (`.call 106`) invoked with the argument
stack `[.i32 8, .i32 8, .i32 additional, .i32 len, .i32 vecPtr]` (top
first) while the shadow stack pointer sits at `stackTop - 16`.  Once the
allocator agents deliver it, instantiating this theorem yields the
seam-free reserve contract at `.call 102`. -/
theorem vecReserveGrow_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr additional stackTop capacity len old12 : UInt32)
    (hgrow : capacity - len < additional)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hvecRoom : vecPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (Pre Post : IProp WasmHeapGF)
    (growCore :
      (iprop% runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 (stackTop - 16)) ∗
        pointsTo_u32 vecPtr capacity ∗
        pointsTo_u32 (vecPtr + 8) len ∗
        Pre ∗
        (runtimeModuleOwn «module» -∗
          globalPointsTo 0 (.i32 (stackTop - 16)) -∗
          Post -∗
          WP (.running
            ⟨⟨[.i32 vecPtr, .i32 additional],
                [.i32 (stackTop - 16), .i32 len, .i32 8], []⟩,
              [], 0, [], [reserveBlockFrame],
              reserveCallFrame callerLocals stack code arity remainder
                controls :: calls⟩ : Expr α)
            @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨[.i32 vecPtr, .i32 additional],
            [.i32 (stackTop - 16), .i32 len, .i32 8],
            [.i32 8, .i32 8, .i32 additional, .i32 len, .i32 vecPtr]⟩,
          reserveGrowSeam, 0, [], [reserveBlockFrame],
          reserveCallFrame callerLocals stack code arity remainder
            controls :: calls⟩ : Expr α)
        @ s; E [{ Φ }]) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 vecPtr capacity ∗
      pointsTo_u32 (vecPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      Pre ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 12) capacity -∗
        Post -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 additional, .i32 vecPtr] ++ stack },
        .call 102 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hcapacity, Hlen, Hframe12, Hpre, Hdone⟩
  iapply reserve_call_to_grow_twp (α := α)
    vecPtr additional stackTop capacity len old12 hgrow hframeRoom hvecRoom
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hcapacity]
  · iexact Hcapacity
  isplitl [Hlen]
  · iexact Hlen
  isplitl [Hframe12]
  · iexact Hframe12
  iintro Hruntime Hglobal Hcapacity Hlen Hframe12
  iapply growCore
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hcapacity]
  · iexact Hcapacity
  isplitl [Hlen]
  · iexact Hlen
  isplitl [Hpre]
  · iexact Hpre
  iintro Hruntime Hglobal Hpost
  iapply reserveGrow_finish_call_twp (α := α) vecPtr additional stackTop len
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hdone $$ Hruntime Hglobal Hframe12 Hpost

/-! ## One level deeper: the amortized grow wrapper `func104`

`.call 106` reaches local `func104`, which allocates its own sixteen-byte
frame, forwards `(retPtr, vecPtr, len, additional, arg3, arg4)` to the
amortized-grow core `func117` (call immediate `119`), and afterwards
panics via `.call 203`/`.unreachable` unless the returned first result
word is the generated success sentinel `2147483649` (`0x80000001`,
kept in static memory at `1049936` for the success path of `func117`).
The rules below prove `func104` totally around its single `.call 119`
boundary, so the reserve seam can be pushed from `.call 106` down to
`.call 119` once the `func117` arithmetic segment lands. -/

/-- Local `func117` is the amortized-grow core reached from `func104`;
its call immediate is `119`. -/
theorem growAmortized_index : «module».funcs[117]? = some func117Def := by rfl

/-- `func104` after its forwarded grow call: the success check and the
panic guard. -/
def growWrapperAfterSeam : Program := func104.drop 13

theorem func104_seam_shape :
    func104 =
      [ .globalGet 0, .const (16 : UInt32), .sub, .localSet 5,
        .localGet 5, .globalSet 0,
        .localGet 5, .localGet 0, .localGet 1, .localGet 2, .localGet 3,
        .localGet 4 ] ++ .call 119 :: growWrapperAfterSeam := rfl

private theorem twp_eq
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .eq :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.eq hresult)

/-- Exact total segment rule for `func104` from entry to exactly the
forwarded `.call 119`.  The stack holds `func117`'s six arguments (top
first: `arg4`, `arg3`, `additional`, `len`, `vecPtr`, and the result
pointer `stackTop - 16`). -/
theorem growWrapper_body_to_amortized_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr len additional arg3 arg4 stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3,
                .i32 arg4],
              [.i32 (stackTop - 16), .i32 0, .i32 0],
              [.i32 arg4, .i32 arg3, .i32 additional, .i32 len,
                .i32 vecPtr, .i32 (stackTop - 16)]⟩,
            .call 119 :: growWrapperAfterSeam, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3, .i32 arg4],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func104, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  simp only [growWrapperAfterSeam, func104, List.drop_succ_cons,
    List.drop_zero]
  iintro ⟨Hglobal, Hdone⟩
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Hdone $$ Hglobal

/-- Exact total rule for `func104` after `.call 119` has returned: the
success check cannot panic when the returned first result word is the
generated success sentinel, and the wrapper frame is popped. -/
theorem growWrapper_finish_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr len additional arg3 arg4 stackTop : UInt32)
    (result0 result4 old8 old12 : UInt32)
    (hsuccess : result0 = 2147483649)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 (stackTop - 16)) ∗
      pointsTo_u32 (stackTop - 16) result0 ∗
      pointsTo_u32 ((stackTop - 16) + 4) result4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (stackTop - 16) result0 -∗
        pointsTo_u32 ((stackTop - 16) + 4) result4 -∗
        pointsTo_u32 ((stackTop - 16) + 8) result0 -∗
        pointsTo_u32 ((stackTop - 16) + 12) result4 -∗
        WP (.running
          ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3,
                .i32 arg4],
              [.i32 (stackTop - 16), .i32 result4, .i32 1], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3, .i32 arg4],
          [.i32 (stackTop - 16), .i32 0, .i32 0], []⟩,
        growWrapperAfterSeam, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf00, hf01, hf02, hf03⟩ :=
    descriptorSlot32Facts (stackTop - 16) 0 16 hframeRoom (by decide)
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts (stackTop - 16) 4 16 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  iintro ⟨Hglobal, Hresult0, Hresult4, Hframe8, Hframe12, Hdone⟩
  simp only [growWrapperAfterSeam, func104, List.drop_succ_cons,
    List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_load32 result4 (by simpa using hf40) (by simpa using hf41)
    (by simpa using hf42) (by simpa using hf43) $$ Hresult4
  iintro Hresult4
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hresult0At : pointsTo_u32 ((stackTop - 16) + 0) result0 $$
      [Hresult0]
  · iapply pointsTo_u32_add_zero
    iexact Hresult0
  iapply twp_load32 result0 (by simp) (by simpa using hf01)
    (by simpa using hf02) (by simpa using hf03) $$ Hresult0At
  iintro Hresult0At
  iapply twp_store32 old8 (by simpa using hf80) (by simpa using hf81)
    (by simpa using hf82) (by simpa using hf83) $$ Hframe8
  iintro Hframe8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old12 (by simpa using hf120) (by simpa using hf121)
    (by simpa using hf122) (by simpa using hf123) $$ Hframe12
  iintro Hframe12
  iapply twp_localGet rfl
  iapply twp_load32 result0 (by simpa using hf80) (by simpa using hf81)
    (by simpa using hf82) (by simpa using hf83) $$ Hframe8
  iintro Hframe8
  iapply twp_const
  iapply twp_eq (result := 1) (by simp [hsuccess])
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_const
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_selectI32 (selected := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (condition := 1) (depth := 0) (by decide) rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave HglobalRestored : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · iapply globalPointsTo_i32_congr 0
      (16 + (stackTop - 16)) stackTop (by bv_decide)
    iexact Hglobal
  ihave Hresult0Base : pointsTo_u32 (stackTop - 16) result0 $$ [Hresult0At]
  · iapply pointsTo_u32_remove_zero
    iexact Hresult0At
  iapply Hdone $$ HglobalRestored Hresult0Base Hresult4 Hframe8 Hframe12

/-- Composable segment rule from a caller's `.call 106` to exactly the
forwarded `.call 119` inside `func104`. -/
theorem growWrapper_call_to_amortized_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr len additional arg3 arg4 stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3,
                .i32 arg4],
              [.i32 (stackTop - 16), .i32 0, .i32 0],
              [.i32 arg4, .i32 arg3, .i32 additional, .i32 len,
                .i32 vecPtr, .i32 (stackTop - 16)]⟩,
            .call 119 :: growWrapperAfterSeam, 0, [], [],
            reserveCallFrame callerLocals stack code arity remainder
              controls :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 arg4, .i32 arg3, .i32 additional, .i32 len,
            .i32 vecPtr] ++ stack },
        .call 106 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [reserveCallFrame]
  iintro ⟨Hruntime, Hglobal, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 106 func104Def
      (by decide) growAmortizedWrapper_index $$ Hruntime
  iintro Hruntime
  simp [func104Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := growWrapper_body_to_amortized_twp (α := α)
    vecPtr len additional arg3 arg4 stackTop
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hdone $$ Hruntime Hglobal

/-- Composable epilogue rule: from the returned `.call 119` seam through
`func104`'s success guard back into the continuation of the caller of
`.call 106`. -/
theorem growWrapper_finish_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr len additional arg3 arg4 stackTop : UInt32)
    (result0 result4 old8 old12 : UInt32)
    (hsuccess : result0 = 2147483649)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 (stackTop - 16)) ∗
      pointsTo_u32 (stackTop - 16) result0 ∗
      pointsTo_u32 ((stackTop - 16) + 4) result4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (stackTop - 16) result0 -∗
        pointsTo_u32 ((stackTop - 16) + 4) result4 -∗
        pointsTo_u32 ((stackTop - 16) + 8) result0 -∗
        pointsTo_u32 ((stackTop - 16) + 12) result4 -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3, .i32 arg4],
          [.i32 (stackTop - 16), .i32 0, .i32 0], []⟩,
        growWrapperAfterSeam, 0, [], [],
        reserveCallFrame callerLocals stack code arity remainder
          controls :: calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [reserveCallFrame]
  iintro ⟨Hglobal, Hresult0, Hresult4, Hframe8, Hframe12, Hdone⟩
  iapply growWrapper_finish_body_twp (α := α)
    vecPtr len additional arg3 arg4 stackTop result0 result4 old8 old12
    hsuccess hframeRoom
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hframe12]
  · iexact Hframe12
  iintro Hglobal Hresult0 Hresult4 Hframe8 Hframe12
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hglobal Hresult0 Hresult4 Hframe8 Hframe12

/-- The composed `.call 106` contract, parameterized by the one missing
total contract of the grow path: the amortized-grow core `func117`
(`.call 119`) with argument stack
`[.i32 arg4, .i32 arg3, .i32 additional, .i32 len, .i32 vecPtr,
.i32 (stackTop - 16)]` (top first) while the shadow stack pointer sits at
`stackTop - 16`.  Its `Post` must yield the two result words at the
wrapper frame, with first word the success sentinel `2147483649`. -/
theorem growWrapper_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr len additional arg3 arg4 stackTop : UInt32)
    (result4 old0 old4 old8 old12 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (Pre Post : IProp WasmHeapGF)
    (amortizedCore :
      (iprop% globalPointsTo 0 (.i32 (stackTop - 16)) ∗
        pointsTo_u32 (stackTop - 16) old0 ∗
        pointsTo_u32 ((stackTop - 16) + 4) old4 ∗
        Pre ∗
        (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
          pointsTo_u32 (stackTop - 16) 2147483649 -∗
          pointsTo_u32 ((stackTop - 16) + 4) result4 -∗
          Post -∗
          WP (.running
            ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3,
                  .i32 arg4],
                [.i32 (stackTop - 16), .i32 0, .i32 0], []⟩,
              growWrapperAfterSeam, 0, [], [],
              reserveCallFrame callerLocals stack code arity remainder
                controls :: calls⟩ : Expr α)
            @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨[.i32 vecPtr, .i32 len, .i32 additional, .i32 arg3,
              .i32 arg4],
            [.i32 (stackTop - 16), .i32 0, .i32 0],
            [.i32 arg4, .i32 arg3, .i32 additional, .i32 len,
              .i32 vecPtr, .i32 (stackTop - 16)]⟩,
          .call 119 :: growWrapperAfterSeam, 0, [], [],
          reserveCallFrame callerLocals stack code arity remainder
            controls :: calls⟩ : Expr α)
        @ s; E [{ Φ }]) :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (stackTop - 16) old0 ∗
      pointsTo_u32 ((stackTop - 16) + 4) old4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) old12 ∗
      Pre ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (stackTop - 16) 2147483649 -∗
        pointsTo_u32 ((stackTop - 16) + 4) result4 -∗
        pointsTo_u32 ((stackTop - 16) + 8) 2147483649 -∗
        pointsTo_u32 ((stackTop - 16) + 12) result4 -∗
        Post -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 arg4, .i32 arg3, .i32 additional, .i32 len,
            .i32 vecPtr] ++ stack },
        .call 106 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hold0, Hold4, Hold8, Hold12, Hpre, Hdone⟩
  iapply growWrapper_call_to_amortized_twp (α := α)
    vecPtr len additional arg3 arg4 stackTop
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hruntime Hglobal
  iapply amortizedCore
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hold0]
  · iexact Hold0
  isplitl [Hold4]
  · iexact Hold4
  isplitl [Hpre]
  · iexact Hpre
  iintro Hglobal Hresult0 Hresult4 Hpost
  iapply growWrapper_finish_call_twp (α := α)
    vecPtr len additional arg3 arg4 stackTop 2147483649 result4 old8 old12
    rfl hframeRoom
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  isplitl [Hold8]
  · iexact Hold8
  isplitl [Hold12]
  · iexact Hold12
  iintro Hglobal Hresult0 Hresult4 Hframe8 Hframe12
  iapply Hdone $$ Hruntime Hglobal Hresult0 Hresult4 Hframe8 Hframe12 Hpost

end Project.Mergesort.ReserveProof
