import HexEncodeStdio.Blueprint
import HexEncodeStdio.MainOperational
import HexEncodeStdio.EncodeResourceCost
import HexEncodeStdio.WriteResourceCost
import CodeLib.SepLogic.CostedLoop
import CodeLib.SepLogic.CostedStepsStdIO
import CodeLib.SepLogic.CostedTerminalBounds
import CodeLib.SepLogic.HostMemoryTrace

/-! # Connecting resource certificates to the named hex encoder

These control segments retain their actual traces and caller configurations.
The functional adapter applies the existing total success/OOM specification to
the same normal-return execution used by a resource certificate.
-/

namespace Project.HexEncodeStdio.ExportResourceCost

open Wasm Wasm.SmallStep Project.HexStdio

def entryTrace : List StepKind :=
  [.instruction (.globalGet 0), .instruction (.const 32), .instruction .sub,
    .instruction (.localTee 0), .instruction (.globalSet 0),
    .instruction (.localGet 0), .instruction (.const 8), .instruction .add]

def readCallConfig (input : List UInt8) : Config Universal.State :=
  ⟨.running
    ⟨⟨[], [.i32 1048544, .i32 0, .i32 0, .i32 0], [.i32 1048552]⟩,
      [.call 10] ++ func10.drop 9, 0, [], [], []⟩,
    encodeFrameStore input⟩

/-- The actual named-export body reaches the input function in eight scalar
transitions, retaining its stack-pointer update and original host input. -/
theorem export_to_read_cost (input : List UInt8) :
    CostedSteps CostedStdIO.work (encodeInitialConfig input) entryTrace
      (readCallConfig input) 8 := by
  apply Steps.with_unit_cost
  · simp only [encodeInitialConfig, readCallConfig, entryTrace, func10, List.drop]
    apply Steps.cons (Step.globalGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.sub
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.globalSet rfl)
    rw [setGlobal_zero_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    simp [encodeFrameStore]
    exact Steps.refl _
  · intro before kind after member
    simp only [entryTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem entryTrace_primary : ∀ kind ∈ entryTrace, HostPrimaryMemoryKind kind := by
  intro kind member
  simp only [entryTrace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

def afterReadTrace : List StepKind :=
  [.instruction (.localGet 0), .instruction (.const 20), .instruction .add,
    .instruction (.localGet 0), .instruction (.load32 12),
    .instruction (.localTee 1), .instruction (.localGet 0),
    .instruction (.load32 16)]

def encodeCallConfig (store : MachineStore Universal.State)
    (pointer length : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[], [.i32 1048544, .i32 pointer, .i32 0, .i32 0],
        [.i32 length, .i32 pointer, .i32 1048564]⟩,
      [.call 9] ++ func10.drop 18, 0, [], [], []⟩, store⟩

/-- Eight scalar transitions connect the complete reader's returned vector to
the encoder call. Both vector fields are read from the actual returned store. -/
theorem after_read_to_encode_cost (store : MachineStore Universal.State)
    (pointer length : UInt32)
    (hpointer : store.wasm.mem.read32 1048556 = pointer)
    (hlength : store.wasm.mem.read32 1048560 = length)
    (hpages : 17 ≤ store.wasm.mem.pages) :
    CostedSteps CostedStdIO.work (encodeAfterReadConfig store) afterReadTrace
      (encodeCallConfig store pointer length) 8 := by
  apply Steps.with_unit_cost
  · simp only [encodeAfterReadConfig, encodeCallConfig, afterReadTrace, func10, List.drop]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048560 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 12 = 1048556 from rfl, hpointer]
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048564 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 16 = 1048560 from rfl, hlength]
    exact Steps.refl _
  · intro before kind after member
    simp only [afterReadTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem afterReadTrace_primary :
    ∀ kind ∈ afterReadTrace, HostPrimaryMemoryKind kind := by
  intro kind member
  simp only [afterReadTrace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

def allocationSetupTrace : List StepKind :=
  [.instruction (.call 9)] ++ (func6.take 16).map StepKind.instruction ++
    [.instruction (.localGet 2), .instruction .eqz, .instruction (.br_if 0),
      .instruction (.localGet 3), .instruction (.const 4), .instruction .add,
      .instruction (.const 0), .instruction (.localGet 2),
      .instruction (.const 1), .instruction .shl]

/-- Entering the generated encoder and initializing its output-vector header
costs 27 scalar transitions before the actual reserve call. -/
theorem encode_call_to_reserve_cost
    (store : MachineStore Universal.State) (pointer length : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hlength : length ≠ 0) (hpages : 17 ≤ store.wasm.mem.pages) :
    CostedSteps CostedStdIO.work (encodeCallConfig store pointer length)
      allocationSetupTrace (encodeReserveConfig store pointer length) 27 := by
  apply Steps.with_unit_cost
  · simp only [encodeCallConfig, allocationSetupTrace, func6, List.take,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    apply Steps.cons (Step.call (fn := func6Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    simp only [func6Def, Function.toLocals, Function.numParams, func6]
    apply Steps.cons (Step.globalGet hglobal)
    apply Steps.cons Step.const
    apply Steps.cons Step.sub
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.globalSet (by simp [hglobal]))
    rw [setGlobal_zero_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.store32 rfl (by change 1048528 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.constI64
    apply Steps.cons (Step.store64 rfl (by change 1048524 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.add
    apply Steps.cons (Step.localSet rfl)
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.eqz (result := 0) (by simp [hlength]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    apply Steps.cons Step.const
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.shl
    simp [encodeReserveConfig, encodeAllocFrameStore, encodeReserveControls,
      encodeMainCalls, UInt32.add_comm]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

theorem allocationSetupTrace_primary :
    ∀ kind ∈ allocationSetupTrace, HostPrimaryMemoryKind kind := by
  intro kind member
  fin_cases member <;> trivial

def emptyEncoderStore (store : MachineStore Universal.State)
    (pointer : UInt32) : MachineStore Universal.State :=
  let framed := encodeAllocFrameStore store
  let memory := ((framed.wasm.mem.write32 1048540 1048576).write32 1048536 pointer).write32 1048532 pointer
  { framed with wasm := { framed.wasm with mem := memory.write32 1048528 1114112 } }

def emptyIteratorLocals (pointer : UInt32) (values : List Value := []) : Locals :=
  ⟨[.i32 1048564, .i32 pointer, .i32 0],
    [.i32 1048512, .i32 pointer, .i32 0, .i32 0, .i32 0, .i32 0], values⟩

def encoderOuterControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := TotalEncodeLoop.encodeOuterBody,
    continuation := func6.drop 29, belowStack := [] }

def emptyIteratorConfig (store : MachineStore Universal.State)
    (pointer : UInt32) : Config Universal.State :=
  ⟨.running ⟨emptyIteratorLocals pointer [.i32 1048528],
    .call 21 :: TotalEncodeLoop.encodeOuterBody.drop 4, 0, [],
    [encoderOuterControl], encodeMainCalls store pointer⟩,
    emptyEncoderStore store pointer⟩

def emptySetupTrace : List StepKind :=
  [.instruction (.call 9)] ++ (func6.take 16).map StepKind.instruction ++
    [.instruction (.localGet 2), .instruction .eqz, .instruction (.br_if 0)] ++
    ((func6.drop 16).take 13).map StepKind.instruction ++
    [.instruction (.localGet 3), .instruction (.const 16), .instruction .add]

/-- Empty input skips allocation and reaches the same iterator endpoint test
as nonempty input. Its iterator cursor equals its end pointer. -/
theorem empty_encoder_to_iterator_cost
    (store : MachineStore Universal.State) (pointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : 17 ≤ store.wasm.mem.pages) :
    CostedSteps CostedStdIO.work (encodeCallConfig store pointer 0)
      emptySetupTrace (emptyIteratorConfig store pointer) 36 := by
  apply Steps.with_unit_cost
  · simp only [encodeCallConfig, emptySetupTrace, func6, List.take, List.drop,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    apply Steps.cons (Step.call (fn := func6Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    simp only [func6Def, Function.toLocals, Function.numParams, func6]
    apply Steps.cons (Step.globalGet hglobal)
    apply Steps.cons Step.const
    apply Steps.cons Step.sub
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.globalSet (by simp [hglobal]))
    rw [setGlobal_zero_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.store32 rfl (by change 1048528 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.constI64
    apply Steps.cons (Step.store64 rfl (by change 1048524 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.add
    apply Steps.cons (Step.localSet rfl)
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.eqz (result := 1) (by decide))
    apply Steps.cons (Step.brIf (condition := 1) (by decide) rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.store32 rfl (by change 1048544 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.store32 rfl (by change 1048540 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.store32 rfl (by change 1048536 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.store32 rfl (by change 1048532 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    simp [emptyIteratorConfig, emptyIteratorLocals, emptyEncoderStore,
      encodeAllocFrameStore, encoderOuterControl, TotalEncodeLoop.encodeOuterBody,
      encodeMainCalls, UInt32.add_zero, UInt32.add_comm]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

theorem emptySetupTrace_primary :
    ∀ kind ∈ emptySetupTrace, HostPrimaryMemoryKind kind := by
  intro kind member
  fin_cases member <;> trivial

def emptyEncodedStore (store : MachineStore Universal.State)
    (pointer : UInt32) : MachineStore Universal.State :=
  EncodeResourceCost.finishStore
    (EncodeResourceCost.iteratorResetStore (emptyEncoderStore store pointer) 1048528)
    1048564 1048512 0 4294967296

def afterEncodeConfig (store : MachineStore Universal.State)
    (pointer : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[], [.i32 1048544, .i32 pointer, .i32 0, .i32 0], []⟩,
    func10.drop 18, 0, [], [], []⟩, store⟩

/-- The full zero-length encoder call performs no allocation or byte transfer.
It publishes the empty vector and returns to the original main continuation. -/
theorem empty_encoder_cost
    (store : MachineStore Universal.State) (pointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : 17 ≤ store.wasm.mem.pages) :
    ∃ trace, CostedSteps CostedStdIO.work (encodeCallConfig store pointer 0) trace
      (afterEncodeConfig (emptyEncodedStore store pointer) pointer) 76 ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  let entered := emptyEncoderStore store pointer
  let reset := EncodeResourceCost.iteratorResetStore entered 1048528
  have hcurrent : entered.wasm.mem.read32 1048528 = EncodeResourceCost.sentinel := by
    exact Mem.read32_write32_same _ _ _
  have hcursor : entered.wasm.mem.read32 (1048528 + 4) = pointer := by
    dsimp only [entered, emptyEncoderStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)]
    exact Mem.read32_write32_same _ _ _
  have hend : entered.wasm.mem.read32 (1048528 + 8) = pointer := by
    dsimp only [entered, emptyEncoderStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)]
    exact Mem.read32_write32_same _ _ _
  obtain ⟨iteratorTrace, iteratorRun, iteratorLabels⟩ :=
    EncodeResourceCost.iterator_end_cost entered (emptyIteratorLocals pointer) []
      (TotalEncodeLoop.encodeOuterBody.drop 4) 0 [] [encoderOuterControl]
      (encodeMainCalls store pointer) 1048528 pointer hmodule hcurrent hcursor hend
      (by change 1048540 ≤ store.wasm.mem.pages * 65536; omega) (by decide)
  let branched := EncodeResourceCost.encodeLocals 1048564 pointer
    EncodeResourceCost.sentinel 1048512 pointer 0 0 0 0
  let branchTrace : List StepKind := [.instruction (.localTee 2),
    .instruction (.const 1114112), .instruction .eq, .instruction (.br_if 0)]
  have branchRun : CostedSteps CostedStdIO.work
      ⟨.running ⟨{ emptyIteratorLocals pointer with values := [.i32 EncodeResourceCost.sentinel] },
        TotalEncodeLoop.encodeOuterBody.drop 4, 0, [], [encoderOuterControl],
        encodeMainCalls store pointer⟩, reset⟩ branchTrace
      ⟨.running ⟨branched, TotalEncodeFunction.func6FinishCode, 0, [], [],
        encodeMainCalls store pointer⟩, reset⟩ 4 := by
    apply Steps.with_unit_cost
    · dsimp only [branchTrace]
      apply Steps.cons (Step.localTee rfl)
      apply Steps.cons Step.const
      apply Steps.cons (Step.eq (result := 1) (by decide))
      exact Steps.single (Step.brIf (condition := 1) (by decide) rfl)
    · intro before kind after member
      simp only [branchTrace, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
  have hlength : reset.wasm.mem.read32 (1048512 + 12) = 0 := by
    dsimp only [reset, entered, EncodeResourceCost.iteratorResetStore,
      emptyEncoderStore, encodeAllocFrameStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write64_disjoint _ _ _ _ (by decide)]
    exact Mem.read32_write32_same _ _ _
  have hpair : reset.wasm.mem.read64 (1048512 + 4) = 4294967296 := by
    dsimp only [reset, entered, EncodeResourceCost.iteratorResetStore,
      emptyEncoderStore, encodeAllocFrameStore]
    rw [Mem.read64_write32_disjoint _ _ _ _ (by decide),
      Mem.read64_write32_disjoint _ _ _ _ (by decide),
      Mem.read64_write32_disjoint _ _ _ _ (by decide),
      Mem.read64_write32_disjoint _ _ _ _ (by decide),
      Mem.read64_write32_disjoint _ _ _ _ (by decide)]
    exact Mem.read64_write64_same _ _ _
  have hglobalReset : (globalAt? reset 0).isSome = true := by
    have hzero : 0 < store.wasm.globals.globals.length := by
      have := (getElem?_eq_some_iff.mp (show store.wasm.globals.globals[0]? =
        some (.i32 1048544) by simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
      exact this
    simp [reset, entered, EncodeResourceCost.iteratorResetStore, emptyEncoderStore,
      encodeAllocFrameStore, globalAt?, canonicalGlobalIndex_zero, hzero]
  obtain ⟨finishTrace, finishRun, finishLabels⟩ :=
    EncodeResourceCost.finish_body_cost reset 1048564 pointer EncodeResourceCost.sentinel
      1048512 pointer 0 0 0 0 0 4294967296 0 [] [] (encodeMainCalls store pointer)
      hglobalReset hlength hpair
      (by change 1048528 ≤ store.wasm.mem.pages * 65536; omega)
      (by change 1048576 ≤ store.wasm.mem.pages * 65536; omega) (by decide)
  have returned : CostedSteps CostedStdIO.work
      ⟨.running ⟨branched, [], 0, [], [], encodeMainCalls store pointer⟩,
        emptyEncodedStore store pointer⟩ [.administrative .returnFromCall]
      (afterEncodeConfig (emptyEncodedStore store pointer) pointer) 1 :=
    CostedSteps.single (Step.returnFromCallFallthrough rfl)
  have setup := empty_encoder_to_iterator_cost store pointer hmodule hglobal hpages
  have run := ((setup.trans iteratorRun).trans branchRun).trans (finishRun.trans returned)
  refine ⟨_, run, ?_⟩
  intro kind member
  simp only [List.mem_append] at member
  rcases member with ((setup | iterator) | branch) | finish | returnLabel
  · exact emptySetupTrace_primary kind setup
  · exact iteratorLabels kind iterator
  · simp only [branchTrace, List.mem_cons, List.not_mem_nil, or_false] at branch
    rcases branch with rfl | rfl | rfl | rfl <;> trivial
  · exact finishLabels kind finish
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at returnLabel
    subst kind
    trivial

def restoredMainStore (store : MachineStore Universal.State) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with globals :=
    { globals := store.wasm.globals.globals.set 0 (.i32 1048576) } } }

def emptyCleanupTrace : List StepKind :=
  [.instruction (.block 0 0 [.localGet 0, .load32 20, .localTee 3, .eqz, .br_if 0,
    .localGet 2, .localGet 3, .const 1, .call 17]), .instruction (.localGet 0),
    .instruction (.load32 20), .instruction (.localTee 3), .instruction .eqz,
    .instruction (.br_if 0), .instruction (.block 0 0 [.localGet 0, .load32 8, .localTee 2, .eqz, .br_if 0,
      .localGet 1, .localGet 2, .const 1, .call 17]),
    .instruction (.localGet 0), .instruction (.load32 8), .instruction (.localTee 2),
    .instruction .eqz, .instruction (.br_if 0), .instruction (.localGet 0),
    .instruction (.const 32), .instruction .add, .instruction (.globalSet 0),
    .administrative .finish]

/-- Empty vectors skip both deallocation calls; the wrapper then restores its
stack pointer and reaches an actual normal terminal state. -/
theorem empty_main_cleanup_cost
    (store : MachineStore Universal.State) (inputPointer outputPointer : UInt32)
    (houtputCapacity : store.wasm.mem.read32 1048564 = 0)
    (hinputCapacity : store.wasm.mem.read32 1048552 = 0)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : 17 ≤ store.wasm.mem.pages) :
    CostedSteps CostedStdIO.work
      ⟨.running ⟨⟨[], [.i32 1048544, .i32 inputPointer, .i32 outputPointer, .i32 0], []⟩,
        func10.drop 24, 0, [], [], []⟩, store⟩ emptyCleanupTrace
      ⟨.done [], restoredMainStore store⟩ 17 := by
  apply Steps.with_unit_cost
  · simp only [emptyCleanupTrace, func10, List.drop]
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048568 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 20 = 1048564 from rfl, houtputCapacity]
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.eqz (result := 1) (by decide))
    apply Steps.cons (Step.brIf (condition := 1) (by decide) rfl)
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048556 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 8 = 1048552 from rfl, hinputCapacity]
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.eqz (result := 1) (by decide))
    apply Steps.cons (Step.brIf (condition := 1) (by decide) rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    apply Steps.cons (Step.globalSet (by simp [hglobal]))
    rw [setGlobal_zero_eq]
    exact Steps.single Step.finish
  · intro before kind after member
    fin_cases member <;> rfl

theorem emptyCleanupTrace_primary :
    ∀ kind ∈ emptyCleanupTrace, HostPrimaryMemoryKind kind := by
  intro kind member
  fin_cases member <;> trivial

def nonemptyCleanupTrace : List StepKind :=
  [.instruction (.block 0 0 [.localGet 0, .load32 20, .localTee 3, .eqz, .br_if 0,
      .localGet 2, .localGet 3, .const 1, .call 17]),
    .instruction (.localGet 0), .instruction (.load32 20), .instruction (.localTee 3),
    .instruction .eqz, .instruction (.br_if 0), .instruction (.localGet 2),
    .instruction (.localGet 3), .instruction (.const 1), .instruction (.call 17),
    .administrative .returnFromCall, .administrative .exitControl,
    .instruction (.block 0 0 [.localGet 0, .load32 8, .localTee 2, .eqz, .br_if 0,
      .localGet 1, .localGet 2, .const 1, .call 17]),
    .instruction (.localGet 0), .instruction (.load32 8), .instruction (.localTee 2),
    .instruction .eqz, .instruction (.br_if 0), .instruction (.localGet 1),
    .instruction (.localGet 2), .instruction (.const 1), .instruction (.call 17),
    .administrative .returnFromCall, .administrative .exitControl,
    .instruction (.localGet 0), .instruction (.const 32), .instruction .add,
    .instruction (.globalSet 0), .administrative .finish]

/-- Both nonempty vectors invoke the actual compiled deallocator before the
main wrapper restores its stack and returns normally. -/
theorem nonempty_main_cleanup_cost
    (store : MachineStore Universal.State) (inputPointer outputPointer inputCapacity outputCapacity : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (houtputCapacity : store.wasm.mem.read32 1048564 = outputCapacity)
    (hinputCapacity : store.wasm.mem.read32 1048552 = inputCapacity)
    (houtput : outputCapacity ≠ 0) (hinput : inputCapacity ≠ 0)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : 17 ≤ store.wasm.mem.pages) :
    CostedSteps CostedStdIO.work
      ⟨.running ⟨⟨[], [.i32 1048544, .i32 inputPointer, .i32 outputPointer, .i32 0], []⟩,
        func10.drop 24, 0, [], [], []⟩, store⟩ nonemptyCleanupTrace
      ⟨.done [], restoredMainStore store⟩ 29 := by
  apply Steps.with_unit_cost
  · simp only [nonemptyCleanupTrace, func10, List.drop]
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048568 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 20 = 1048564 from rfl, houtputCapacity]
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.eqz (result := 0) (by simp [houtput]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.call (fn := func14Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    apply Steps.cons (Step.returnFromCallFallthrough rfl)
    apply Steps.cons (Step.exitControl rfl)
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048556 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 8 = 1048552 from rfl, hinputCapacity]
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.eqz (result := 0) (by simp [hinput]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.call (fn := func14Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    apply Steps.cons (Step.returnFromCallFallthrough rfl)
    apply Steps.cons (Step.exitControl rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    apply Steps.cons (Step.globalSet (by simp [hglobal]))
    rw [setGlobal_zero_eq]
    exact Steps.single Step.finish
  · intro before kind after member
    fin_cases member <;> rfl

theorem nonemptyCleanupTrace_primary :
    ∀ kind ∈ nonemptyCleanupTrace, HostPrimaryMemoryKind kind := by
  intro kind member
  fin_cases member <;> trivial

def writeSetupTrace : List StepKind :=
  [.instruction (.localGet 0), .instruction (.load32 24), .instruction (.localTee 2),
    .instruction (.localGet 0), .instruction (.load32 28)]

def mainWriteLocals (inputPointer outputPointer : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[], [.i32 1048544, .i32 inputPointer, .i32 outputPointer, .i32 0], values⟩

theorem after_encode_to_write_cost
    (store : MachineStore Universal.State) (inputPointer outputPointer length : UInt32)
    (hpointer : store.wasm.mem.read32 1048568 = outputPointer)
    (hlength : store.wasm.mem.read32 1048572 = length)
    (hpages : 17 ≤ store.wasm.mem.pages) :
    CostedSteps CostedStdIO.work (afterEncodeConfig store inputPointer) writeSetupTrace
      ⟨.running ⟨mainWriteLocals inputPointer outputPointer [.i32 length, .i32 outputPointer],
        .call 11 :: func10.drop 24, 0, [], [], []⟩, store⟩ 5 := by
  apply Steps.with_unit_cost
  · simp only [afterEncodeConfig, writeSetupTrace, func10, List.drop]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048572 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 24 = 1048568 from rfl, hpointer]
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (by change 1048576 ≤ store.wasm.mem.pages * 65536; omega))
    rw [show (1048544 : UInt32) + 28 = 1048572 from rfl, hlength]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

theorem writeSetupTrace_primary :
    ∀ kind ∈ writeSetupTrace, HostPrimaryMemoryKind kind := by
  intro kind member
  fin_cases member <;> trivial

def completedWriteStore (store : MachineStore Universal.State)
    (outputPointer length : UInt32) : MachineStore Universal.State :=
  WriteResourceCost.writeAllResultStore store 1048544
    (store.wasm.mem.readBytes outputPointer.toNat length.toNat) length

/-- The complete nonempty main continuation writes the actual output bytes,
executes both deallocations, restores the stack and returns normally. -/
theorem nonempty_main_cost
    (store : MachineStore Universal.State) (inputPointer outputPointer inputCapacity outputCapacity length : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.HexStdio.module)
    (houtputCapacity : store.wasm.mem.read32 1048564 = outputCapacity)
    (hinputCapacity : store.wasm.mem.read32 1048552 = inputCapacity)
    (hpointer : store.wasm.mem.read32 1048568 = outputPointer)
    (hlength : store.wasm.mem.read32 1048572 = length)
    (houtput : outputCapacity ≠ 0) (hinput : inputCapacity ≠ 0) (hne : length ≠ 0)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hphysical : outputPointer.toNat + length.toNat ≤ store.wasm.mem.pages * 65536)
    (hpages : 17 ≤ store.wasm.mem.pages) :
    ∃ trace, CostedSteps CostedStdIO.work (afterEncodeConfig store inputPointer) trace
      ⟨.done [], restoredMainStore (completedWriteStore store outputPointer length)⟩
      (99 + length.toNat) ∧ (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  let written := completedWriteStore store outputPointer length
  have setup := after_encode_to_write_cost store inputPointer outputPointer length hpointer hlength hpages
  obtain ⟨writeTrace, writeRun, writeLabels⟩ :=
    WriteResourceCost.write_all_nonempty_cost store (mainWriteLocals inputPointer outputPointer)
      [] (func10.drop 24) 0 [] [] [] outputPointer length 1048544
      (store.wasm.mem.readBytes outputPointer.toNat length.toNat) hmodule hhost hglobal hne rfl
      hphysical (by change 1048544 ≤ store.wasm.mem.pages * 65536; omega) (by decide)
  have outputCapacity : written.wasm.mem.read32 1048564 = outputCapacity := by
    dsimp only [written, completedWriteStore, WriteResourceCost.writeAllResultStore,
      WriteResourceCost.writeAdapterResultStore, WriteResourceCost.universalWriteStore,
      WriteResourceCost.writeAllFrameStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write8_disjoint _ _ _ _ (by decide)]
    exact houtputCapacity
  have inputCapacity : written.wasm.mem.read32 1048552 = inputCapacity := by
    dsimp only [written, completedWriteStore, WriteResourceCost.writeAllResultStore,
      WriteResourceCost.writeAdapterResultStore, WriteResourceCost.universalWriteStore,
      WriteResourceCost.writeAllFrameStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write8_disjoint _ _ _ _ (by decide)]
    exact hinputCapacity
  have global : globalAt? written 0 = some (.i32 1048544) := by
    have hzero := (getElem?_eq_some_iff.mp (show store.wasm.globals.globals[0]? =
      some (.i32 1048544) by simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
    simp [written, completedWriteStore, WriteResourceCost.writeAllResultStore,
      WriteResourceCost.writeAdapterResultStore, WriteResourceCost.universalWriteStore,
      WriteResourceCost.writeAllFrameStore, globalAt?, canonicalGlobalIndex_zero, hzero]
  have cleanup := nonempty_main_cleanup_cost written inputPointer outputPointer _ _
    hmodule outputCapacity inputCapacity houtput hinput global hpages
  have run := (setup.trans writeRun).trans cleanup
  refine ⟨writeSetupTrace ++ writeTrace ++ nonemptyCleanupTrace, ?_, ?_⟩
  · convert run using 1; omega
  · intro kind member
    simp only [List.mem_append] at member
    rcases member with (setup | write) | cleanup
    · exact writeSetupTrace_primary kind setup
    · exact writeLabels kind write
    · exact nonemptyCleanupTrace_primary kind cleanup

/-- The zero-output path skips the host write and both deallocations, but
still charges every generated control and stack-restoration transition. -/
theorem empty_main_cost
    (store : MachineStore Universal.State) (inputPointer outputPointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (houtputCapacity : store.wasm.mem.read32 1048564 = 0)
    (hinputCapacity : store.wasm.mem.read32 1048552 = 0)
    (hpointer : store.wasm.mem.read32 1048568 = outputPointer)
    (hlength : store.wasm.mem.read32 1048572 = 0)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : 17 ≤ store.wasm.mem.pages) :
    ∃ trace, CostedSteps CostedStdIO.work (afterEncodeConfig store inputPointer) trace
      ⟨.done [], restoredMainStore (WriteResourceCost.writeAllEmptyResultStore store 1048544)⟩
      37 ∧ (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  let written := WriteResourceCost.writeAllEmptyResultStore store 1048544
  have setup := after_encode_to_write_cost store inputPointer outputPointer 0 hpointer hlength hpages
  obtain ⟨writeTrace, writeRun, writeLabels⟩ :=
    WriteResourceCost.write_all_empty_cost store (mainWriteLocals inputPointer outputPointer)
      [] (func10.drop 24) 0 [] [] [] outputPointer 1048544 hmodule hglobal
  have global : globalAt? written 0 = some (.i32 1048544) := by
    have hzero := (getElem?_eq_some_iff.mp (show store.wasm.globals.globals[0]? =
      some (.i32 1048544) by simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
    simp [written, WriteResourceCost.writeAllEmptyResultStore,
      WriteResourceCost.writeAllFrameStore, globalAt?, canonicalGlobalIndex_zero, hzero]
  have cleanup := empty_main_cleanup_cost written inputPointer outputPointer
    houtputCapacity hinputCapacity global hpages
  exact ⟨_, (setup.trans writeRun).trans cleanup, by
    intro kind member
    simp only [List.mem_append] at member
    rcases member with (setup | write) | cleanup
    · exact writeSetupTrace_primary kind setup
    · exact writeLabels kind write
    · exact emptyCleanupTrace_primary kind cleanup⟩

/-- From the empty reader's actual returned vector to normal export return.
All scalar setup, the sentinel iterator, empty writer and cleanup are included. -/
theorem empty_after_read_cost
    (store : MachineStore Universal.State) (inputPointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hcapacity : store.wasm.mem.read32 1048552 = 0)
    (hpointer : store.wasm.mem.read32 1048556 = inputPointer)
    (hlength : store.wasm.mem.read32 1048560 = 0)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : 17 ≤ store.wasm.mem.pages) :
    ∃ trace, CostedSteps CostedStdIO.work (encodeAfterReadConfig store) trace
      ⟨.done [], restoredMainStore (WriteResourceCost.writeAllEmptyResultStore
        (emptyEncodedStore store inputPointer) 1048544)⟩ 121 ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  let encoded := emptyEncodedStore store inputPointer
  have setup := after_read_to_encode_cost store inputPointer 0 hpointer hlength hpages
  obtain ⟨encodeTrace, encodeRun, encodeLabels⟩ :=
    empty_encoder_cost store inputPointer hmodule hglobal hpages
  have outputCapacity : encoded.wasm.mem.read32 1048564 = 0 := by
    change ((_ : Mem).write64 1048564 4294967296).read32 1048564 = 0
    rw [Mem.read32_write64_low]
    rfl
  have outputPointer : encoded.wasm.mem.read32 1048568 = 1 := by
    change ((_ : Mem).write64 1048564 4294967296).read32 (1048564 + 4) = 1
    rw [Mem.read32_write64_high _ _ _ (by decide)]
    rfl
  have outputLength : encoded.wasm.mem.read32 1048572 = 0 := by
    dsimp only [encoded, emptyEncodedStore, EncodeResourceCost.finishStore]
    rw [Mem.read32_write64_disjoint _ _ _ _ (by decide)]
    exact Mem.read32_write32_same _ _ _
  have inputCapacity : encoded.wasm.mem.read32 1048552 = 0 := by
    dsimp only [encoded, emptyEncodedStore, EncodeResourceCost.finishStore,
      EncodeResourceCost.iteratorResetStore, emptyEncoderStore, encodeAllocFrameStore]
    rw [Mem.read32_write64_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write64_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)]
    exact hcapacity
  have global : globalAt? encoded 0 = some (.i32 1048544) := by
    have hzero := (getElem?_eq_some_iff.mp (show store.wasm.globals.globals[0]? =
      some (.i32 1048544) by simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
    simp [encoded, emptyEncodedStore, EncodeResourceCost.finishStore,
      EncodeResourceCost.iteratorResetStore, emptyEncoderStore, encodeAllocFrameStore,
      globalAt?, canonicalGlobalIndex_zero, hzero]
  obtain ⟨mainTrace, mainRun, mainLabels⟩ := empty_main_cost encoded inputPointer 1 hmodule
    outputCapacity inputCapacity outputPointer outputLength global hpages
  exact ⟨_, (setup.trans encodeRun).trans mainRun, by
    intro kind member
    simp only [List.mem_append] at member
    rcases member with (setup | encoded) | main
    · exact afterReadTrace_primary kind setup
    · exact encodeLabels kind encoded
    · exact mainLabels kind main⟩

/-- The existing total functional theorem fixes the output of every actual
normal return. Its OOM branch is incompatible with the supplied normal trace. -/
theorem normal_return_correct (input : List UInt8)
    {trace : List StepKind} {values : List Value} {store : MachineStore Universal.State}
    (run : Steps (encodeInitialConfig input) trace ⟨.done values, store⟩) :
    values = [] ∧ store.wasm.host.stdio.output = Spec.encode input := by
  rcases Blueprint.encode_export_outcome input with normal | trapped
  · rcases normal with ⟨initial, hstart, execution⟩
    rw [encode_start_config] at hstart
    cases Option.some.inj hstart
    exact execution.toPartiallyMeets _ _ _ run
  · rcases trapped with ⟨initial, hstart, trapTrace, trapStore, execution, _⟩
    rw [encode_start_config] at hstart
    cases Option.some.inj hstart
    exact False.elim (steps_done_ne_trapped run execution)

end Project.HexEncodeStdio.ExportResourceCost
