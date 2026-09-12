import Project.Mergesort.InputCost
import Project.Mergesort.TotalProof
import Project.Mergesort.SortCostRecurrence

set_option maxRecDepth 1048576

/-! Actual numerical costs at the driver's read/decode dispatch boundaries. -/
namespace Project.Mergesort.DriverDispatchCost

open Wasm Wasm.SmallStep Project.Mergesort.DriverProof
open Project.Mergesort.Representations

private def alignedBody : Program :=
  [.localGet 6, .const 2147483644, .and, .localTee 7, .br_if 0,
    .const 1, .localSet 5, .const 0, .localSet 1, .br 4]

private theorem decode_shape : func3DecodeAllocationBody =
    func3CompletedLengthGuard ++ [.block 0 0 alignedBody] ++ func3AllocationBody := rfl

def completedCode : Program :=
  func3CompletedPtrReload ++ [.block 0 0 func3ScratchOuterBody] ++ func3ScratchAllocationPanic

def completedControls : List ControlFrame :=
  [func3ReadAndDispatchFrame, func3EmptyMiddleFrame func3MiddleBody,
    func3CleanupOuterFrame func3DriverBody]

/-- Reload the actual completed pointer, enter all three generated error
blocks, and discharge the aligned nonempty length guards. No allocation has
executed yet; the exact allocation body and its six frames remain pending. -/
theorem completed_nonempty_cost (store : MachineStore α) (inputPtr : UInt32)
    (n : Nat) (calls : List CallFrame) (hp : 0<n) (hb : 4*n<2147483648)
    (hheader : store.wasm.mem.read32 (driverBase+4)=inputPtr)
    (hphysical : driverBase.toNat+4+4 ≤ store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3AppendLocals inputPtr 0 (UInt32.ofNat (4*n)) 4 0 0 0 0 0 0 [],
        completedCode, 0, [], completedControls, calls⟩, store⟩ trace
      ⟨.running ⟨func3AppendLocals inputPtr 0 (UInt32.ofNat (4*n)) 4 inputPtr 0
          (UInt32.ofNat (4*n)) 0 0 0 [],
        func3AllocationBody, 0, [], func3ScratchSuccessControls, calls⟩, store⟩ 16 := by
  have hsize : 4*n<UInt32.size := by norm_num [UInt32.size]; omega
  have hlow : UInt32.ofNat (4*n) &&& (3:UInt32)=0 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_and, UInt32.toNat_ofNat_of_lt' hsize]
    change (4*n) &&& 3=0
    rw [show (3:Nat)=2^2-1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hmask := align4_signedMask_eq (4*n) hb (by omega)
  have hnz : UInt32.ofNat (4*n)≠0 := by
    intro h
    have hnat := congrArg UInt32.toNat h
    rw [UInt32.toNat_ofNat_of_lt' hsize] at hnat
    change 4*n=0 at hnat
    omega
  let trace : List StepKind := [.instruction (.localGet 0), .instruction (.load32 4), .instruction (.localSet 4),
    .instruction (.block 0 0 func3ScratchOuterBody), .instruction (.block 0 0 func3ValuesOuterBody),
    .instruction (.block 0 0 func3DecodeAllocationBody), .instruction (.localGet 6),
    .instruction (.const 3), .instruction .and, .instruction (.br_if 0),
    .instruction (.block 0 0 alignedBody), .instruction (.localGet 6),
    .instruction (.const 2147483644), .instruction .and, .instruction (.localTee 7),
    .instruction (.br_if 0)]
  refine ⟨trace, ?_⟩
  apply Steps.with_unit_cost
  · unfold trace completedCode func3CompletedPtrReload
    simp only [List.cons_append, List.nil_append]
    wasm_steps [(.localGet rfl), (.load32 rfl (by simpa using hphysical))]
    rw [hheader]
    wasm_steps [(.localSet rfl), .block]
    unfold func3ScratchOuterBody
    simp only [List.cons_append, List.nil_append]
    wasm_steps [.block]
    unfold func3ValuesOuterBody
    simp only [List.cons_append, List.nil_append]
    wasm_steps [.block]
    rw [decode_shape]
    unfold func3CompletedLengthGuard
    simp only [List.cons_append, List.nil_append]
    wasm_steps [(.localGet rfl), .const, .and]
    rw [hlow]
    wasm_steps [.brIfZero, .block]
    unfold alignedBody
    wasm_steps [(.localGet rfl), .const, .and]
    rw [hmask]
    wasm_steps [(.localTee rfl)]
    exact Steps.single (.brIf hnz rfl)
  · intro before kind after member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Empty initial input executes the actual read shim and the generated empty
arm. It leaves the empty-driver setup pending after seventeen transitions. -/
theorem initial_empty_cost (store : MachineStore Universal.State) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule=Project.Mergesort.module)
    (hhost : store.runtime.currentHost=Universal.envFor Project.Mergesort.module)
    (hempty : store.wasm.host.stdio.input=[])
    (hphysical : (driverBase+12).toNat ≤ store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨func3InitializedLocals,
        .block 0 0 func3InitialReadBody :: func3AfterInitialRead completedCode,
        0, [], completedControls, calls⟩, store⟩ trace
      ⟨.running ⟨func3EmptyLocals, func3EmptyAfterReadSetup, 0, [],
        [func3EmptyMiddleFrame func3MiddleBody, func3CleanupOuterFrame func3DriverBody], calls⟩,
        InputCost.readResult store 256 (driverBase+12)⟩ 17 := by
  have hc : InputCost.readCount store 256=0 := (InputCost.readCount_zero_iff store).2 hempty
  have enter : CostedSteps CostedStdIO.work
      ⟨.running ⟨func3InitializedLocals,
        .block 0 0 func3InitialReadBody :: func3AfterInitialRead completedCode,
        0, [], completedControls, calls⟩, store⟩
      [.instruction (.block 0 0 func3InitialReadBody)]
      ⟨.running ⟨func3InitializedLocals, func3InitialReadBody, 0, [],
        func3InitialReadFrame completedCode :: completedControls, calls⟩, store⟩ 1 :=
    CostedSteps.single .block
  obtain ⟨tr, _, read⟩ := InputCost.read_chunk_cost store func3InitializedLocals []
    ([.localTee 3, .br_if 0] ++ func3EmptyInputSuffix) 0 []
    (func3InitialReadFrame completedCode :: completedControls) calls rfl hmodule hhost
    (by rw [hc]; simpa using hphysical)
  rw [hc] at read
  have finish : CostedSteps CostedStdIO.work
      ⟨.running ⟨{ func3InitializedLocals with values := [.i32 0] },
        [.localTee 3, .br_if 0] ++ func3EmptyInputSuffix, 0, [],
        func3InitialReadFrame completedCode :: completedControls, calls⟩,
        InputCost.readResult store 256 (driverBase+12)⟩
      [.instruction (.localTee 3), .instruction (.br_if 0),
        .instruction (.const 1), .instruction (.localSet 4),
        .instruction (.const 1), .instruction (.localSet 5), .instruction (.br 1)]
      ⟨.running ⟨func3EmptyLocals, func3EmptyAfterReadSetup, 0, [],
        [func3EmptyMiddleFrame func3MiddleBody, func3CleanupOuterFrame func3DriverBody], calls⟩,
        InputCost.readResult store 256 (driverBase+12)⟩ 7 := by
    apply Steps.with_unit_cost
    · unfold func3EmptyInputSuffix
      simp only [List.cons_append, List.nil_append]
      wasm_steps [(.localTee rfl), .brIfZero, .const, (.localSet rfl), .const, (.localSet rfl)]
      exact Steps.single (.br rfl)
    · intro before kind after member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  exact ⟨_, (enter.trans read).trans finish⟩

private def prologue : Program :=
  [.globalGet 0, .const 272, .sub, .localTee 0, .globalSet 0,
    .const 0, .localSet 1, .localGet 0, .const 0, .store32 8,
    .localGet 0, .constI64 4294967296, .store64 0,
    .localGet 0, .const 12, .add, .const 0, .const 256,
    .memoryFill, .const 4, .localSet 2]

private theorem prologue_shape : Project.Mergesort.func3 = prologue ++ func3AfterInit := rfl

private def beforeFillLocals : Locals :=
  func3AppendLocals 0 0 0 0 0 0 0 0 0 0 []

def initializedStore (store : MachineStore α) : MachineStore α :=
  { store with wasm := { store.wasm with
    globals := { globals := store.wasm.globals.globals.set 0 (.i32 driverBase) },
    mem := ((store.wasm.mem.write32 (driverBase+8) 0).write64 driverBase 4294967296).fill
      (driverBase+12).toNat 256 0 } }

/-- The exact generated prologue executes twenty-one transitions and charges
all 256 bytes initialized by memory.fill, for 277 total work. -/
theorem initialize_cost (store : MachineStore α) (calls : List CallFrame)
    (hglobal : globalAt? store 0=some (.i32 entryStackTop))
    (hphysical : driverBase.toNat+268 ≤ store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, CostedSteps (byteWork hostBytes)
      ⟨.running ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
        0, [], [], calls⟩, store⟩ trace
      ⟨.running ⟨func3InitializedLocals, func3AfterInit, 0, [], [], calls⟩,
        initializedStore store⟩ 277 := by
  let prefixStore : MachineStore α := { store with wasm := { store.wasm with
    globals := { globals := store.wasm.globals.globals.set 0 (.i32 driverBase) },
    mem := (store.wasm.mem.write32 (driverBase+8) 0).write64 driverBase 4294967296 } }
  have pre : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
        0, [], [], calls⟩, store⟩
      ((prologue.take 18).map StepKind.instruction)
      ⟨.running ⟨{ beforeFillLocals with values := [.i32 256, .i32 0, .i32 (driverBase+12)] },
        [.memoryFill, .const 4, .localSet 2] ++ func3AfterInit, 0, [], [], calls⟩,
        prefixStore⟩ 18 := by
    apply Steps.with_unit_cost
    · rw [prologue_shape]
      unfold prologue
      simp only [List.take, List.map, List.cons_append, List.nil_append]
      wasm_steps [(.globalGet hglobal), .const, .sub]
      rw [show entryStackTop-272=driverBase by decide]
      wasm_steps [(.localTee rfl), (.globalSet (by rw [hglobal]; rfl)), .const,
        (.localSet rfl), (.localGet rfl), .const,
        (.store32 rfl (by change driverBase.toNat+8+4≤store.wasm.mem.pages*65536; omega)),
        (.localGet rfl), .constI64,
        (.store64 rfl (by change driverBase.toNat+0+8≤store.wasm.mem.pages*65536; omega)),
        (.localGet rfl), .const, .add]
      rw [show (12:UInt32)+driverBase=driverBase+12 by decide]
      wasm_steps [.const]
      exact Steps.single .const
    · intro before kind after member
      simp only [prologue, List.take, List.map, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have fill : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨{ beforeFillLocals with values := [.i32 256, .i32 0, .i32 (driverBase+12)] },
        [.memoryFill, .const 4, .localSet 2] ++ func3AfterInit, 0, [], [], calls⟩,
        prefixStore⟩ [.instruction .memoryFill]
      ⟨.running ⟨beforeFillLocals, [.const 4, .localSet 2] ++ func3AfterInit,
        0, [], [], calls⟩, initializedStore store⟩ 257 := by
    exact CostedSteps.single (.memoryFill32 (by
      change (driverBase+12).toNat+256≤store.wasm.mem.pages*65536
      have ha : (driverBase+12).toNat=driverBase.toNat+12 := by decide
      rw [ha]; omega))
  have finish : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨beforeFillLocals, [.const 4, .localSet 2] ++ func3AfterInit,
        0, [], [], calls⟩, initializedStore store⟩
      [.instruction (.const 4), .instruction (.localSet 2)]
      ⟨.running ⟨func3InitializedLocals, func3AfterInit, 0, [], [], calls⟩, initializedStore store⟩ 2 := by
    apply Steps.with_unit_cost
    · simp only [List.cons_append, List.nil_append]
      wasm_steps [.const]
      exact Steps.single (.localSet (locals' := { func3InitializedLocals with values := [.i32 4] }) rfl)
    · intro before kind after member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
  exact ⟨_, (pre.trans fill).trans finish⟩

/-- Three actual enclosing blocks connect initialized locals to the common
initial-read entry, with the precise caller frames used by both input arms. -/
theorem enter_read_cost (store : MachineStore α) (calls : List CallFrame)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3InitializedLocals, func3AfterInit, 0, [], [], calls⟩, store⟩
      [.instruction (.block 0 0 func3DriverBody), .instruction (.block 0 0 func3MiddleBody),
        .instruction (.block 0 0 func3ReadAndDispatchBody)]
      ⟨.running ⟨func3InitializedLocals,
        .block 0 0 func3InitialReadBody :: func3AfterInitialRead completedCode,
        0, [], completedControls, calls⟩, store⟩ 3 := by
  apply Steps.with_unit_cost
  · rw [func3_after_init_exact]
    simp only [List.cons_append, List.nil_append]
    wasm_steps [.block]
    unfold func3DriverBody
    simp only [List.cons_append, List.nil_append]
    wasm_steps [.block]
    unfold func3MiddleBody
    simp only [List.cons_append, List.nil_append]
    exact Steps.single .block
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- The concrete initialized store selected by the named export frontend. -/
abbrev canonicalInitializedStore (input : List UInt32) : MachineStore Universal.State :=
  initializedStore (TotalProof.exportConfig input).store

/-- Exact initial metadata. These facts follow from the generated initial
store and the actual prologue writes, independently of any execution premise. -/
theorem canonical_initialized_metadata (input : List UInt32) :
    let store := canonicalInitializedStore input
    store.wasm.mem.pages = 17 ∧
    store.wasm.mem.read32 driverBase = 0 ∧
    store.wasm.mem.read32 (driverBase+4) = 1 ∧
    store.wasm.mem.read32 (driverBase+8) = 0 ∧
    store.wasm.mem.read32 allocatorCursor = 0 ∧
    globalAt? store 0 = some (.i32 driverBase) ∧
    store.runtime.currentModule = Project.Mergesort.module ∧
    store.runtime.currentHost = Universal.envFor Project.Mergesort.module ∧
    store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap ∧
    store.wasm.host.stdio.input = serialize input ∧
    store.wasm.host.stdio.output = [] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl⟩
  · exact TotalProof.exportConfig_pages input
  · change (((((Project.Mergesort.module.initialStore : Store Universal.State).mem).write32
        (driverBase+8) 0).write64 driverBase 4294967296).fill
        (driverBase+12).toNat 256 0).read32 driverBase=0
    decide
  · change (((((Project.Mergesort.module.initialStore : Store Universal.State).mem).write32
        (driverBase+8) 0).write64 driverBase 4294967296).fill
        (driverBase+12).toNat 256 0).read32 (driverBase+4)=1
    decide
  · change (((((Project.Mergesort.module.initialStore : Store Universal.State).mem).write32
        (driverBase+8) 0).write64 driverBase 4294967296).fill
        (driverBase+12).toNat 256 0).read32 (driverBase+8)=0
    decide
  · change (((((Project.Mergesort.module.initialStore : Store Universal.State).mem).write32
        (driverBase+8) 0).write64 driverBase 4294967296).fill
        (driverBase+12).toNat 256 0).read32 allocatorCursor=0
    decide
  · rfl
  · rfl

/-- Actual named-export body entry through prologue and the three enclosing
blocks, ending precisely before the shared initial read. -/
theorem export_to_read_cost (input : List UInt32) :
    ∃ trace, CostedSteps CostedStdIO.work (TotalProof.exportConfig input) trace
      ⟨.running ⟨func3InitializedLocals,
        .block 0 0 func3InitialReadBody :: func3AfterInitialRead completedCode,
        0, [], completedControls, []⟩, canonicalInitializedStore input⟩ 280 := by
  obtain ⟨trace, run⟩ := initialize_cost (TotalProof.exportConfig input).store []
    (by rfl) (by rw [TotalProof.exportConfig_pages]; decide) CostedStdIO.hostBytes
  exact ⟨_, run.trans (enter_read_cost _ [] CostedStdIO.hostBytes)⟩

private def valuesDeallocBody : Program :=
  [.localGet 1,.eqz,.br_if 0,.localGet 2,.localGet 1,.const 2,.shl,.const 4,.call 10]

private def scratchDeallocBody : Program :=
  [.localGet 5,.br_if 0,.localGet 8,.localGet 10,.const 4,.call 10]

private def inputDeallocTail : Program :=
  [.localGet 0,.load32 0,.localTee 3,.eqz,.br_if 0,.localGet 4,.localGet 3,.const 1,.call 10]

private theorem cleanup_shape : func3NonemptyCleanup =
    [.block 0 0 valuesDeallocBody,.block 0 0 scratchDeallocBody]++inputDeallocTail := rfl

/-- Exact empty-arm locals after its post-read scalar setup. -/
def emptyReadyLocals : Locals :=
  func3AppendLocals 0 0 0 4 1 1 0 4 0 0 []

/-- Only the stack-pointer global changes during the empty arm's cleanup. -/
def restoredStore (store : MachineStore α) : MachineStore α :=
  { store with wasm := { store.wasm with globals :=
    { globals := store.wasm.globals.globals.set 0 (.i32 entryStackTop) } } }

/-- The complete generated empty continuation: scalar setup, actual zero-word
sort call, output and retirement skips, and stack restoration. -/
theorem finish_empty_cost (store : MachineStore α) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hheader : store.wasm.mem.read32 driverBase = 0)
    (hphysical : driverBase.toNat+4 ≤ store.wasm.mem.pages*65536)
    (hglobal : (globalAt? store 0).isSome = true)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3EmptyLocals, func3EmptyAfterReadSetup, 0, [],
        [func3EmptyMiddleFrame func3MiddleBody,func3CleanupOuterFrame func3DriverBody],calls⟩,
        store⟩ trace
      ⟨.running ⟨emptyReadyLocals,[],0,[],[],calls⟩,restoredStore store⟩ 41 := by
  let afterSort := [.block 0 0 func3OutputBlockBody]++func3NonemptyCleanup
  have setup : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3EmptyLocals, func3EmptyAfterReadSetup, 0, [],
        [func3EmptyMiddleFrame func3MiddleBody,func3CleanupOuterFrame func3DriverBody],calls⟩,
        store⟩
      [.instruction (.const 0),.instruction (.localSet 10),
        .instruction (.const 0),.instruction (.localSet 9),
        .instruction (.const 4),.instruction (.localSet 8),.administrative .exitControl,
        .instruction (.localGet 2),.instruction (.localGet 9),
        .instruction (.localGet 8),.instruction (.localGet 9)]
      ⟨.running ⟨{emptyReadyLocals with values := [.i32 0,.i32 4,.i32 0,.i32 4]},
        .call 5 :: afterSort,0,[],[func3CleanupOuterFrame func3DriverBody],calls⟩,store⟩ 11 := by
    apply Steps.with_unit_cost
    · unfold func3EmptyAfterReadSetup
      wasm_steps [.const,(.localSet rfl),.const,(.localSet rfl),.const,(.localSet rfl),
        (.exitControl rfl)]
      wasm_steps [(.localGet rfl),(.localGet rfl),(.localGet rfl)]
      exact Steps.single (.localGet rfl)
    · intro before kind after member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  obtain ⟨sortTrace,_,sortRun⟩ := SortCostRecurrence.sort_base_call_cost store 4 4 0 0
    emptyReadyLocals [] afterSort 0 [] [func3CleanupOuterFrame func3DriverBody] calls
    hmodule (by decide) hostBytes
  have tail : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨emptyReadyLocals,afterSort,0,[],[func3CleanupOuterFrame func3DriverBody],calls⟩,store⟩
      [.instruction (.block 0 0 func3OutputBlockBody),.instruction (.localGet 9),
        .instruction .eqz,.instruction (.br_if 0),
        .instruction (.block 0 0 valuesDeallocBody),.instruction (.localGet 1),
        .instruction .eqz,.instruction (.br_if 0),
        .instruction (.block 0 0 scratchDeallocBody),.instruction (.localGet 5),
        .instruction (.br_if 0),.instruction (.localGet 0),.instruction (.load32 0),
        .instruction (.localTee 3),.instruction .eqz,.instruction (.br_if 0),
        .instruction (.localGet 0),.instruction (.const 272),.instruction .add,
        .instruction (.globalSet 0)]
      ⟨.running ⟨emptyReadyLocals,[],0,[],[],calls⟩,restoredStore store⟩ 20 := by
    apply Steps.with_unit_cost
    · unfold afterSort
      simp only [List.cons_append,List.nil_append]
      wasm_steps [.block]
      unfold func3OutputBlockBody
      wasm_steps [(.localGet rfl),(.eqz (result := 1) (by rfl)),(.brIf (by decide) rfl)]
      rw [cleanup_shape]
      wasm_steps [.block]
      unfold valuesDeallocBody
      wasm_steps [(.localGet rfl),(.eqz (result := 1) (by rfl)),(.brIf (by decide) rfl),.block]
      unfold scratchDeallocBody
      wasm_steps [(.localGet rfl),(.brIf (by decide) rfl)]
      unfold inputDeallocTail
      wasm_steps [(.localGet rfl),(.load32 rfl hphysical)]
      rw [UInt32.add_zero,hheader]
      wasm_steps [(.localTee rfl),(.eqz (result := 1) (by rfl)),(.brIf (by decide) rfl)]
      wasm_steps [(.localGet rfl),.const,.add]
      convert Steps.single (Step.globalSet hglobal) using 1
      simp only [setGlobal_zero_eq]
      rfl
    · intro before kind after member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
        rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  exact ⟨_,(setup.trans sortRun).trans tail⟩

/-- An actual EOF read preserves the entire store, including other host fields. -/
theorem readResult_empty (store : MachineStore Universal.State) (requested pointer : UInt32)
    (hinput : store.wasm.host.stdio.input=[]) :
    InputCost.readResult store requested pointer=store := by
  simp only [InputCost.readResult,CostedStdIO.readStore,hinput,List.take_nil,
    List.length_nil,List.drop_nil,Mem.writeBytes_nil]
  rw [← hinput]

/-- The complete canonical empty export body has exactly 338 work units.
The terminal finish transition remains explicit for the export-level wrapper. -/
theorem empty_export_body_cost :
    ∃ trace, CostedSteps CostedStdIO.work (TotalProof.exportConfig []) trace
      ⟨.running ⟨emptyReadyLocals,[],0,[],[],[]⟩,
        restoredStore (canonicalInitializedStore [])⟩ 338 := by
  obtain ⟨entryTrace,entryRun⟩ := export_to_read_cost []
  rcases canonical_initialized_metadata [] with
    ⟨hpages,hcapacity,_hpointer,_hlength,_hcursor,hglobal,hmodule,hhost,_hcap,hinput,_houtput⟩
  obtain ⟨readTrace,readRun⟩ := initial_empty_cost (canonicalInitializedStore []) []
    hmodule hhost hinput (by rw [hpages]; decide)
  rw [readResult_empty _ _ _ hinput] at readRun
  obtain ⟨finishTrace,finishRun⟩ := finish_empty_cost (canonicalInitializedStore []) []
    hmodule hcapacity (by rw [hpages]; decide) (by rw [hglobal]; rfl) CostedStdIO.hostBytes
  exact ⟨_,(entryRun.trans readRun).trans finishRun⟩

end Project.Mergesort.DriverDispatchCost
