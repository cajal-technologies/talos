import Project.Mergesort.AllocatorExecution

/-!
# Actual execution of the compiled zeroed allocator

Local `func9` (absolute call 12) repeats the bump arithmetic, optionally grows
physical memory, commits the cursor, fills the allocated bytes with zero, and
returns to its original caller. These certificates retain that exact generated
control flow and charge both growth and zero filling in the byte-work model.
-/

namespace Project.Mergesort.ZeroedAllocatorExecution

open Wasm Wasm.SmallStep
open Project.Mergesort.Representations Project.Mergesort.MemoryBounds

private def arithmeticPrefix : Program :=
  [.localGet 1, .const 0xFFFFFFFF, .add, .localTee 2,
    .const 0, .load32 allocatorCursor, .localTee 3,
    .const heapBase, .localGet 3, .select, .add, .localTee 3,
    .localGet 2, .ltU, .br_if 0,
    .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 1,
    .localGet 0, .add, .localTee 2,
    .localGet 1, .ltU, .br_if 0,
    .localGet 2, .const 0, .ltS, .br_if 0]

private def growthBody : Program :=
  [.localGet 2, .const 65535, .add, .const 16, .shrU,
    .localTee 3, .memorySize, .localTee 4, .leU, .br_if 0,
    .localGet 3, .localGet 4, .sub, .memoryGrow,
    .const 0xFFFFFFFF, .eq, .br_if 1]

private def zeroBody : Program :=
  [.localGet 1, .eqz, .br_if 0, .localGet 0, .eqz, .br_if 0,
    .localGet 1, .const 0, .localGet 0, .memoryFill]

private def commitTail : Program :=
  [.const 0, .localGet 2, .store32 allocatorCursor,
    .block 0 0 zeroBody, .localGet 1, .ret]

private def outerBody : Program :=
  arithmeticPrefix ++ [.block 0 0 growthBody] ++ commitTail

/-- The symbolic trace below executes the actual WAT-decoded body. -/
theorem compiled_body :
    func9Def.body = [.block 0 0 outerBody, .call 9, .unreachable] := rfl

private def outerFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := outerBody, continuation := [.call 9, .unreachable], belowStack := [] }

private def growthFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := growthBody, continuation := commitTail, belowStack := [] }

private def zeroFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := zeroBody, continuation := [.localGet 1, .ret], belowStack := [] }

private def allocatorLocals (size base finish required current : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[.i32 size, .i32 base], [.i32 finish, .i32 required, .i32 current], values⟩

/-- Exact committed and zero-filled final store. -/
def finalStore {α : Type} (store : MachineStore α) (size base finish : UInt32) :
    MachineStore α :=
  { store with wasm := { store.wasm with mem := ((AllocatorExecution.grownMemory store.wasm.mem finish).write32 allocatorCursor finish).fill base.toNat size.toNat 0 } }

private def growthTrace (memory : Mem) (finish : UInt32) : List StepKind :=
  [.instruction (.block 0 0 growthBody)] ++
  (growthBody.take 10).map StepKind.instruction ++
  if memory.pages < (allocatorRequiredPages finish).toNat then
    (growthBody.drop 10).map StepKind.instruction ++ [.administrative .exitControl]
  else []

private theorem growth_steps
    {α : Type} (store : MachineStore α) (size base finish auxiliary : UInt32)
    (calls : List CallFrame)
    (h32 : store.runtime.currentModule.memIs64 = false)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages < UInt32.size)
    (hfinish : finish.toNat < 2147483648) :
    Steps
      ⟨.running ⟨allocatorLocals size base finish auxiliary 0,
        [.block 0 0 growthBody] ++ commitTail, 1, [], [outerFrame], calls⟩, store⟩
      (growthTrace store.wasm.mem finish)
      ⟨.running ⟨allocatorLocals size base finish (allocatorRequiredPages finish)
          store.wasm.mem.pages.toUInt32,
        commitTail, 1, [], [outerFrame], calls⟩,
        { store with wasm := { store.wasm with mem := AllocatorExecution.grownMemory store.wasm.mem finish } }⟩ := by
  simp only [growthTrace, growthBody, allocatorLocals,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
  apply Steps.cons Step.block
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  rw [show (65535 : UInt32) + finish = finish + 65535 from UInt32.add_comm _ _]
  apply Steps.cons Step.const
  apply Steps.cons Step.shrU
  change Steps
    ⟨.running ⟨allocatorLocals size base finish auxiliary 0
      [.i32 (allocatorRequiredPages finish)],
      .localTee 3 :: .memorySize :: .localTee 4 :: .leU :: .br_if 0 ::
        growthBody.drop 10, 1, [], [growthFrame, outerFrame], calls⟩, store⟩ _ _
  apply Steps.cons (Step.localTee (by rfl))
  apply Steps.cons Step.memorySize
  simp only [sizeValue, h32, Bool.false_eq_true, ↓reduceIte]
  apply Steps.cons (Step.localTee (by rfl))
  have hpagesNat : store.wasm.mem.pages.toUInt32.toNat = store.wasm.mem.pages :=
    UInt32.toNat_ofNat_of_lt' hpages
  by_cases hneed : store.wasm.mem.pages < (allocatorRequiredPages finish).toNat
  · have hnotFits : ¬ allocatorRequiredPages finish ≤ store.wasm.mem.pages.toUInt32 := by
      rw [UInt32.le_iff_toNat_le_toNat, hpagesNat]; omega
    simp only [if_pos hneed]
    apply Steps.cons (Step.leU (result := 0) (by simp [hnotFits]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons Step.sub
    have hg := allocatorMemoryGrow_succeeds store.wasm.mem finish hfinish hneed
    rw [← hcap] at hg
    apply Steps.cons (by simpa only [setMemory_eq] using Step.memoryGrowSuccess hg)
    apply Steps.cons Step.const
    have hnotFailure : store.wasm.mem.pages.toUInt32 ≠ (0xFFFFFFFF : UInt32) := by
      intro equality
      have bad := congrArg UInt32.toNat equality
      change store.wasm.mem.pages.toUInt32.toNat = 4294967295 at bad
      rw [hpagesNat] at bad
      have := allocatorRequiredPages_le_signedLimit finish hfinish
      omega
    apply Steps.cons (Step.eq (result := 0) (by simp [hnotFailure]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.exitControl (by rfl))
    simp only [AllocatorExecution.grownMemory, max_eq_right (Nat.le_of_lt hneed),
      growthFrame, List.set, List.length, Nat.reduceAdd,
      Nat.reduceSub, List.take_zero, List.nil_append]
    exact Steps.refl _
  · have hfits : allocatorRequiredPages finish ≤ store.wasm.mem.pages.toUInt32 := by
      rw [UInt32.le_iff_toNat_le_toNat, hpagesNat]; omega
    simp only [if_neg hneed]
    apply Steps.cons (Step.leU (result := 1) (by simp [hfits]))
    apply Steps.cons (Step.brIf (by decide) (by rfl))
    simp only [AllocatorExecution.grownMemory, max_eq_left (Nat.le_of_not_gt hneed),
      growthFrame, List.set, List.length, Nat.reduceAdd,
      Nat.reduceSub, List.take_zero, List.nil_append]
    exact Steps.refl _

private theorem arithmetic_prefix_steps
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (calls : List CallFrame)
    (halignment : layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Steps
      ⟨.running ⟨allocatorLocals (UInt32.ofNat layout.size)
          (UInt32.ofNat layout.alignment) 0 0 0,
        func9Def.body, 1, [], [], calls⟩, store⟩
      (([Instruction.block 0 0 outerBody] ++ arithmeticPrefix).map
        StepKind.instruction)
      ⟨.running ⟨allocatorLocals (UInt32.ofNat layout.size) base finish
          (UInt32.ofNat (frontier + (layout.alignment - 1))) 0,
        [.block 0 0 growthBody] ++ commitTail, 1, [], [outerFrame], calls⟩, store⟩ := by
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  dsimp only at hfacts
  obtain ⟨hsum, hbase, hend, hsigned, hfinishNat⟩ := hfacts
  have hfrontier : frontier < UInt32.size := by omega
  have hpadSmall : layout.alignment - 1 ≤ 3 := by
    omega
  have hpadBound : layout.alignment - 1 < UInt32.size := by
    exact Nat.lt_of_le_of_lt hpadSmall (by decide)
  have hsizeBound : layout.size < UInt32.size := by omega
  have hsizeNat : (UInt32.ofNat layout.size).toNat = layout.size :=
    UInt32.toNat_ofNat_of_lt' hsizeBound
  have hpadWord : (0xFFFFFFFF : UInt32) + UInt32.ofNat layout.alignment =
      UInt32.ofNat (layout.alignment - 1) := by
    rw [halignment]; decide
  have hsumWord : UInt32.ofNat frontier + UInt32.ofNat (layout.alignment - 1) =
      UInt32.ofNat (frontier + (layout.alignment - 1)) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hfrontier,
      UInt32.toNat_ofNat_of_lt' hpadBound, UInt32.toNat_ofNat_of_lt' hsum,
      Nat.mod_eq_of_lt hsum]
  have hsumNotLt : ¬ UInt32.ofNat (frontier + (layout.alignment - 1)) <
      UInt32.ofNat (layout.alignment - 1) := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hsum,
      UInt32.toNat_ofNat_of_lt' hpadBound]
    omega
  have hfinishWord : UInt32.ofNat layout.size + base = finish := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hsizeNat, Nat.add_comm layout.size base.toNat,
      Nat.mod_eq_of_lt hend, hfinishNat]
  have hbaseLe : base ≤ finish := by
    rw [UInt32.le_iff_toNat_le_toNat, hfinishNat]
    omega
  have hnonnegative : ¬ finish.toInt32 < (0 : UInt32).toInt32 := by
    simp only [UInt32.toInt32, LT.lt, Int32.lt, Int32.toBitVec]
    rw [BitVec.slt_iff_toInt_lt]
    simp only [BitVec.toInt, Nat.reducePow]
    change ¬ (if 2 * finish.toNat < 4294967296 then
      (finish.toNat : Int) else (finish.toNat : Int) - 4294967296) < 0
    omega
  rw [compiled_body]
  simp only [List.map_cons,
    List.cons_append, List.nil_append, allocatorLocals]
  apply Steps.cons Step.block
  simp only [outerBody, arithmeticPrefix, List.cons_append, List.nil_append]
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  rw [hpadWord]
  apply Steps.cons (Step.localTee (by rfl))
  apply Steps.cons Step.const
  apply Steps.cons (Step.load32 (logicalAddress := 0) (physicalAddress := 0)
    (by rfl) (by simpa only [Nat.zero_add] using hcursorBounds))
  rw [UInt32.zero_add, hcursor]
  apply Steps.cons (Step.localTee (by rfl))
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (Step.select (selected := .i32 (UInt32.ofNat frontier)) (by
    simpa only [apply_ite] using (congrArg Value.i32 heffective).symm))
  apply Steps.cons Step.add
  rw [hsumWord]
  apply Steps.cons (Step.localTee (by rfl))
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (Step.ltU (result := 0) (by simp only [if_neg hsumNotLt]))
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.sub
  apply Steps.cons Step.and
  rw [← hbase]
  apply Steps.cons (Step.localTee (by rfl))
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.add
  rw [hfinishWord]
  apply Steps.cons (Step.localTee (by rfl))
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (Step.ltU (result := 0) (by simp [UInt32.not_lt.mpr hbaseLe]))
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.const
  apply Steps.cons (Step.ltS (result := 0) (by rw [if_neg hnonnegative]))
  apply Steps.cons Step.brIfZero
  simp only [outerFrame, outerBody,
    List.set, List.length, Nat.reduceAdd, Nat.reduceSub,
    List.drop_zero]
  exact Steps.refl _


private def tailPrefix : Program :=
  [.const 0, .localGet 2, .store32 allocatorCursor,
    .block 0 0 zeroBody] ++ zeroBody.take 9

private def tailTrace : List StepKind :=
  tailPrefix.map StepKind.instruction ++
    [.instruction .memoryFill, .administrative .exitControl, .instruction (.localGet 1)]

private theorem commit_zero_cost
    {α : Type} (store : MachineStore α) (size base finish required current : UInt32)
    (calls : List CallFrame)
    (hbase : base ≠ 0) (hsize : size ≠ 0)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hfillBounds : base.toNat + size.toNat ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨allocatorLocals size base finish required current,
        commitTail, 1, [], [outerFrame], calls⟩, store⟩ tailTrace
      ⟨.running ⟨allocatorLocals size base finish required current [.i32 base],
        [.ret], 1, [], [outerFrame], calls⟩,
        { store with wasm := { store.wasm with mem := (store.wasm.mem.write32 allocatorCursor finish).fill base.toNat size.toNat 0 } }⟩
      (16 + size.toNat) := by
  let committed : MachineStore α :=
    { store with wasm := { store.wasm with mem := store.wasm.mem.write32 allocatorCursor finish } }
  let filled : MachineStore α :=
    { committed with wasm := { committed.wasm with mem := committed.wasm.mem.fill base.toNat size.toNat 0 } }
  have beforeFill : Steps
      ⟨.running ⟨allocatorLocals size base finish required current,
        commitTail, 1, [], [outerFrame], calls⟩, store⟩
      (tailPrefix.map StepKind.instruction)
      ⟨.running ⟨allocatorLocals size base finish required current
          [.i32 size, .i32 0, .i32 base],
        [.memoryFill], 1, [], [zeroFrame, outerFrame], calls⟩, committed⟩ := by
    simp only [tailPrefix, commitTail, zeroBody, allocatorLocals,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero]
    apply Steps.cons Step.const
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons (by
      simpa only [setMemory_eq, UInt32.zero_add, Nat.zero_add] using
        Step.store32 (logicalAddress := 0) (physicalAddress := 0)
          (by rfl) (by simpa only [Nat.zero_add] using hcursorBounds))
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons (Step.eqz (result := 0) (by simp [hbase]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons (Step.eqz (result := 0) (by simp [hsize]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons Step.const
    apply Steps.cons (Step.localGet (by rfl))
    exact Steps.refl _
  have prefixCost := beforeFill.growth_byteWork (by
    simp [tailPrefix, zeroBody, GrowthCostKind, PrimaryMemoryKind]) hostBytes
  have filling : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨allocatorLocals size base finish required current
          [.i32 size, .i32 0, .i32 base],
        [.memoryFill], 1, [], [zeroFrame, outerFrame], calls⟩, committed⟩
      [.instruction .memoryFill]
      ⟨.running ⟨allocatorLocals size base finish required current,
        [], 1, [], [zeroFrame, outerFrame], calls⟩, filled⟩ (1 + size.toNat) := by
    exact CostedSteps.single (Step.memoryFill32 hfillBounds)
  have last : Steps
      ⟨.running ⟨allocatorLocals size base finish required current,
        [], 1, [], [zeroFrame, outerFrame], calls⟩, filled⟩
      [.administrative .exitControl, .instruction (.localGet 1)]
      ⟨.running ⟨allocatorLocals size base finish required current [.i32 base],
        [.ret], 1, [], [outerFrame], calls⟩, filled⟩ := by
    exact .cons (.exitControl rfl) (.single (.localGet rfl))
  have suffixCost := last.growth_byteWork (by
    simp [GrowthCostKind, PrimaryMemoryKind]) hostBytes
  convert prefixCost.trans (filling.trans suffixCost) using 1 <;>
    simp [tailTrace, tailPrefix, zeroBody, committed, filled]
  omega

private def prefixTrace (memory : Mem) (finish : UInt32) : List StepKind :=
  ([Instruction.block 0 0 outerBody] ++ arithmeticPrefix).map StepKind.instruction ++
    growthTrace memory finish

private theorem prefixTrace_growth (memory : Mem) (finish : UInt32) :
    ∀ kind ∈ prefixTrace memory finish, GrowthCostKind kind := by
  by_cases h : memory.pages < (allocatorRequiredPages finish).toNat <;>
    simp [prefixTrace, growthTrace, h, arithmeticPrefix, growthBody,
      GrowthCostKind, PrimaryMemoryKind]

private theorem prefixTrace_length (memory : Mem) (finish : UInt32) :
    (prefixTrace memory finish).length =
      if memory.pages < (allocatorRequiredPages finish).toNat then 51 else 43 := by
  by_cases h : memory.pages < (allocatorRequiredPages finish).toNat <;>
    simp [prefixTrace, growthTrace, h, arithmeticPrefix, growthBody]

private theorem tailTrace_length : tailTrace.length = 16 := rfl

private theorem tailTrace_primary : ∀ kind ∈ tailTrace, PrimaryMemoryKind kind := by
  simp [tailTrace, tailPrefix, zeroBody, PrimaryMemoryKind]

/-- Complete actual call 12, including optional positive growth, cursor commit,
zero fill, and return to the original caller. Work counts semantic transitions,
all filled bytes, and all added physical bytes. No host function executes. -/
theorem func9_call_byteWork
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvalid : layout.Valid) (halignment : layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length ≤ 69 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨{ callerLocals with values := (.i32 4 ::
            .i32 (UInt32.ofNat layout.size) :: stack) },
          .call 12 :: code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
          code, arity, remainder, controls, calls⟩,
          finalStore store (UInt32.ofNat layout.size) base finish⟩
        (trace.length + layout.size + 65536 *
          ((allocatorRequiredPages finish).toNat - store.wasm.mem.pages)) ∧
      (∀ kind ∈ trace, PrimaryMemoryKind kind) := by
  let caller : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code, resultArity := arity, callerRemainder := remainder,
      control := controls, returningInstance := store.runtime.entry }
  let size := UInt32.ofNat layout.size
  let grown : MachineStore α :=
    { store with wasm := { store.wasm with mem := AllocatorExecution.grownMemory store.wasm.mem finish } }
  have facts := classifyBump_success_reachable frontier layout base finish
    hfrontier hvalid (Or.inr halignment) hclassify
  obtain ⟨_, hbase, _, halloc, hsigned, hfinish, _⟩ := facts
  have hfinishSigned : finish.toNat < 2147483648 := by omega
  have hsizeNat : size.toNat = layout.size :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hsizeNonzero : size ≠ 0 := by
    intro zero
    have positive := hvalid.1
    rw [← hsizeNat, zero] at positive
    contradiction
  have before := arithmetic_prefix_steps store layout frontier storedCursor base finish
    (caller :: calls) halignment hclassify hcursor heffective hcursorBounds
  have growth := growth_steps store size base finish
    (UInt32.ofNat (frontier + (layout.alignment - 1))) (caller :: calls)
    (by rw [hmodule]; rfl) hcap (hpages.trans_lt (by decide)) hfinishSigned
  have prefixExecution := before.trans growth
  have prefixCost := prefixExecution.growth_byteWork
    (prefixTrace_growth store.wasm.mem finish) hostBytes
  have zeroCost := commit_zero_cost grown size base finish
    (allocatorRequiredPages finish) store.wasm.mem.pages.toUInt32
    (caller :: calls) hbase hsizeNonzero
    (hcursorBounds.trans (Nat.mul_le_mul_right 65536 (Nat.le_max_left _ _)))
    (by
      change base.toNat + size.toNat ≤
        max store.wasm.mem.pages (allocatorRequiredPages finish).toNat * 65536
      rw [hsizeNat, ← hfinish]
      exact (allocatorRequiredPages_covers finish hfinishSigned).trans
        (Nat.mul_le_mul_right 65536 (Nat.le_max_right _ _))) hostBytes
  have call : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨{ callerLocals with values := .i32 4 :: .i32 size :: stack },
        .call 12 :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction (.call 12)]
      ⟨.running ⟨func9Def.toLocals [.i32 size, .i32 (UInt32.ofNat layout.alignment)],
        func9Def.body, 1, [], [], caller :: calls⟩, store⟩ 1 := by
    rw [halignment]
    exact CostedSteps.single (Step.call (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
  have returning : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨allocatorLocals size base finish (allocatorRequiredPages finish)
          store.wasm.mem.pages.toUInt32 [.i32 base],
        [.ret], 1, [], [outerFrame], caller :: calls⟩, finalStore store size base finish⟩
      [.administrative .returnFromCall]
      ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
        code, arity, remainder, controls, calls⟩, finalStore store size base finish⟩ 1 :=
    CostedSteps.single (Step.returnFromCallExplicit rfl)
  refine ⟨[.instruction (.call 12)] ++ prefixTrace store.wasm.mem finish ++
    tailTrace ++ [.administrative .returnFromCall], ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil,
      prefixTrace_length, tailTrace_length]
    split <;> omega
  · have result := call.trans (prefixCost.trans (zeroCost.trans returning))
    convert result using 1 <;>
      simp [prefixTrace, List.append_assoc, size,
        AllocatorExecution.grownMemory, tailTrace_length, hsizeNat]
    have delta : max store.wasm.mem.pages (allocatorRequiredPages finish).toNat -
        store.wasm.mem.pages =
        (allocatorRequiredPages finish).toNat - store.wasm.mem.pages := by omega
    rw [delta]
    omega
  · intro kind member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ((rfl | member) | member) | rfl
    · trivial
    · exact (prefixTrace_growth _ _ kind member).primary
    · exact tailTrace_primary kind member
    · trivial

@[simp] theorem finalStore_pages {α : Type} (store : MachineStore α)
    (size base finish : UInt32) :
    (finalStore store size base finish).wasm.mem.pages =
      max store.wasm.mem.pages (allocatorRequiredPages finish).toNat := rfl

/-- The committed cursor survives filling because its four bytes precede
this allocation. Reachable successful allocations establish this separation. -/
theorem finalStore_cursor {α : Type} (store : MachineStore α)
    (size base finish : UInt32)
    (hseparate : allocatorCursor.toNat + 4 ≤ base.toNat) :
    (finalStore store size base finish).wasm.mem.read32 allocatorCursor = finish := by
  calc
    _ = ((AllocatorExecution.grownMemory store.wasm.mem finish).write32
        allocatorCursor finish).read32 allocatorCursor := by
      have h0 : ¬ base.toNat ≤ allocatorCursor.toNat := by omega
      have h1 : ¬ base.toNat ≤ allocatorCursor.toNat + 1 := by omega
      have h2 : ¬ base.toNat ≤ allocatorCursor.toNat + 2 := by omega
      have h3 : ¬ base.toNat ≤ allocatorCursor.toNat + 3 := by omega
      simp [finalStore, Mem.read32, Mem.fill, h0, h1, h2, h3]
    _ = finish := Mem.read32_write32_same _ _ _

/-- Every byte of the returned allocation is zero in the same exact store. -/
theorem finalStore_zero {α : Type} (store : MachineStore α)
    (size base finish address : UInt32)
    (hinside : base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + size.toNat) :
    (finalStore store size base finish).wasm.mem.read8 address = 0 :=
  Mem.fill_read8_in _ _ _ _ _ hinside

/-- Store components unrelated to allocation retain their exact values. -/
theorem finalStore_frame {α : Type} (store : MachineStore α)
    (size base finish : UInt32) :
    (finalStore store size base finish).runtime = store.runtime ∧
    (finalStore store size base finish).wasm.memoryCaps = store.wasm.memoryCaps ∧
    (finalStore store size base finish).wasm.host = store.wasm.host ∧
    (finalStore store size base finish).wasm.globals = store.wasm.globals :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Caller-oriented initial configuration for the actual absolute call 12. -/
def callConfig (store : MachineStore α) (layout : AllocLayout)
    (caller : ThreadState α) : Config α :=
  ⟨.running { caller with
    locals := { caller.locals with values := .i32 4 :: .i32 (UInt32.ofNat layout.size) :: caller.locals.values }
    code := .call 12 :: caller.code }, store⟩

def returnConfig (store : MachineStore α) (layout : AllocLayout)
    (base finish : UInt32) (caller : ThreadState α) : Config α :=
  ⟨.running { caller with
    locals := { caller.locals with values := .i32 base :: caller.locals.values } },
    finalStore store (UInt32.ofNat layout.size) base finish⟩

/-- Work, successful cursor commit, and every physical prefix bound belong to
one actual execution ending at caller resumption. The final page count reaches
its stated peak, which may exceed the initial page count. -/
theorem func9_call_memory_work
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32) (caller : ThreadState α)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvalid : layout.Valid) (halignment : layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length ≤ 69 ∧
      CostedSteps (byteWork hostBytes) (callConfig store layout caller) trace
        (returnConfig store layout base finish caller)
        (trace.length + layout.size + 65536 *
          ((allocatorRequiredPages finish).toNat - store.wasm.mem.pages)) ∧
      (returnConfig store layout base finish caller).store.wasm.mem.read32 allocatorCursor = finish ∧
      (returnConfig store layout base finish caller).store.wasm.mem.pages =
        max store.wasm.mem.pages (allocatorRequiredPages finish).toNat ∧
      ∀ (partialTrace : List StepKind) (middle : Config α),
        Steps (callConfig store layout caller) partialTrace middle →
        partialTrace.length ≤ trace.length →
        store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
        middle.store.wasm.mem.pages ≤
          max store.wasm.mem.pages (allocatorRequiredPages finish).toNat := by
  obtain ⟨trace, bound, execution, allowed⟩ := func9_call_byteWork store layout
    frontier storedCursor base finish caller.locals caller.locals.values caller.code
    caller.resultArity caller.callerRemainder caller.control caller.calls
    hmodule hcap hpages hfrontier hvalid halignment hclassify hcursor heffective
    hcursorBounds hostBytes
  have hbase := (classifyBump_success_reachable frontier layout base finish
    hfrontier hvalid (Or.inr halignment) hclassify).1
  have hcursorBefore : allocatorCursor.toNat + 4 ≤ base.toNat := by
    have hcursorHeap : allocatorCursor.toNat + 4 ≤ heapBase.toNat := by decide
    omega
  refine ⟨trace, bound, execution, finalStore_cursor _ _ _ _ hcursorBefore, rfl, ?_⟩
  intro partialTrace middle first lengthBound
  exact execution.erase.primary_pages_at_prefix first lengthBound allowed

private def boundaryStore : MachineStore Universal.State :=
  let m := Project.Mergesort.module
  { runtime := { instances := #[{ module := m, host := Universal.envFor m }], entry := ⟨0⟩ }
    wasm := { mem := ((Mem.empty 17).write8 heapBase 77).write8 (heapBase - 1) 99, globals := ⟨[]⟩, host := default, memoryCaps := [Module.memoryHardCap] } }

private def boundaryCaller : ThreadState Universal.State :=
  ⟨⟨[.i32 101], [.i32 102], [.i32 103]⟩,
    [.unreachable], 1, [.i32 104], [], []⟩

set_option maxRecDepth 65536 in
/-- Positive physical growth (17 to 18 pages), nonzero old bytes cleared,
committed cursor, and a preserved neighboring byte in the actual runner.
The caller's trap one step later lies outside the certified interval. -/
theorem page_boundary_runner :
    (runSteps 69 (callConfig boundaryStore { size := 65536, alignment := 4 }
      boundaryCaller)).result.finalConfig? =
      some (returnConfig boundaryStore { size := 65536, alignment := 4 }
        heapBase 1115072 boundaryCaller) ∧
    (runSteps 69 (callConfig boundaryStore { size := 65536, alignment := 4 }
      boundaryCaller)).result.finalConfig?.map (fun c => c.store.wasm.mem.pages) = some 18 ∧
    (finalStore boundaryStore 65536 heapBase 1115072).wasm.mem.read32 allocatorCursor = 1115072 ∧
    (finalStore boundaryStore 65536 heapBase 1115072).wasm.mem.read8 heapBase = 0 ∧
    (finalStore boundaryStore 65536 heapBase 1115072).wasm.mem.read8 (heapBase - 1) = 99 ∧
    (runSteps 70 (callConfig boundaryStore { size := 65536, alignment := 4 }
      boundaryCaller)).result.trapReason? = some .unreachable := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 65536 in
/-- The no-growth branch returns after 61 steps, clears existing bytes, and
keeps the original page count. -/
theorem no_growth_runner :
    (runSteps 61 (callConfig boundaryStore { size := 4, alignment := 4 }
      boundaryCaller)).result.finalConfig? =
      some (returnConfig boundaryStore { size := 4, alignment := 4 }
        heapBase 1049540 boundaryCaller) ∧
    (runSteps 61 (callConfig boundaryStore { size := 4, alignment := 4 }
      boundaryCaller)).result.finalConfig?.map (fun c => c.store.wasm.mem.pages) = some 17 := by
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 65536 in
/-- The symbolic certificate proves the page-crossing regression, including
all actual prefixes. Growth and fill each contribute 65,536 work units. -/
theorem page_boundary_resources (hostBytes : Config Universal.State → Nat →
    Config Universal.State → Nat) :
    ∃ trace, trace.length ≤ 69 ∧
      CostedSteps (byteWork hostBytes)
        (callConfig boundaryStore { size := 65536, alignment := 4 } boundaryCaller)
        trace (returnConfig boundaryStore { size := 65536, alignment := 4 }
          heapBase 1115072 boundaryCaller) (trace.length + 131072) ∧
      ∀ (partialTrace : List StepKind) (middle : Config Universal.State),
        Steps (callConfig boundaryStore { size := 65536, alignment := 4 } boundaryCaller)
          partialTrace middle → partialTrace.length ≤ trace.length →
          17 ≤ middle.store.wasm.mem.pages ∧ middle.store.wasm.mem.pages ≤ 18 := by
  obtain ⟨trace, bound, execution, _, _, peak⟩ := func9_call_memory_work boundaryStore
    { size := 65536, alignment := 4 } heapBase.toNat 0 heapBase 1115072
    boundaryCaller rfl rfl (by decide) (by decide) (by exact ⟨by decide, by decide, ⟨2, rfl⟩, by decide, by decide, by decide, by decide⟩) rfl
    (by decide) rfl rfl (by decide) hostBytes
  refine ⟨trace, bound, ?_, peak⟩
  convert execution using 1
  change trace.length + 131072 = trace.length + 65536 + 65536 * (18 - 17)
  omega

end Project.Mergesort.ZeroedAllocatorExecution
