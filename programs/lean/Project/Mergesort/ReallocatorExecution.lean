import Project.Mergesort.AllocatorExecution

/-!
# Actual execution of the compiled growing reallocator

Local `func8` (absolute call 11) executes bump arithmetic, optional growth,
cursor commit, copying of the old allocation, and the original caller return.
The certificates charge both actual growth bytes and copied bytes.
-/

namespace Project.Mergesort.ReallocatorExecution

open Wasm Wasm.SmallStep
open Project.Mergesort.Representations Project.Mergesort.MemoryBounds

private def arithmeticPrefix : Program :=
  [.localGet 2, .const 0xFFFFFFFF, .add, .localTee 4,
    .const 0, .load32 allocatorCursor, .localTee 5,
    .const heapBase, .localGet 5, .select, .add, .localTee 5,
    .localGet 4, .ltU, .br_if 0,
    .localGet 5, .const 0, .localGet 2, .sub, .and, .localTee 2,
    .localGet 3, .add, .localTee 4,
    .localGet 2, .ltU, .br_if 0,
    .localGet 4, .const 0, .ltS, .br_if 0]

private def growthBody : Program :=
  [.localGet 4, .const 65535, .add, .const 16, .shrU,
    .localTee 5, .memorySize, .localTee 6, .leU, .br_if 0,
    .localGet 5, .localGet 6, .sub, .memoryGrow,
    .const 0xFFFFFFFF, .eq, .br_if 1]

private def copyBody : Program :=
  [.localGet 2, .eqz, .br_if 0,
    .localGet 3, .localGet 1, .localGet 3, .localGet 1, .ltU,
    .select, .localTee 4, .eqz, .br_if 0,
    .localGet 2, .localGet 0, .localGet 4, .memoryCopy]

private def commitTail : Program :=
  [.const 0, .localGet 4, .store32 allocatorCursor,
    .block 0 0 copyBody, .localGet 2, .ret]

private def outerBody : Program :=
  arithmeticPrefix ++ [.block 0 0 growthBody] ++ commitTail

/-- The symbolic trace below executes the actual WAT-decoded body. -/
theorem compiled_body :
    func8Def.body = [.block 0 0 outerBody, .call 9, .unreachable] := rfl

private def outerFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := outerBody, continuation := [.call 9, .unreachable], belowStack := [] }

private def growthFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := growthBody, continuation := commitTail, belowStack := [] }

private def copyFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := copyBody, continuation := [.localGet 2, .ret], belowStack := [] }

private def allocatorLocals (oldPtr oldSize size base finish required current : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[.i32 oldPtr, .i32 oldSize, .i32 base, .i32 size], [.i32 finish, .i32 required, .i32 current], values⟩

/-- The exact cursor commit and physical old-allocation copy. -/
def finalStore {α : Type} (store : MachineStore α)
    (oldPtr oldSize base finish : UInt32) : MachineStore α :=
  { store with wasm := { store.wasm with mem := ((AllocatorExecution.grownMemory store.wasm.mem finish).write32 allocatorCursor finish).copy base.toNat oldPtr.toNat oldSize.toNat } }

private def growthTrace (memory : Mem) (finish : UInt32) : List StepKind :=
  [.instruction (.block 0 0 growthBody)] ++
  (growthBody.take 10).map StepKind.instruction ++
  if memory.pages < (allocatorRequiredPages finish).toNat then
    (growthBody.drop 10).map StepKind.instruction ++ [.administrative .exitControl]
  else []

private theorem growth_steps
    {α : Type} (store : MachineStore α) (oldPtr oldSize size base finish auxiliary : UInt32)
    (calls : List CallFrame)
    (h32 : store.runtime.currentModule.memIs64 = false)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages < UInt32.size)
    (hfinish : finish.toNat < 2147483648) :
    Steps
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base finish auxiliary 0,
        [.block 0 0 growthBody] ++ commitTail, 1, [], [outerFrame], calls⟩, store⟩
      (growthTrace store.wasm.mem finish)
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base finish (allocatorRequiredPages finish)
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
    ⟨.running ⟨allocatorLocals oldPtr oldSize size base finish auxiliary 0
      [.i32 (allocatorRequiredPages finish)],
      .localTee 5 :: .memorySize :: .localTee 6 :: .leU :: .br_if 0 ::
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
    {α : Type} (store : MachineStore α) (layout : AllocLayout) (oldPtr oldSize : UInt32)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (calls : List CallFrame)
    (halignment : layout.alignment = 1)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Steps
      ⟨.running ⟨allocatorLocals oldPtr oldSize (UInt32.ofNat layout.size)
          (UInt32.ofNat layout.alignment) 0 0 0,
        func8Def.body, 1, [], [], calls⟩, store⟩
      (([Instruction.block 0 0 outerBody] ++ arithmeticPrefix).map
        StepKind.instruction)
      ⟨.running ⟨allocatorLocals oldPtr oldSize (UInt32.ofNat layout.size) base finish
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
  [.const 0, .localGet 4, .store32 allocatorCursor,
    .block 0 0 copyBody] ++ copyBody.take 15

private def tailTrace : List StepKind :=
  tailPrefix.map StepKind.instruction ++
    [.instruction .memoryCopy, .administrative .exitControl, .instruction (.localGet 2)]

private theorem commit_copy_cost
    {α : Type} (store : MachineStore α) (oldPtr oldSize size base finish required current : UInt32)
    (calls : List CallFrame)
    (hbase : base ≠ 0) (holdPositive : oldSize ≠ 0) (hold : oldSize < size)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hsource : oldPtr.toNat + oldSize.toNat ≤ store.wasm.mem.pages * 65536)
    (hdestination : base.toNat + oldSize.toNat ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base finish required current,
        commitTail, 1, [], [outerFrame], calls⟩, store⟩ tailTrace
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base oldSize required current [.i32 base],
        [.ret], 1, [], [outerFrame], calls⟩,
        { store with wasm := { store.wasm with mem :=
          (store.wasm.mem.write32 allocatorCursor finish).copy base.toNat oldPtr.toNat oldSize.toNat } }⟩
      (22 + oldSize.toNat) := by
  let committed : MachineStore α :=
    { store with wasm := { store.wasm with mem := store.wasm.mem.write32 allocatorCursor finish } }
  let copied : MachineStore α :=
    { committed with wasm := { committed.wasm with mem := committed.wasm.mem.copy base.toNat oldPtr.toNat oldSize.toNat } }
  have beforeCopy : Steps
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base finish required current,
        commitTail, 1, [], [outerFrame], calls⟩, store⟩
      (tailPrefix.map StepKind.instruction)
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base oldSize required current
          [.i32 oldSize, .i32 oldPtr, .i32 base],
        [.memoryCopy], 1, [], [copyFrame, outerFrame], calls⟩, committed⟩ := by
    simp only [tailPrefix, commitTail, copyBody, allocatorLocals,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero]
    apply Steps.cons Step.const
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons (by
      simpa only [setMemory_eq, UInt32.zero_add, Nat.zero_add] using
        Step.store32 (logicalAddress := 0) (physicalAddress := 0)
          (by rfl) (by simpa only [Nat.zero_add] using hcursorBounds))
    wasm_steps [.block, (.localGet rfl), (.eqz (result := 0) (by simp [hbase])), .brIfZero,
      (.localGet rfl), (.localGet rfl), (.localGet rfl), (.localGet rfl),
      (.ltU (result := 0) (by simp [UInt32.not_lt.mpr (UInt32.le_of_lt hold)])),
      (.select rfl), (.localTee rfl), (.eqz (result := 0) (by simp [holdPositive])), .brIfZero,
      (.localGet rfl), (.localGet rfl), (.localGet rfl)]
    exact Steps.refl _
  have prefixCost := beforeCopy.growth_byteWork (by
    simp [tailPrefix, copyBody, GrowthCostKind, PrimaryMemoryKind]) hostBytes
  have copying : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base oldSize required current
          [.i32 oldSize, .i32 oldPtr, .i32 base],
        [.memoryCopy], 1, [], [copyFrame, outerFrame], calls⟩, committed⟩
      [.instruction .memoryCopy]
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base oldSize required current,
        [], 1, [], [copyFrame, outerFrame], calls⟩, copied⟩ (1 + oldSize.toNat) := by
    exact CostedSteps.single (Step.memoryCopy32 hdestination hsource)
  have last : Steps
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base oldSize required current,
        [], 1, [], [copyFrame, outerFrame], calls⟩, copied⟩
      [.administrative .exitControl, .instruction (.localGet 2)]
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base oldSize required current [.i32 base],
        [.ret], 1, [], [outerFrame], calls⟩, copied⟩ := by
    exact .cons (.exitControl rfl) (.single (.localGet rfl))
  have suffixCost := last.growth_byteWork (by
    simp [GrowthCostKind, PrimaryMemoryKind]) hostBytes
  convert prefixCost.trans (copying.trans suffixCost) using 1 <;>
    simp [tailTrace, tailPrefix, copyBody, committed, copied]
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

private theorem tailTrace_length : tailTrace.length = 22 := rfl

private theorem tailTrace_primary : ∀ kind ∈ tailTrace, PrimaryMemoryKind kind := by
  simp [tailTrace, tailPrefix, copyBody, PrimaryMemoryKind]

/-- Complete actual call 11, with copied old bytes and physical growth charged.
Initial allocator arithmetic, cursor facts, and source bounds establish its
normal return; no future allocation or copying execution is assumed. -/
theorem func8_call_byteWork
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (oldPtr oldSize : UInt32) (frontier : Nat) (storedCursor base finish : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvalid : layout.Valid) (halignment : layout.alignment = 1)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) = UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (holdPositive : 0 < oldSize.toNat) (hold : oldSize.toNat < layout.size)
    (hsource : oldPtr.toNat + oldSize.toNat ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length ≤ 75 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨{ callerLocals with values := (.i32 (UInt32.ofNat layout.size) ::
            .i32 1 :: .i32 oldSize :: .i32 oldPtr :: stack) },
          .call 11 :: code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
          code, arity, remainder, controls, calls⟩, finalStore store oldPtr oldSize base finish⟩
        (trace.length + oldSize.toNat + 65536 *
          ((allocatorRequiredPages finish).toNat - store.wasm.mem.pages)) ∧
      (∀ kind ∈ trace, PrimaryMemoryKind kind) := by
  let caller : CallFrame :=
    { locals := { callerLocals with values := stack }, continuation := code,
      resultArity := arity, callerRemainder := remainder, control := controls,
      returningInstance := store.runtime.entry }
  let size := UInt32.ofNat layout.size
  let grown : MachineStore α :=
    { store with wasm := { store.wasm with mem := AllocatorExecution.grownMemory store.wasm.mem finish } }
  have facts := classifyBump_success_reachable frontier layout base finish
    hfrontier hvalid (Or.inl halignment) hclassify
  obtain ⟨_, hbase, _, halloc, hsigned, hfinish, _⟩ := facts
  have hfinishSigned : finish.toNat < 2147483648 := by omega
  have hsizeNat : size.toNat = layout.size := UInt32.toNat_ofNat_of_lt' (by omega)
  have holdNonzero : oldSize ≠ 0 := by
    intro hz
    rw [hz] at holdPositive
    contradiction
  have holdWord : oldSize < size := by
    rw [UInt32.lt_iff_toNat_lt, hsizeNat]
    exact hold
  have before := arithmetic_prefix_steps store layout oldPtr oldSize frontier storedCursor base finish
    (caller :: calls) halignment hclassify hcursor heffective hcursorBounds
  have growth := growth_steps store oldPtr oldSize size base finish
    (UInt32.ofNat (frontier + (layout.alignment - 1))) (caller :: calls)
    (by rw [hmodule]; rfl) hcap (hpages.trans_lt (by decide)) hfinishSigned
  have prefixExecution := before.trans growth
  have prefixCost := prefixExecution.growth_byteWork
    (prefixTrace_growth store.wasm.mem finish) hostBytes
  have copyCost := commit_copy_cost grown oldPtr oldSize size base finish
    (allocatorRequiredPages finish) store.wasm.mem.pages.toUInt32
    (caller :: calls) hbase holdNonzero holdWord
    (hcursorBounds.trans (Nat.mul_le_mul_right 65536 (Nat.le_max_left _ _)))
    (hsource.trans (Nat.mul_le_mul_right 65536 (Nat.le_max_left _ _)))
    (by
      change base.toNat + oldSize.toNat ≤
        max store.wasm.mem.pages (allocatorRequiredPages finish).toNat * 65536
      have hn := (allocatorRequiredPages_covers finish hfinishSigned).trans
        (Nat.mul_le_mul_right 65536 (Nat.le_max_right store.wasm.mem.pages _))
      omega) hostBytes
  have call : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨{ callerLocals with values := .i32 size :: .i32 1 :: .i32 oldSize :: .i32 oldPtr :: stack },
        .call 11 :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction (.call 11)]
      ⟨.running ⟨func8Def.toLocals [.i32 oldPtr, .i32 oldSize, .i32 (UInt32.ofNat layout.alignment), .i32 size],
        func8Def.body, 1, [], [], caller :: calls⟩, store⟩ 1 := by
    rw [halignment]
    exact CostedSteps.single (Step.call (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
  have returning : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨allocatorLocals oldPtr oldSize size base oldSize (allocatorRequiredPages finish)
          store.wasm.mem.pages.toUInt32 [.i32 base],
        [.ret], 1, [], [outerFrame], caller :: calls⟩, finalStore store oldPtr oldSize base finish⟩
      [.administrative .returnFromCall]
      ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
        code, arity, remainder, controls, calls⟩, finalStore store oldPtr oldSize base finish⟩ 1 :=
    CostedSteps.single (Step.returnFromCallExplicit rfl)
  refine ⟨[.instruction (.call 11)] ++ prefixTrace store.wasm.mem finish ++
    tailTrace ++ [.administrative .returnFromCall], ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil,
      prefixTrace_length, tailTrace_length]
    split <;> omega
  · have result := call.trans (prefixCost.trans (copyCost.trans returning))
    convert result using 1 <;>
      simp [prefixTrace, List.append_assoc, AllocatorExecution.grownMemory, tailTrace_length]
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
    (oldPtr oldSize base finish : UInt32) :
    (finalStore store oldPtr oldSize base finish).wasm.mem.pages =
      max store.wasm.mem.pages (allocatorRequiredPages finish).toNat := rfl

/-- The cursor commit survives copying into an allocation above its slot. -/
theorem finalStore_cursor {α : Type} (store : MachineStore α)
    (oldPtr oldSize base finish : UInt32)
    (hseparate : allocatorCursor.toNat + 4 ≤ base.toNat) :
    (finalStore store oldPtr oldSize base finish).wasm.mem.read32 allocatorCursor = finish := by
  calc
    _ = ((AllocatorExecution.grownMemory store.wasm.mem finish).write32
        allocatorCursor finish).read32 allocatorCursor := by
      have h0 : ¬ base.toNat ≤ allocatorCursor.toNat := by omega
      have h1 : ¬ base.toNat ≤ allocatorCursor.toNat + 1 := by omega
      have h2 : ¬ base.toNat ≤ allocatorCursor.toNat + 2 := by omega
      have h3 : ¬ base.toNat ≤ allocatorCursor.toNat + 3 := by omega
      simp [finalStore, Mem.read32, Mem.copy, h0, h1, h2, h3]
    _ = finish := Mem.read32_write32_same _ _ _

/-- Every store component other than primary memory is retained. -/
theorem finalStore_frame {α : Type} (store : MachineStore α)
    (oldPtr oldSize base finish : UInt32) :
    (finalStore store oldPtr oldSize base finish).runtime = store.runtime ∧
    (finalStore store oldPtr oldSize base finish).wasm.memoryCaps = store.wasm.memoryCaps ∧
    (finalStore store oldPtr oldSize base finish).wasm.globals = store.wasm.globals ∧
    (finalStore store oldPtr oldSize base finish).wasm.host = store.wasm.host :=
  ⟨rfl, rfl, rfl, rfl⟩

end Project.Mergesort.ReallocatorExecution
