import Project.Mergesort.MemoryBounds
import CodeLib.SepLogic.MemoryTrace

/-!
# Normal execution of the compiled merge-sort bump allocator

The proofs use the authoritative small-step relation.  In particular,
`memory.size`, delta calculation and `memory.grow` are kept in one concrete
execution, so an exact physical page count is not weakened to a persistent
lower-bound snapshot between instructions.
-/

namespace Project.Mergesort.AllocatorExecution

open Wasm Wasm.SmallStep
open Project.Mergesort.Representations Project.Mergesort.MemoryBounds

private def arithmeticPrefix : Program :=
  [.localGet 1, .const 0xFFFFFFFF, .add, .localTee 2,
    .const 0, .load32 allocatorCursor, .localTee 3,
    .const heapBase, .localGet 3, .select, .add, .localTee 3,
    .localGet 2, .ltU, .br_if 0,
    .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 2,
    .localGet 0, .add, .localTee 1,
    .localGet 2, .ltU, .br_if 0,
    .localGet 1, .const 0, .ltS, .br_if 0]

private def growthTail : Program :=
  [.localGet 1, .const 65535, .add, .const 16, .shrU,
    .localTee 3, .memorySize, .localTee 0, .leU, .br_if 1] ++
    allocatorGrowSuffix

private def commitTail : Program :=
  [.const 0, .localGet 1, .store32 allocatorCursor, .localGet 2]

private def innerBody : Program := arithmeticPrefix ++ growthTail
private def outerBody : Program := [.block 0 0 innerBody, .call 9, .unreachable]

private theorem compiled_body :
    func5Def.body = [.block 0 0 outerBody] ++ commitTail := by rfl

private def innerFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := innerBody, continuation := [.call 9, .unreachable], belowStack := [] }

private def outerFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := outerBody, continuation := commitTail, belowStack := [] }

private def allocatorLocals (first finish base auxiliary : UInt32) : Locals :=
  ⟨[.i32 first, .i32 finish], [.i32 base, .i32 auxiliary], []⟩

private def growthTrace (memory : Mem) (finish : UInt32) : List StepKind :=
  [.localGet 1, .const 65535, .add, .const 16, .shrU,
    .localTee 3, .memorySize, .localTee 0, .leU, .br_if 1].map
      StepKind.instruction ++
    if memory.pages < (allocatorRequiredPages finish).toNat then
      allocatorGrowSuffix.map StepKind.instruction else []

/-- The exact physical memory after the allocator's optional growth. -/
def grownMemory (memory : Mem) (finish : UInt32) : Mem :=
  { memory with pages := max memory.pages (allocatorRequiredPages finish).toNat }

/-- Exact post-store, including the allocator cursor commit.  All other store
components and all bytes outside the cursor word are inherited unchanged. -/
def finalStore {α : Type} (store : MachineStore α) (finish : UInt32) : MachineStore α :=
  { store with wasm := { store.wasm with mem :=
      (grownMemory store.wasm.mem finish).write32 allocatorCursor finish } }

/-- Serialized physical measurement, comparison, optional growth and success
branch for the actual compiled allocator. -/
private theorem growth_tail_steps
    {α : Type} (store : MachineStore α) (first finish base auxiliary : UInt32)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (h32 : store.runtime.currentModule.memIs64 = false)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages < UInt32.size)
    (hfinish : finish.toNat < 2147483648) :
    Steps
      ⟨.running ⟨allocatorLocals first finish base auxiliary,
        growthTail, arity, remainder, innerFrame :: outerFrame :: controls, calls⟩,
        store⟩ (growthTrace store.wasm.mem finish)
      ⟨.running ⟨allocatorLocals store.wasm.mem.pages.toUInt32 finish base
          (allocatorRequiredPages finish), commitTail,
        arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem := grownMemory store.wasm.mem finish } }⟩ := by
  simp only [growthTail, growthTrace, allocatorLocals,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  rw [show (65535 : UInt32) + finish = finish + 65535 from UInt32.add_comm _ _]
  apply Steps.cons Step.const
  apply Steps.cons Step.shrU
  change Steps
    ⟨.running ⟨⟨[.i32 first, .i32 finish], [.i32 base, .i32 auxiliary],
      [.i32 (allocatorRequiredPages finish)]⟩,
      .localTee 3 :: .memorySize :: .localTee 0 :: .leU :: .br_if 1 ::
        allocatorGrowSuffix, arity, remainder, innerFrame :: outerFrame :: controls,
      calls⟩, store⟩ _ _
  apply Steps.cons (Step.localTee (by rfl))
  apply Steps.cons Step.memorySize
  simp only [sizeValue, h32, Bool.false_eq_true, ↓reduceIte]
  apply Steps.cons (Step.localTee (by rfl))
  have hpagesNat : store.wasm.mem.pages.toUInt32.toNat = store.wasm.mem.pages :=
    UInt32.toNat_ofNat_of_lt' hpages
  by_cases hneed : store.wasm.mem.pages < (allocatorRequiredPages finish).toNat
  · have hnotFits : ¬ allocatorRequiredPages finish ≤ store.wasm.mem.pages.toUInt32 := by
      rw [UInt32.le_iff_toNat_le_toNat, hpagesNat]
      omega
    simp only [if_pos hneed]
    apply Steps.cons (Step.leU (result := 0) (by simp [hnotFits]))
    apply Steps.cons Step.brIfZero
    simpa only [grownMemory, max_eq_right (Nat.le_of_lt hneed),
      innerFrame, outerFrame, commitTail, allocatorLocals,
      List.set, List.length, Nat.reduceAdd, Nat.reduceSub] using
      allocatorGrowSuffix_to_commit_steps store finish base remainder arity
        innerFrame outerBody controls calls hcap hfinish hneed
  · have hfits : allocatorRequiredPages finish ≤ store.wasm.mem.pages.toUInt32 := by
      rw [UInt32.le_iff_toNat_le_toNat, hpagesNat]
      omega
    simp only [if_neg hneed]
    apply Steps.cons (Step.leU (result := 1) (by simp [hfits]))
    apply Steps.cons (Step.brIf (by decide) (by rfl))
    simpa only [grownMemory, max_eq_left (Nat.le_of_not_gt hneed),
      outerFrame, allocatorLocals, List.set, List.length,
      Nat.reduceAdd, Nat.reduceSub, List.take_zero, List.nil_append] using Steps.refl
      (⟨.running ⟨allocatorLocals store.wasm.mem.pages.toUInt32 finish base
        (allocatorRequiredPages finish), commitTail, arity, remainder, controls, calls⟩,
        store⟩ : Config α)

private theorem commit_steps
    {α : Type} (store : MachineStore α) (first finish base auxiliary : UInt32)
    (calls : List CallFrame)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Steps
      ⟨.running ⟨allocatorLocals first finish base auxiliary,
        commitTail, 1, [], [], calls⟩, store⟩ (commitTail.map StepKind.instruction)
      ⟨.running ⟨{ allocatorLocals first finish base auxiliary with values := [.i32 base] },
          [], 1, [], [], calls⟩,
        { store with
          wasm := { store.wasm with
            mem := store.wasm.mem.write32 allocatorCursor finish } }⟩ := by
  simp only [allocatorLocals, commitTail, List.map_cons, List.map_nil]
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (by
    simpa only [setMemory_eq, UInt32.zero_add, Nat.zero_add] using
      Step.store32 (logicalAddress := 0) (physicalAddress := 0)
        (by rfl) (by simpa only [Nat.zero_add] using hcursorBounds))
  apply Steps.cons (Step.localGet (by rfl))
  exact Steps.refl _

private theorem arithmetic_prefix_steps
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (calls : List CallFrame)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Steps
      ⟨.running ⟨allocatorLocals (UInt32.ofNat layout.size)
          (UInt32.ofNat layout.alignment) 0 0,
        func5Def.body, 1, [], [], calls⟩, store⟩
      (([Instruction.block 0 0 outerBody, Instruction.block 0 0 innerBody] ++ arithmeticPrefix).map
        StepKind.instruction)
      ⟨.running ⟨allocatorLocals (UInt32.ofNat layout.size) finish base
          (UInt32.ofNat (frontier + (layout.alignment - 1))),
        growthTail, 1, [], [innerFrame, outerFrame], calls⟩, store⟩ := by
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  dsimp only at hfacts
  obtain ⟨hsum, hbase, hend, hsigned, hfinishNat⟩ := hfacts
  have hfrontier : frontier < UInt32.size := by omega
  have hpadSmall : layout.alignment - 1 ≤ 3 := by
    rcases halignment with h | h <;> omega
  have hpadBound : layout.alignment - 1 < UInt32.size := by
    exact Nat.lt_of_le_of_lt hpadSmall (by decide)
  have hsizeBound : layout.size < UInt32.size := by omega
  have hsizeNat : (UInt32.ofNat layout.size).toNat = layout.size :=
    UInt32.toNat_ofNat_of_lt' hsizeBound
  have hpadWord : (0xFFFFFFFF : UInt32) + UInt32.ofNat layout.alignment =
      UInt32.ofNat (layout.alignment - 1) := by
    rcases halignment with h | h <;> rw [h] <;> decide
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
  apply Steps.cons Step.block
  simp only [innerBody, arithmeticPrefix, List.cons_append, List.nil_append]
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
  simp only [innerFrame, outerFrame, outerBody, innerBody,
    List.set, List.length, Nat.reduceAdd, Nat.reduceSub,
    List.drop_zero]
  exact Steps.refl _

private def bodyTrace (memory : Mem) (finish : UInt32) : List StepKind :=
  ([Instruction.block 0 0 outerBody, Instruction.block 0 0 innerBody] ++
    arithmeticPrefix).map StepKind.instruction ++
    growthTrace memory finish ++ commitTail.map StepKind.instruction

private theorem body_steps
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (calls : List CallFrame)
    (h32 : store.runtime.currentModule.memIs64 = false)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages < UInt32.size)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Steps
      ⟨.running ⟨func5Def.toLocals
          [.i32 (UInt32.ofNat layout.size), .i32 (UInt32.ofNat layout.alignment)],
        func5Def.body, 1, [], [], calls⟩, store⟩ (bodyTrace store.wasm.mem finish)
      ⟨.running ⟨{ allocatorLocals store.wasm.mem.pages.toUInt32 finish base
          (allocatorRequiredPages finish) with values := [.i32 base] },
        [], 1, [], [], calls⟩, finalStore store finish⟩ := by
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  dsimp only at hfacts
  have hsigned : finish.toNat < 2147483648 := by omega
  have hprefix := arithmetic_prefix_steps store layout frontier storedCursor base finish
    calls halignment hclassify hcursor heffective hcursorBounds
  have hgrowth := growth_tail_steps store (UInt32.ofNat layout.size) finish base
    (UInt32.ofNat (frontier + (layout.alignment - 1))) 1 [] [] calls
    h32 hcap hpages hsigned
  let grown : MachineStore α :=
    { store with wasm := { store.wasm with mem := grownMemory store.wasm.mem finish } }
  have hcursorGrown : allocatorCursor.toNat + 4 ≤ grown.wasm.mem.pages * 65536 := by
    exact hcursorBounds.trans (Nat.mul_le_mul_right 65536 (Nat.le_max_left _ _))
  have hcommit := commit_steps grown store.wasm.mem.pages.toUInt32 finish base
    (allocatorRequiredPages finish) calls hcursorGrown
  simpa only [bodyTrace, List.append_assoc, grown, finalStore,
    func5Def, Function.toLocals, allocatorLocals, List.map_cons, List.map_nil,
    ValueType.zero] using hprefix.trans (hgrowth.trans hcommit)

private theorem bodyTrace_length_le (memory : Mem) (finish : UInt32) :
    (bodyTrace memory finish).length ≤ 54 := by
  by_cases h : memory.pages < (allocatorRequiredPages finish).toNat <;>
    simp [bodyTrace, growthTrace, h, arithmeticPrefix, commitTail, allocatorGrowSuffix]

private theorem bodyTrace_growth (memory : Mem) (finish : UInt32) :
    ∀ kind ∈ bodyTrace memory finish, GrowthCostKind kind := by
  by_cases h : memory.pages < (allocatorRequiredPages finish).toNat <;>
    simp [bodyTrace, growthTrace, h, arithmeticPrefix, commitTail,
      allocatorGrowSuffix, GrowthCostKind, PrimaryMemoryKind]

/-- Successful arithmetic plus the current physical cap gives an actual
finite normal execution of the complete compiled allocator body.  The step
bound counts small steps, not the byte-weighted cost of memory growth. -/
theorem func5_body_normal_return
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length ≤ 55 ∧ Steps
      ⟨.running ⟨func5Def.toLocals
          [.i32 (UInt32.ofNat layout.size), .i32 (UInt32.ofNat layout.alignment)],
        func5Def.body, 1, [], [], []⟩, store⟩ trace
      ⟨.done [.i32 base], finalStore store finish⟩ := by
  have h32 : store.runtime.currentModule.memIs64 = false := by rw [hmodule]; rfl
  have hpagesWord : store.wasm.mem.pages < UInt32.size := by
    exact hpages.trans_lt (by decide)
  refine ⟨bodyTrace store.wasm.mem finish ++ [.administrative .finish], ?_, ?_⟩
  · have hlen := bodyTrace_length_le store.wasm.mem finish
    simpa only [List.length_append, List.length_cons, List.length_nil] using
      Nat.add_le_add_right hlen 1
  · exact (body_steps store layout frontier storedCursor base finish [] h32 hcap
      hpagesWord halignment hclassify hcursor heffective hcursorBounds).trans
        (Steps.single Step.finish)

/-- The actual absolute-index-8 call returns the computed pointer to an arbitrary
caller and preserves its operand-stack tail, control frames and outer calls.
This includes function entry and the administrative return transition. -/
theorem func5_call_normal_return_trace
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length ≤ 56 ∧ Steps
      ⟨.running ⟨{ callerLocals with values := (.i32 (UInt32.ofNat layout.alignment) ::
          .i32 (UInt32.ofNat layout.size) :: stack) },
        .call 8 :: code, arity, remainder, controls, calls⟩, store⟩ trace
      ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
        code, arity, remainder, controls, calls⟩, finalStore store finish⟩ ∧
      (∀ kind ∈ trace, GrowthCostKind kind) := by
  let caller : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := store.runtime.entry }
  have h32 : store.runtime.currentModule.memIs64 = false := by rw [hmodule]; rfl
  have hpagesWord : store.wasm.mem.pages < UInt32.size :=
    hpages.trans_lt (by decide)
  have hbody := body_steps store layout frontier storedCursor base finish
    (caller :: calls) h32 hcap hpagesWord halignment hclassify hcursor heffective hcursorBounds
  have hcall : Step
      ⟨.running ⟨{ callerLocals with values := (.i32 (UInt32.ofNat layout.alignment) ::
          .i32 (UInt32.ofNat layout.size) :: stack) },
        .call 8 :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.call 8))
      ⟨.running ⟨func5Def.toLocals
          [.i32 (UInt32.ofNat layout.size), .i32 (UInt32.ofNat layout.alignment)],
        func5Def.body, 1, [], [], caller :: calls⟩, store⟩ := by
    exact Step.call (by rw [hmodule]; decide) (by rw [hmodule]; rfl)
  have hreturn : Step
      ⟨.running ⟨{ allocatorLocals store.wasm.mem.pages.toUInt32 finish base
          (allocatorRequiredPages finish) with values := [.i32 base] },
        [], 1, [], [], caller :: calls⟩, finalStore store finish⟩
      (.administrative .returnFromCall)
      ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
        code, arity, remainder, controls, calls⟩, finalStore store finish⟩ := by
    exact Step.returnFromCallFallthrough rfl
  refine ⟨.instruction (.call 8) ::
    (bodyTrace store.wasm.mem finish ++ [.administrative .returnFromCall]), ?_,
      Steps.cons hcall (hbody.trans (Steps.single hreturn)), ?_⟩
  · have hlen := bodyTrace_length_le store.wasm.mem finish
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  · intro kind member
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with rfl | member | rfl
    · trivial
    · exact bodyTrace_growth _ _ kind member
    · trivial

/-- Compatibility projection retaining the original caller contract. -/
theorem func5_call_normal_return
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length ≤ 56 ∧ Steps
      ⟨.running ⟨{ callerLocals with values := (.i32 (UInt32.ofNat layout.alignment) ::
          .i32 (UInt32.ofNat layout.size) :: stack) },
        .call 8 :: code, arity, remainder, controls, calls⟩, store⟩ trace
      ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
        code, arity, remainder, controls, calls⟩, finalStore store finish⟩ := by
  obtain ⟨trace, bound, execution, _⟩ := func5_call_normal_return_trace
    store layout frontier storedCursor base finish callerLocals stack code arity
    remainder controls calls hmodule hcap hpages halignment hclassify hcursor
    heffective hcursorBounds
  exact ⟨trace, bound, execution⟩

@[simp] theorem finalStore_cursor {α : Type} (store : MachineStore α) (finish : UInt32) :
    (finalStore store finish).wasm.mem.read32 allocatorCursor = finish :=
  Mem.read32_write32_same _ _ _

@[simp] theorem finalStore_pages {α : Type} (store : MachineStore α) (finish : UInt32) :
    (finalStore store finish).wasm.mem.pages =
      max store.wasm.mem.pages (allocatorRequiredPages finish).toNat := by rfl

@[simp] theorem finalStore_memoryCaps {α : Type} (store : MachineStore α) (finish : UInt32) :
    (finalStore store finish).wasm.memoryCaps = store.wasm.memoryCaps := by rfl

theorem finalStore_pages_le_cap {α : Type} (store : MachineStore α) (finish : UInt32)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hfinish : finish.toNat < 2147483648) :
    (finalStore store finish).wasm.mem.pages ≤ Module.memoryHardCap := by
  rw [finalStore_pages]
  exact max_le hpages
    ((allocatorRequiredPages_le_signedLimit finish hfinish).trans (by decide))

theorem finalStore_covers_finish {α : Type} (store : MachineStore α) (finish : UInt32)
    (hfinish : finish.toNat < 2147483648) :
    finish.toNat ≤ (finalStore store finish).wasm.mem.pages * 65536 := by
  rw [finalStore_pages]
  exact (allocatorRequiredPages_covers finish hfinish).trans
    (Nat.mul_le_mul_right 65536 (Nat.le_max_right _ _))

/-- The same actual normal-return execution bounds physical memory at every
prefix, including prefixes inside the allocator's measurement/growth sequence.
The endpoint is the caller's resumption, before any caller instruction executes.
The bound is exact: the endpoint reaches the stated maximum page count. -/
theorem func5_call_peak_pages
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    let initial : Config α :=
      ⟨.running ⟨{ callerLocals with values := (.i32 (UInt32.ofNat layout.alignment) ::
          .i32 (UInt32.ofNat layout.size) :: stack) },
        .call 8 :: code, arity, remainder, controls, calls⟩, store⟩
    ∃ trace, trace.length ≤ 56 ∧ Steps initial trace
      ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
        code, arity, remainder, controls, calls⟩, finalStore store finish⟩ ∧
      ∀ (partialTrace : List StepKind) (middle : Config α),
        Steps initial partialTrace middle → partialTrace.length ≤ trace.length →
          store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
          middle.store.wasm.mem.pages ≤
            max store.wasm.mem.pages (allocatorRequiredPages finish).toNat := by
  dsimp only
  obtain ⟨trace, bound, execution, allowed⟩ := func5_call_normal_return_trace
    store layout frontier storedCursor base finish callerLocals stack code arity
    remainder controls calls hmodule hcap hpages halignment hclassify hcursor
    heffective hcursorBounds
  refine ⟨trace, bound, execution, ?_⟩
  intro partialTrace middle partialExecution lengthBound
  exact execution.primary_pages_at_prefix partialExecution lengthBound
    (fun kind member => (allowed kind member).primary)

/-- The allocator charges its actual added physical bytes, including a
page-crossing allocation. It does not assign unit cost to memory growth. -/
theorem func5_call_byteWork
    {α : Type} (store : MachineStore α) (layout : AllocLayout)
    (frontier : Nat) (storedCursor base finish : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor = storedCursor)
    (heffective : (if storedCursor ≠ 0 then storedCursor else heapBase) =
      UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length ≤ 56 ∧ CostedSteps (byteWork hostBytes)
      ⟨.running ⟨{ callerLocals with values := (.i32 (UInt32.ofNat layout.alignment) ::
          .i32 (UInt32.ofNat layout.size) :: stack) },
        .call 8 :: code, arity, remainder, controls, calls⟩, store⟩ trace
      ⟨.running ⟨{ callerLocals with values := .i32 base :: stack },
        code, arity, remainder, controls, calls⟩, finalStore store finish⟩
      (trace.length + 65536 *
        ((allocatorRequiredPages finish).toNat - store.wasm.mem.pages)) := by
  obtain ⟨trace, bound, execution, allowed⟩ := func5_call_normal_return_trace
    store layout frontier storedCursor base finish callerLocals stack code arity
    remainder controls calls hmodule hcap hpages halignment hclassify hcursor
    heffective hcursorBounds
  refine ⟨trace, bound, ?_⟩
  have annotated := execution.growth_byteWork allowed hostBytes
  have delta : max store.wasm.mem.pages (allocatorRequiredPages finish).toNat -
      store.wasm.mem.pages =
      (allocatorRequiredPages finish).toNat - store.wasm.mem.pages := by omega
  simpa only [finalStore_pages, delta] using annotated

private def pageBoundaryStore : MachineStore Universal.State :=
  let m := Project.Mergesort.module
  { runtime := { instances := #[{ module := m, host := Universal.envFor m }], entry := ⟨0⟩ }
    wasm := { mem := Mem.empty 17, globals := ⟨[]⟩, host := default, memoryCaps := [Module.memoryHardCap] } }

private def pageBoundaryCall : Config Universal.State :=
  ⟨.running ⟨⟨[], [], [.i32 4, .i32 65536]⟩,
      [.call 8, .drop, .const 1, .memoryGrow], 0, [], [], []⟩, pageBoundaryStore⟩

set_option maxRecDepth 65536 in
/-- A real allocator call crosses 17 to 18 pages. A later caller growth
reaches 19 pages and is outside the allocator's certified prefix interval. -/
theorem page_boundary_runner :
    (runSteps 56 pageBoundaryCall).result.finalConfig?.map
      (fun config => config.store.wasm.mem.pages) = some 18 ∧
    (runSteps 59 pageBoundaryCall).result.finalConfig?.map
      (fun config => config.store.wasm.mem.pages) = some 19 := by
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 65536 in
/-- The symbolic all-prefix theorem applies to that same page-crossing call. -/
theorem page_boundary_peak :
    ∃ trace, trace.length ≤ 56 ∧ Steps pageBoundaryCall trace
      ⟨.running ⟨⟨[], [], [.i32 heapBase]⟩,
          [.drop, .const 1, .memoryGrow], 0, [], [], []⟩,
        finalStore pageBoundaryStore 1115072⟩ ∧
      ∀ (partialTrace : List StepKind) (middle : Config Universal.State),
        Steps pageBoundaryCall partialTrace middle → partialTrace.length ≤ trace.length →
          17 ≤ middle.store.wasm.mem.pages ∧ middle.store.wasm.mem.pages ≤ 18 := by
  exact func5_call_peak_pages pageBoundaryStore { size := 65536, alignment := 4 }
    heapBase.toNat 0 heapBase 1115072 ⟨[], [], []⟩ []
    [.drop, .const 1, .memoryGrow] 0 [] [] []
    rfl rfl (by decide) (Or.inr rfl) (by decide) rfl rfl (by decide)

set_option maxRecDepth 65536 in
/-- Added memory contributes 65,536 work units in addition to at most 56
semantic transitions. Host charging is arbitrary because this trace has no host call. -/
theorem page_boundary_work (hostBytes : Config Universal.State → Nat →
    Config Universal.State → Nat) :
    ∃ trace amount, CostedSteps (byteWork hostBytes) pageBoundaryCall trace
      ⟨.running ⟨⟨[], [], [.i32 heapBase]⟩,
          [.drop, .const 1, .memoryGrow], 0, [], [], []⟩,
        finalStore pageBoundaryStore 1115072⟩ amount ∧ amount ≤ 65592 := by
  obtain ⟨trace, bound, execution⟩ := func5_call_byteWork pageBoundaryStore
    { size := 65536, alignment := 4 } heapBase.toNat 0 heapBase 1115072
    ⟨[], [], []⟩ [] [.drop, .const 1, .memoryGrow] 0 [] [] []
    rfl rfl (by decide) (Or.inr rfl) (by decide) rfl rfl (by decide) hostBytes
  exact ⟨trace, _, execution, by change trace.length + 65536 * (18 - 17) ≤ 65592; omega⟩

end Project.Mergesort.AllocatorExecution
