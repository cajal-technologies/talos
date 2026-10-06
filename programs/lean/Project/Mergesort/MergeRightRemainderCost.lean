import Project.Mergesort.SortProof
import CodeLib.SepLogic.CostedLoop

/-! # Scalar work of the generated right-remainder loop -/

namespace Project.Mergesort.MergeRightRemainderCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof

structure RemainderState where
  source : UInt32
  scratch : UInt32
  length : UInt32
  scratchLength : UInt32
  mid : UInt32
  count : UInt32
  aux6 : UInt32
  rightLength : UInt32
  readPtr : UInt32
  writePtr : UInt32
  counter : UInt32
  limit : UInt32
  aux12 : UInt32

structure Context where
  stack : List Value := []
  arity : Nat := 0
  remainder : List Value := []
  continuation : Program := []
  controls : List ControlFrame := []
  calls : List CallFrame := []

def locals (v : RemainderState) (stack : List Value) : Locals :=
  sortLocals v.source v.scratch v.length v.scratchLength v.mid v.count
    v.aux6 v.rightLength v.readPtr v.writePtr v.counter v.limit v.aux12 stack

def loopFrame (ctx : Context) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := mergeRightLoopBody, continuation := ctx.continuation,
    belowStack := ctx.stack }

def head (store : MachineStore α) (v : RemainderState) (ctx : Context) : Config α :=
  ⟨.running ⟨locals v ctx.stack, mergeRightLoopBody, ctx.arity, ctx.remainder,
    loopFrame ctx :: ctx.controls, ctx.calls⟩, store⟩

def nextState (v : RemainderState) : RemainderState :=
  { v with
    count := 1 + v.count
    readPtr := 4 + v.readPtr
    writePtr := 4 + v.writePtr
    counter := 1 + v.counter }

def nextStore (store : MachineStore α) (v : RemainderState) : MachineStore α :=
  { store with wasm := { store.wasm with
    mem := store.wasm.mem.write32 (v.writePtr + 0) (store.wasm.mem.read32 (v.readPtr + 0)) } }

private def iterationPrefixTrace : List StepKind :=
  [.instruction (.localGet 11), .instruction (.localGet 5), .instruction .eq,
    .instruction (.br_if 3), .instruction (.localGet 9), .instruction (.localGet 8),
    .instruction (.load32 0), .instruction (.store32 0), .instruction (.localGet 9),
    .instruction (.const 4), .instruction .add, .instruction (.localSet 9),
    .instruction (.localGet 8), .instruction (.const 4), .instruction .add,
    .instruction (.localSet 8), .instruction (.localGet 5), .instruction (.const 1),
    .instruction .add, .instruction (.localSet 5), .instruction (.localGet 10),
    .instruction (.const 1), .instruction .add, .instruction (.localTee 10)]

/-- All scalar operations before the loop branch, including the actual word
copy and updated pointer/counter locals. Physical bounds apply to this store. -/
theorem iteration_prefix_cost (store : MachineStore α) (v : RemainderState)
    (ctx : Context) (hguard : v.limit ≠ v.count)
    (hread : v.readPtr.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hwrite : v.writePtr.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) (head store v ctx) iterationPrefixTrace
      ⟨.running ⟨locals (nextState v) (.i32 (1 + v.counter) :: ctx.stack),
        [.br_if 0], ctx.arity, ctx.remainder,
        loopFrame ctx :: ctx.controls, ctx.calls⟩, nextStore store v⟩ 24 := by
  apply Steps.with_unit_cost
  · unfold head
    rw [mergeRightLoopBody_shape]
    wasm_steps [(.localGet rfl), (.localGet rfl), (.eq (result := 0) (by simp [hguard])),
      .brIfZero, (.localGet rfl), (.localGet rfl),
      (.load32 rfl hread), (.store32 rfl hwrite),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add]
    exact Steps.single (.localTee rfl)
  · intro before kind after member
    simp only [iterationPrefixTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl

/-- A nonzero updated counter takes the actual back-edge in twenty-five
transitions, retaining the copied store and all enclosing caller context. -/
theorem iteration_continue_cost (store : MachineStore α) (v : RemainderState)
    (ctx : Context) (hguard : v.limit ≠ v.count)
    (hread : v.readPtr.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hwrite : v.writePtr.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hcontinue : 1 + v.counter ≠ 0)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 25 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        (head (nextStore store v) (nextState v) ctx) 25 := by
  have prefixCost := iteration_prefix_cost store v ctx hguard hread hwrite hostBytes
  have branch : Steps
      ⟨.running ⟨locals (nextState v) (.i32 (1 + v.counter) :: ctx.stack),
        [.br_if 0], ctx.arity, ctx.remainder,
        loopFrame ctx :: ctx.controls, ctx.calls⟩, nextStore store v⟩
      [.instruction (.br_if 0)] (head (nextStore store v) (nextState v) ctx) := by
    exact Steps.single (Step.brIf hcontinue rfl)
  have branchCost := branch.with_unit_cost (charge := byteWork hostBytes) (by
    intro before kind after member
    simp only [List.mem_singleton] at member
    subst kind
    rfl)
  refine ⟨iterationPrefixTrace ++ [.instruction (.br_if 0)], rfl, ?_⟩
  exact prefixCost.trans branchCost

/-- A zero updated counter exits the loop and resumes its saved continuation.
The final iteration plus its administrative loop exit costs twenty-six units. -/
theorem iteration_exit_cost (store : MachineStore α) (v : RemainderState)
    (ctx : Context) (hguard : v.limit ≠ v.count)
    (hread : v.readPtr.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hwrite : v.writePtr.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hfinal : 1 + v.counter = 0)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 26 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        ⟨.running ⟨locals (nextState v) ctx.stack,
          ctx.continuation, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩,
          nextStore store v⟩ 26 := by
  have prefixCost := iteration_prefix_cost store v ctx hguard hread hwrite hostBytes
  have branch : Steps
      ⟨.running ⟨locals (nextState v) (.i32 (1 + v.counter) :: ctx.stack),
        [.br_if 0], ctx.arity, ctx.remainder,
        loopFrame ctx :: ctx.controls, ctx.calls⟩, nextStore store v⟩
      [.instruction (.br_if 0), .administrative .exitControl]
      ⟨.running ⟨locals (nextState v) ctx.stack,
        ctx.continuation, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩,
        nextStore store v⟩ := by
    rw [hfinal]
    apply Steps.cons Step.brIfZero
    exact Steps.single (Step.exitControl rfl)
  have branchCost := branch.with_unit_cost (charge := byteWork hostBytes) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)
  refine ⟨iterationPrefixTrace ++ [.instruction (.br_if 0),
    .administrative .exitControl], rfl, ?_⟩
  exact prefixCost.trans branchCost

/-- The exact machine locals after all requested words have been copied. -/
def finishedState (v : RemainderState) (remaining : Nat) : RemainderState :=
  { v with
    count := UInt32.ofNat (v.count.toNat + remaining)
    readPtr := UInt32.ofNat (v.readPtr.toNat + 4 * remaining)
    writePtr := UInt32.ofNat (v.writePtr.toNat + 4 * remaining)
    counter := 0 }

def resumed (store : MachineStore α) (v : RemainderState) (ctx : Context) : Config α :=
  ⟨.running ⟨locals v ctx.stack, ctx.continuation,
    ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

theorem nextStore_pages (store : MachineStore α) (v : RemainderState) :
    (nextStore store v).wasm.mem.pages = store.wasm.mem.pages := rfl

private theorem counter_successor (v : RemainderState) (remaining : Nat)
    (hcounter : v.counter = 0 - UInt32.ofNat (remaining + 1)) :
    (nextState v).counter = 0 - UInt32.ofNat remaining := by
  change 1 + v.counter = _
  rw [UInt32.add_comm, hcounter, ← UInt32.ofNat_succ, UInt32.zero_sub,
    UInt32.zero_sub, UInt32.neg_add, UInt32.sub_add_cancel]

private theorem negative_counter_ne_zero (remaining : Nat)
    (hpositive : 0 < remaining) (hsize : remaining < UInt32.size) :
    (0 - UInt32.ofNat remaining : UInt32) ≠ 0 := by
  intro zero
  have cancel : (0 - UInt32.ofNat remaining : UInt32) + UInt32.ofNat remaining = 0 :=
    UInt32.sub_add_cancel _ _
  rw [zero, UInt32.zero_add] at cancel
  have equal := congrArg UInt32.toNat cancel
  rw [UInt32.toNat_ofNat_of_lt' hsize] at equal
  change remaining = 0 at equal
  omega

/-- Natural-count composition of the actual right remainder loop. All future
guards, memory bounds and counter branches are derived from these initial
ranges. No future iteration certificate is assumed. The exact work includes
the final administrative loop exit. -/
theorem loop_exact_cost (store : MachineStore α) (v : RemainderState)
    (ctx : Context) (remaining : Nat) (hpositive : 0 < remaining)
    (hcounter : v.counter = 0 - UInt32.ofNat remaining)
    (hcount : v.count.toNat + remaining ≤ v.limit.toNat)
    (hreadWrap : v.readPtr.toNat + 4 * remaining < UInt32.size)
    (hwriteWrap : v.writePtr.toNat + 4 * remaining < UInt32.size)
    (hread : v.readPtr.toNat + 4 * remaining ≤ store.wasm.mem.pages * 65536)
    (hwrite : v.writePtr.toNat + 4 * remaining ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace finalStore, trace.length = 25 * remaining + 1 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        (resumed finalStore (finishedState v remaining) ctx) (25 * remaining + 1) ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages ∧
      finalStore = { store with wasm := { store.wasm with mem := finalStore.wasm.mem } } := by
  induction remaining generalizing store v with
  | zero => omega
  | succ remaining ih =>
    have hguard : v.limit ≠ v.count := by
      intro equality
      have equal := congrArg UInt32.toNat equality
      omega
    have hreadOne : v.readPtr.toNat + 4 ≤ store.wasm.mem.pages * 65536 := by omega
    have hwriteOne : v.writePtr.toNat + 4 ≤ store.wasm.mem.pages * 65536 := by omega
    have hcountStep : (nextState v).count.toNat = v.count.toNat + 1 := by
      change (1 + v.count).toNat = _
      rw [UInt32.toNat_add]
      change (1 + v.count.toNat) % UInt32.size = _
      rw [Nat.mod_eq_of_lt (by have := v.limit.toNat_lt_size; omega)]
      omega
    have hreadStep : (nextState v).readPtr.toNat = v.readPtr.toNat + 4 := by
      change (4 + v.readPtr).toNat = _
      rw [UInt32.toNat_add]
      change (4 + v.readPtr.toNat) % UInt32.size = _
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hwriteStep : (nextState v).writePtr.toNat = v.writePtr.toNat + 4 := by
      change (4 + v.writePtr).toNat = _
      rw [UInt32.toNat_add]
      change (4 + v.writePtr.toNat) % UInt32.size = _
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hnextCounter := counter_successor v remaining hcounter
    by_cases last : remaining = 0
    · subst remaining
      have finalCounter : 1 + v.counter = 0 := by
        exact hnextCounter
      obtain ⟨trace, hlength, execution⟩ := iteration_exit_cost store v ctx
        hguard hreadOne hwriteOne finalCounter hostBytes
      have finalLocals : nextState v = finishedState v 1 := by
        have hc : (nextState v).count = UInt32.ofNat (v.count.toNat + 1) := by
          rw [← hcountStep, UInt32.ofNat_toNat]
        have hr : (nextState v).readPtr = UInt32.ofNat (v.readPtr.toNat + 4) := by
          rw [← hreadStep, UInt32.ofNat_toNat]
        have hw : (nextState v).writePtr = UInt32.ofNat (v.writePtr.toNat + 4) := by
          rw [← hwriteStep, UInt32.ofNat_toNat]
        simp only [nextState] at hc hr hw
        simp only [nextState, finishedState, Nat.mul_one, hc, hr, hw, finalCounter]
      refine ⟨trace, nextStore store v, hlength, ?_, rfl, rfl⟩
      simpa only [finalLocals, resumed] using execution
    · have positive : 0 < remaining := by omega
      have nonzero : 1 + v.counter ≠ 0 := by
        change (nextState v).counter ≠ 0
        rw [hnextCounter]
        exact negative_counter_ne_zero remaining positive (by omega)
      obtain ⟨first, hfirst, firstCost⟩ := iteration_continue_cost store v ctx
        hguard hreadOne hwriteOne nonzero hostBytes
      obtain ⟨tail, finalStore, htail, tailCost, hpages, hframe⟩ :=
        ih (nextStore store v) (nextState v) positive hnextCounter
          (by change (nextState v).count.toNat + remaining ≤ v.limit.toNat
              rw [hcountStep]; omega)
          (by rw [hreadStep]; omega)
          (by rw [hwriteStep]; omega)
          (by rw [hreadStep, nextStore_pages]; omega)
          (by rw [hwriteStep, nextStore_pages]; omega)
      have finalLocals : finishedState (nextState v) remaining =
          finishedState v (remaining + 1) := by
        unfold finishedState
        rw [hcountStep, hreadStep, hwriteStep]
        have hc : v.count.toNat + 1 + remaining = v.count.toNat + (remaining + 1) := by omega
        have hr : v.readPtr.toNat + 4 + 4 * remaining =
            v.readPtr.toNat + 4 * (remaining + 1) := by omega
        have hw : v.writePtr.toNat + 4 + 4 * remaining =
            v.writePtr.toNat + 4 * (remaining + 1) := by omega
        rw [hc, hr, hw]
        rfl
      refine ⟨first ++ tail, finalStore, ?_, ?_,
        hpages.trans (nextStore_pages store v), ?_⟩
      · simp only [List.length_append, hfirst, htail]
        omega
      · have result := firstCost.trans tailCost
        rw [finalLocals] at result
        convert result using 1
        omega
      · exact hframe

end Project.Mergesort.MergeRightRemainderCost
