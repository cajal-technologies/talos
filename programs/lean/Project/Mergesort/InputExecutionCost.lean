import Project.Mergesort.InputLoopCost
import Project.Mergesort.InputReserveResources
import Project.Mergesort.InputWorkBudget

/-! # Composing the actual input iterations and their numerical work -/

namespace Project.Mergesort.InputExecutionCost

open Wasm Wasm.SmallStep Wasm.SmallStep.CostedStdIO
open Project.Mergesort.DriverProof Project.Mergesort.Representations
open Project.Mergesort.InputCost Project.Mergesort.InputControlCost
open Project.Mergesort.InputLoopCost
open Project.Mergesort.MemoryBounds

/-- Non-memory fields needed when the generated caller resumes. -/
structure Frame (before after : MachineStore Universal.State) : Prop where
  runtime : after.runtime = before.runtime
  globals : after.wasm.globals = before.wasm.globals
  globalIds : after.wasm.globalIds = before.wasm.globalIds
  memoryCaps : after.wasm.memoryCaps = before.wasm.memoryCaps
  memoryIds : after.wasm.memoryIds = before.wasm.memoryIds

theorem Frame.refl (store : MachineStore Universal.State) : Frame store store :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {a b c : MachineStore Universal.State} (h : Frame a b) (g : Frame b c) :
    Frame a c := ⟨g.runtime.trans h.runtime, g.globals.trans h.globals,
      g.globalIds.trans h.globalIds, g.memoryCaps.trans h.memoryCaps,
      g.memoryIds.trans h.memoryIds⟩

structure IterationResult (total : Nat) (before : MachineStore Universal.State)
    (v : State) (aux : Aux) (ctx : Context) where
  store : MachineStore Universal.State
  state : State
  trace : List StepKind
  amount : Nat
  run : CostedSteps work (head before (stateLocals v aux) ctx) trace
    (afterClassify store (stateLocals state aux) (if state.current = 0 then 1 else 0) ctx) amount
  invariant : Invariant total store state
  current : state.current = min 256 before.wasm.host.stdio.input.length
  input : store.wasm.host.stdio.input =
    before.wasm.host.stdio.input.drop (min 256 before.wasm.host.stdio.input.length)
  capacity : v.capacity.toNat ≤ state.capacity.toNat
  pages : before.wasm.mem.pages ≤ store.wasm.mem.pages
  charge : amount + 2 ≤ 259 + v.current + state.current +
    (state.capacity.toNat - v.capacity.toNat) +
    65536 * (store.wasm.mem.pages - before.wasm.mem.pages)
  frame : Frame before store

/-- The already-fitting path executes from concrete invariant facts. -/
theorem fitting_step (total : Nat) (store : MachineStore Universal.State)
    (v : State) (aux : Aux) (ctx : Context)
    (h : Invariant total store v) (hpositive : 0 < v.current)
    (hfits : v.current ≤ v.capacity.toNat - v.length) :
    Nonempty (IterationResult total store v aux ctx) := by
  have hcurrent : v.current ≤ 256 := h.chunk_shape ▸ min_le_left _ _
  have hword : v.dataPtr.toNat + v.length < UInt32.size := by
    have := h.allocation_frontier
    have := h.frontier_signed
    have := h.length_capacity
    norm_num [UInt32.size]
    omega
  have hdestination : (v.dataPtr + UInt32.ofNat v.length).toNat + v.current ≤
      store.wasm.mem.pages * 65536 := by
    rw [byteOffset_toNat v.dataPtr v.length hword]
    have := h.allocation_frontier
    have := h.frontier_physical
    have := h.length_capacity
    omega
  obtain ⟨trace, htrace, run⟩ := fitting_iteration_cost store v.dataPtr v.capacity v.length v.current
    aux.aux2 aux.aux4 aux.aux5 aux.aux7 aux.aux8 aux.aux9 aux.aux10 ctx
    hpositive hcurrent h.header_capacity ((capacity_test h).mpr hfits) hdestination
    (fixed_ranges h).1 h.module h.host
  refine ⟨{
    store := fittingStore store v, state := fittingState store v, trace := trace,
    amount := 42 + v.current + readCount store 256,
    run := run, invariant := fitting_invariant h hpositive hfits,
    current := rfl, input := fittingStore_input store v,
    capacity := Nat.le_refl _, pages := Nat.le_refl _, charge := ?_,
    frame := ⟨rfl, rfl, rfl, rfl, rfl⟩ }⟩
  change 42 + v.current + readCount store 256 + 2 ≤
    259 + v.current + readCount store 256 + (_ - _) + 65536 * (_ - _)
  omega

set_option maxRecDepth 65536 in
/-- The non-fitting path executes reserve, reload, append and next host read.
All arithmetic and physical allocator premises come from the loop invariant
and input-size bound. -/
theorem reserve_step (total : Nat) (store : MachineStore Universal.State)
    (v : State) (aux : Aux) (ctx : Context)
    (h : Invariant total store v) (hpositive : 0 < v.current)
    (hnonfit : v.capacity.toNat < v.length + v.current)
    (hfit : WorkArraysFit total) :
    Nonempty (IterationResult total store v aux ctx) := by
  let selected := selectedCapacity v.length v.current v.capacity.toNat
  let base := UInt32.ofNat v.frontier
  let finish := UInt32.ofNat (v.frontier + selected)
  have hclassify : classifyBump v.frontier { size := selected, alignment := 1 } =
      .success base finish := MemoryBounds.BoundedGeometricVecFacts.reserve_classify_success
    total v.length v.current store.wasm.host.stdio.input.length v.capacity v.dataPtr
    v.frontier v.history h.lineage hpositive hnonfit hfit
  obtain ⟨history, hhistory⟩ := reserve_history_exists h hpositive base
    { size := selected, alignment := 1 }
  let grown := InputReserveResources.reservedStore store v base finish
  let next := InputReserveResources.reservedState v base finish history
  obtain ⟨hinvariant, hdoubled, hpages⟩ := InputReserveResources.reserve_invariant
    h hpositive hnonfit base finish history hclassify hhistory
  change 2 * v.capacity.toNat ≤ next.capacity.toNat at hdoubled
  change store.wasm.mem.pages ≤ grown.wasm.mem.pages at hpages
  have hcurrent : v.current ≤ 256 := h.chunk_shape ▸ min_le_left _ _
  have hcurrentNat : (UInt32.ofNat v.current).toNat = v.current :=
    UInt32.toNat_ofNat_of_lt' (by norm_num [UInt32.size]; omega)
  have hlengthNat : (UInt32.ofNat v.length).toNat = v.length :=
    UInt32.toNat_ofNat_of_lt' (lt_of_le_of_lt h.length_capacity v.capacity.toNat_lt)
  obtain ⟨htotalWord, hselectedWord, hvalid⟩ := GeometricVecFacts.reserveLayout
    total v.length (v.current + store.wasm.host.stdio.input.length) v.current
    v.capacity v.dataPtr v.frontier v.history h.lineage.1 h.chunk_shape hpositive
  have hfresh := geometricVec_frontier_ge_heapBase _ _ _ _ _ _ _ h.lineage
  have hframe := ReserveCostResources.finalStore_frame store v.capacity v.dataPtr
    (UInt32.ofNat selected) base finish
  have hruntime : grown.runtime = store.runtime := hframe.1
  have hhostState : grown.wasm.host = store.wasm.host := hframe.2.2.2.1
  have hgpages : grown.wasm.mem.pages = max store.wasm.mem.pages (allocatorRequiredPages finish).toNat :=
    ReserveCostResources.finalStore_pages _ _ _ _ _ _
  have hphysical : driverBase.toNat + 12 ≤ store.wasm.mem.pages * 65536 :=
    le_trans (by decide : driverBase.toNat + 12 ≤ (driverBase + 12).toNat + 256) (fixed_ranges h).1
  have hgphysical : driverBase.toNat + 12 ≤ grown.wasm.mem.pages * 65536 :=
    hphysical.trans (Nat.mul_le_mul_right 65536 hpages)
  have hcursorBase : allocatorCursor.toNat + 4 ≤ base.toNat := by
    have hb := (classifyBump_success_align1 _ _ _ _ hclassify).2.2.1
    have : allocatorCursor.toNat + 4 ≤ heapBase.toNat := by decide
    omega
  have hnotfits : ¬ UInt32.ofNat v.current ≤ v.capacity - UInt32.ofNat v.length := by
    intro hf
    have := (capacity_test h).mp hf
    have := h.length_capacity
    omega
  let code := func3AppendBody ++ (func3ReadClassifyBody ++ [.br_if 2, .br 0])
  let caller : ThreadState Universal.State :=
    ⟨{ stateLocals v aux with values := ctx.stack }, capacityReload, ctx.arity, ctx.remainder,
      capacityFrame ctx.stack code :: loopControls ctx, ctx.calls⟩
  have guard := count_guard_cost store (stateLocals v aux) v.current hcurrent rfl ctx.stack
    (.block 0 0 func3CapacityBody :: code) ctx.arity ctx.remainder (loopControls ctx) ctx.calls
  have setup := capacity_reserve_prefix store (stateLocals v aux)
    (UInt32.ofNat v.current) (UInt32.ofNat v.length) v.capacity rfl rfl rfl h.header_capacity
    (by omega) hnotfits ctx.stack code ctx.arity ctx.remainder (loopControls ctx) ctx.calls
  obtain ⟨reserveTrace, reserveBound, reserveRun⟩ := ReserveCost.reserve_call_byteWork store
    (UInt32.ofNat v.length) (UInt32.ofNat v.current) v.capacity v.dataPtr v.frontier
    v.storedCursor base finish caller h.module h.cap h.pages_upper h.global
    h.header_capacity h.header_pointer hphysical hfresh
    (by simpa only [hlengthNat, hcurrentNat] using hvalid)
    (by simpa only [hlengthNat, hcurrentNat] using hclassify)
    h.cursor h.effective (fixed_ranges h).2
    (h.allocation_frontier.trans h.frontier_physical) CostedStdIO.hostBytes
  simp only [hlengthNat, hcurrentNat] at reserveRun
  have reload := capacity_reserve_suffix grown v.dataPtr base (UInt32.ofNat v.current)
    (UInt32.ofNat v.length) aux.aux2 aux.aux4 aux.aux5 aux.aux7 aux.aux8 aux.aux9 aux.aux10
    (ReserveCostResources.finalStore_pointer _ _ _ _ _ _)
    ((ReserveCostResources.finalStore_length store v.capacity v.dataPtr
      (UInt32.ofNat selected) base finish hcursorBase).trans h.header_length)
    hgphysical ctx.stack code ctx.arity ctx.remainder (loopControls ctx) ctx.calls
  have hbaseNat := (classifyBump_success_align1 _ _ _ _ hclassify).2.2.1
  have hendWord := (classifyBump_success_align1 _ _ _ _ hclassify).2.2.2.1
  have hfinishNat := (classifyBump_success_align1 _ _ _ _ hclassify).2.2.2.2.2
  have hselectedLength : v.length + v.current ≤ selected := by unfold selected selectedCapacity; omega
  have hdestination : (base + UInt32.ofNat v.length).toNat + v.current ≤ grown.wasm.mem.pages * 65536 := by
    rw [byteOffset_toNat base v.length (by omega)]
    have hp := hinvariant.frontier_physical
    change finish.toNat ≤ grown.wasm.mem.pages * 65536 at hp
    omega
  have hgchunk : (driverBase + 12).toNat + 256 ≤ grown.wasm.mem.pages * 65536 :=
    (fixed_ranges h).1.trans (Nat.mul_le_mul_right 65536 hpages)
  obtain ⟨appendTrace, appendLength, appendRun⟩ := append_cost grown base v.length v.current
    aux.aux2 aux.aux4 aux.aux5 aux.aux7 aux.aux8 aux.aux9 aux.aux10 ctx.stack
    (func3ReadClassifyBody ++ [.br_if 2, .br 0]) ctx.arity ctx.remainder (loopControls ctx) ctx.calls
    hpositive (by norm_num [UInt32.size]; omega) hdestination (by omega)
    (by exact le_trans (by decide : (driverBase + 8).toNat + 4 ≤ driverBase.toNat + 12) hgphysical)
  obtain ⟨readTrace, readLength, readRun⟩ := read_classify_cost
    (appendedStore grown base v.length v.current) base (UInt32.ofNat v.current)
    (UInt32.ofNat (v.length + v.current)) aux.aux2 aux.aux4 aux.aux5 aux.aux7 aux.aux8 aux.aux9 aux.aux10
    ctx.stack [.br_if 2, .br 0] ctx.arity ctx.remainder (loopControls ctx) ctx.calls
    (by change grown.runtime.currentModule = _; rw [hruntime]; exact h.module)
    (by change grown.runtime.currentHost = _; rw [hruntime]; exact h.host)
    (by have hc := readCount_bound (appendedStore grown base v.length v.current)
        change (driverBase + 12).toNat + _ ≤ grown.wasm.mem.pages * 65536
        omega)
  have joined := ((((guard.trans setup).trans reserveRun).trans reload).trans appendRun).trans readRun
  have stepRun := joined
  change CostedSteps work (head store (stateLocals v aux) ctx) _
      (afterClassify (fittingStore grown next) (stateLocals (fittingState grown next) aux)
        (if (fittingState grown next).current = 0 then 1 else 0) ctx)
      (4 + 13 + (reserveTrace.length + v.capacity.toNat + 65536 *
        ((allocatorRequiredPages finish).toNat - store.wasm.mem.pages)) + 7 +
        (19 + v.current) + (11 + readCount grown 256)) at stepRun
  refine ⟨{
    store := fittingStore grown next, state := fittingState grown next,
    trace := _, amount := _, run := stepRun, invariant := hinvariant,
    current := ?_, input := ?_, capacity := ?_, pages := hpages, charge := ?_, frame := ?_ }⟩
  · change readCount grown 256 = _
    unfold readCount
    rw [hhostState]
    rfl
  · rw [fittingStore_input]
    unfold readCount
    rw [hhostState]
    rfl
  · change v.capacity.toNat ≤ next.capacity.toNat
    omega
  · change _ ≤ 259 + v.current + readCount grown 256 + (next.capacity.toNat - v.capacity.toNat) +
      65536 * (grown.wasm.mem.pages - store.wasm.mem.pages)
    rw [hgpages]
    have hcopy := InputWorkBudget.reallocation_copy _ _ hdoubled
    have hscalar : reserveTrace.length ≤ 203 := by split_ifs at reserveBound <;> omega
    omega
  · exact ⟨hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.2.1, hframe.2.2.2.2.2⟩

/-- Both concrete branches furnish the next generated iteration. -/
theorem iteration_step (total : Nat) (store : MachineStore Universal.State)
    (v : State) (aux : Aux) (ctx : Context)
    (h : Invariant total store v) (hpositive : 0 < v.current) (hfit : WorkArraysFit total) :
    Nonempty (IterationResult total store v aux ctx) := by
  by_cases hfits : v.current ≤ v.capacity.toNat - v.length
  · exact fitting_step total store v aux ctx h hpositive hfits
  · exact reserve_step total store v aux ctx h hpositive (by have := h.length_capacity; omega) hfit

def done (store : MachineStore Universal.State) (v : State) (aux : Aux) (ctx : Context) :
    Config Universal.State :=
  ⟨.running ⟨{ stateLocals v aux with values := ctx.stack }, ctx.afterLoop,
    ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

structure Result (total : Nat) (before : MachineStore Universal.State)
    (v : State) (aux : Aux) (ctx : Context) where
  store : MachineStore Universal.State
  state : State
  trace : List StepKind
  amount : Nat
  run : CostedSteps work (head before (stateLocals v aux) ctx) trace (done store state aux ctx) amount
  invariant : Invariant total store state
  exhausted : state.current = 0
  capacity : v.capacity.toNat ≤ state.capacity.toNat
  pages : before.wasm.mem.pages ≤ store.wasm.mem.pages
  charge : amount ≤ InputWorkBudget.budget v.current before.wasm.host.stdio.input.length
    v.capacity.toNat before.wasm.mem.pages state.capacity.toNat store.wasm.mem.pages
  frame : Frame before store

/-- Internal induction only. The exported execution theorem below supplies
its per-iteration premise from the concrete capacity branches. -/
private theorem compose_iterations (total : Nat) (aux : Aux) (ctx : Context)
    (iterate : ∀ store v, Invariant total store v → 0 < v.current →
      Nonempty (IterationResult total store v aux ctx))
    (store : MachineStore Universal.State) (v : State)
    (h : Invariant total store v) (hpositive : 0 < v.current) :
    Nonempty (Result total store v aux ctx) := by
  let remaining := v.current + store.wasm.host.stdio.input.length
  generalize heq : remaining = n
  induction n using Nat.strong_induction_on generalizing store v with
  | h n ih =>
    obtain ⟨step⟩ := iterate store v h hpositive
    have hc : min 256 store.wasm.host.stdio.input.length ≤ store.wasm.host.stdio.input.length :=
      min_le_right _ _
    have hremaining : step.state.current + step.store.wasm.host.stdio.input.length =
        store.wasm.host.stdio.input.length := by
      rw [step.current, step.input, List.length_drop]
      omega
    by_cases hz : step.state.current = 0
    · have hinput : store.wasm.host.stdio.input.length = 0 := by
        have hcurrent := step.current
        omega
      have exitRun := eof_exit_cost step.store (stateLocals step.state aux) ctx
      have joined := step.run.trans (by simpa only [if_pos hz] using exitRun)
      refine ⟨{
        store := step.store, state := step.state, trace := _, amount := step.amount + 1,
        run := joined, invariant := step.invariant, exhausted := hz,
        capacity := step.capacity, pages := step.pages, charge := ?_, frame := step.frame }⟩
      rw [hinput, ← InputWorkBudget.finish _ _ _ _ _ hpositive (h.chunk_shape ▸ min_le_left _ _)]
      have hb := step.charge
      rw [hz] at hb
      omega
    · have hnext : 0 < step.state.current := Nat.pos_of_ne_zero hz
      have hsmall : step.state.current + step.store.wasm.host.stdio.input.length < n := by
        change v.current + store.wasm.host.stdio.input.length = n at heq
        omega
      obtain ⟨tail⟩ := ih _ hsmall step.store step.state step.invariant hnext rfl
      have again := continue_cost step.store (stateLocals step.state aux) ctx
      have joined := (step.run.trans (by simpa only [if_neg hz] using again)).trans tail.run
      refine ⟨{
        store := tail.store, state := tail.state, trace := _, amount := step.amount + 2 + tail.amount,
        run := joined, invariant := tail.invariant, exhausted := tail.exhausted,
        capacity := step.capacity.trans tail.capacity, pages := step.pages.trans tail.pages,
        charge := ?_, frame := step.frame.trans tail.frame }⟩
      have arithmetic := InputWorkBudget.step v.current store.wasm.host.stdio.input.length
        v.capacity.toNat store.wasm.mem.pages step.state.capacity.toNat step.store.wasm.mem.pages
        tail.state.capacity.toNat tail.store.wasm.mem.pages hpositive h.chunk_shape
        step.capacity tail.capacity step.pages tail.pages
      have ht := tail.charge
      rw [step.current, step.input, List.length_drop] at ht
      have hb := step.charge
      rw [step.current] at hb
      omega

/-- Complete actual input-loop execution, including every reserve, byte copy,
next read, EOF test and enclosing-block exit. The only global bound premise is
the input-size arithmetic needed to prove each allocator succeeds. -/
theorem loop_cost (total : Nat) (store : MachineStore Universal.State)
    (v : State) (aux : Aux) (ctx : Context)
    (h : Invariant total store v) (hpositive : 0 < v.current) (hfit : WorkArraysFit total) :
    Nonempty (Result total store v aux ctx) :=
  compose_iterations total aux ctx
    (fun currentStore currentState invariant positive =>
      iteration_step total currentStore currentState aux ctx invariant positive hfit)
    store v h hpositive

end Project.Mergesort.InputExecutionCost
