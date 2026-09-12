import Project.Mergesort.MergeRightRemainderCost
import Project.Mergesort.Representations

/-!
# Operational cost of the generated right remainder dispatcher

The branch and scalar setup are executed before applying the checked copying
loop. Initial natural indices discharge its counter, guard and physical range
premises. The endpoint is the actual generated copy-back continuation.
-/

namespace Project.Mergesort.MergeRightDispatcherCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof
open Project.Mergesort.MergeRightRemainderCost
open Project.Mergesort.Representations

def blockFrame (ctx : Context) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := mergeRightRemainderBody, continuation := sortBlock4.drop 7,
    belowStack := ctx.stack }

def inputState (source scratch : UInt32) (n mid j : Nat)
    (aux6 aux8 aux9 aux11 aux12 : UInt32) : RemainderState :=
  { source, scratch, length := UInt32.ofNat n, scratchLength := UInt32.ofNat n,
    mid := UInt32.ofNat mid, count := UInt32.ofNat (mid + j), aux6,
    rightLength := UInt32.ofNat (n - mid), readPtr := aux8, writePtr := aux9,
    counter := UInt32.ofNat j, limit := aux11, aux12 }

def prepared (v : RemainderState) : RemainderState :=
  { v with
    readPtr := v.source + 4 * v.mid + 4 * v.counter
    writePtr := v.scratch + 4 * v.count
    counter := v.mid - v.length + v.counter
    limit := v.scratchLength }

def start (store : MachineStore α) (v : RemainderState) (ctx : Context) : Config α :=
  ⟨.running ⟨locals v ctx.stack, sortBlock4.drop 6,
    ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

def finish (store : MachineStore α) (v : RemainderState) (ctx : Context) : Config α :=
  ⟨.running ⟨locals v ctx.stack, sortBlock4.drop 7,
    ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

def loopContext (ctx : Context) : Context :=
  { ctx with continuation := [], controls := blockFrame ctx :: ctx.controls }

private def setupTrace : List StepKind :=
  [.instruction (.block 0 0 mergeRightRemainderBody),
    .instruction (.localGet 10), .instruction (.localGet 7), .instruction .geU,
    .instruction (.br_if 0), .instruction (.localGet 0), .instruction (.localGet 4),
    .instruction (.const 2), .instruction .shl, .instruction .add,
    .instruction (.localGet 10), .instruction (.const 2), .instruction .shl,
    .instruction .add, .instruction (.localSet 8),
    .instruction (.localGet 5), .instruction (.localGet 3),
    .instruction (.localGet 5), .instruction (.localGet 3), .instruction .gtU,
    .instruction .select, .instruction (.localSet 11),
    .instruction (.localGet 2), .instruction (.localGet 5), .instruction (.const 2),
    .instruction .shl, .instruction .add, .instruction (.localSet 9),
    .instruction (.localGet 4), .instruction (.localGet 1), .instruction .sub,
    .instruction (.localGet 10), .instruction .add, .instruction (.localSet 10),
    .instruction (.loop 0 0 mergeRightLoopBody)]

/-- The actual block entry, two guards, scalar initializers and loop entry.
No body iteration has run at the endpoint. -/
theorem setup_cost (store : MachineStore α) (v : RemainderState) (ctx : Context)
    (hremaining : v.counter < v.rightLength) (hcount : v.count ≤ v.scratchLength)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) (start store v ctx) setupTrace
      (head store (prepared v) (loopContext ctx)) 35 := by
  apply Steps.with_unit_cost
  · unfold start
    change Steps ⟨.running ⟨locals v ctx.stack,
      .block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7,
      ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩ _ _
    wasm_steps [.block]
    rw [mergeRightRemainderBody_shape]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.geU (result := 0) (by simp [UInt32.not_le.mpr hremaining])), .brIfZero,
      (.localGet rfl), (.localGet rfl), .const, .shl]
    rw [MemRegion.shl2_eq_mul4]
    wasm_steps [.add, (.localGet rfl), .const, .shl]
    rw [MemRegion.shl2_eq_mul4]
    wasm_steps [.add, (.localSet rfl), (.localGet rfl), (.localGet rfl),
      (.localGet rfl), (.localGet rfl),
      (.gtU (result := 0) (by simp [UInt32.not_lt.mpr hcount])),
      (.select (selected := .i32 v.scratchLength) (by simp)), (.localSet rfl),
      (.localGet rfl), (.localGet rfl), .const, .shl]
    rw [MemRegion.shl2_eq_mul4]
    wasm_steps [.add, (.localSet rfl), (.localGet rfl), (.localGet rfl),
      .sub, (.localGet rfl), .add, (.localSet rfl)]
    have hr : 4 * v.counter + (4 * v.mid + v.source) =
        v.source + 4 * v.mid + 4 * v.counter := by ac_rfl
    have hw : 4 * v.count + v.scratch = v.scratch + 4 * v.count := by ac_rfl
    have hc : v.counter + (v.mid - v.length) = v.mid - v.length + v.counter := by ac_rfl
    rw [hr, hw, hc]
    exact Steps.single Step.loop
  · intro before kind after member
    simp only [setupTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl

/-- An exhausted right input takes the generated branch out of its block;
it neither executes the loop nor changes the physical store. -/
theorem skip_cost (store : MachineStore α) (v : RemainderState) (ctx : Context)
    (hexhausted : v.rightLength ≤ v.counter)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 5 ∧
      CostedSteps (byteWork hostBytes) (start store v ctx) trace
        (finish store v ctx) 5 := by
  refine ⟨[.instruction (.block 0 0 mergeRightRemainderBody),
    .instruction (.localGet 10), .instruction (.localGet 7),
    .instruction .geU, .instruction (.br_if 0)], rfl, ?_⟩
  apply Steps.with_unit_cost
  · unfold start
    change Steps ⟨.running ⟨locals v ctx.stack,
      .block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7,
      ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩ _ _
    wasm_steps [.block]
    rw [mergeRightRemainderBody_shape]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.geU (result := 1) (by simp [hexhausted]))]
    exact Steps.single (Step.brIf (by decide) rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- All requested right words are copied, then the actual enclosing block exits.
The cost includes every dispatcher and loop transition. -/
theorem positive_cost (store : MachineStore α) (v : RemainderState) (ctx : Context)
    (remaining : Nat) (hpositive : 0 < remaining)
    (hremaining : v.counter < v.rightLength) (hcount : v.count ≤ v.scratchLength)
    (hcounter : (prepared v).counter = 0 - UInt32.ofNat remaining)
    (hlimit : v.count.toNat + remaining ≤ v.scratchLength.toNat)
    (hreadWrap : (prepared v).readPtr.toNat + 4 * remaining < UInt32.size)
    (hwriteWrap : (prepared v).writePtr.toNat + 4 * remaining < UInt32.size)
    (hread : (prepared v).readPtr.toNat + 4 * remaining ≤ store.wasm.mem.pages * 65536)
    (hwrite : (prepared v).writePtr.toNat + 4 * remaining ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace finalStore, trace.length = 25 * remaining + 37 ∧
      CostedSteps (byteWork hostBytes) (start store v ctx) trace
        (finish finalStore (finishedState (prepared v) remaining) ctx)
        (25 * remaining + 37) ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages ∧
      finalStore = { store with wasm := { store.wasm with mem := finalStore.wasm.mem } } := by
  have setup := setup_cost store v ctx hremaining hcount hostBytes
  obtain ⟨loopTrace, finalStore, hlength, loopCost, hpages, hstore⟩ :=
    loop_exact_cost store (prepared v) (loopContext ctx) remaining hpositive hcounter
      hlimit hreadWrap hwriteWrap hread hwrite hostBytes
  have exited : Steps
      (resumed finalStore (finishedState (prepared v) remaining) (loopContext ctx))
      [.administrative .exitControl]
      (finish finalStore (finishedState (prepared v) remaining) ctx) := by
    exact Steps.single (Step.exitControl rfl)
  have exitCost := exited.with_unit_cost (charge := byteWork hostBytes) (by
    intro before kind after member
    simp only [List.mem_singleton] at member
    subst kind
    rfl)
  refine ⟨setupTrace ++ loopTrace ++ [.administrative .exitControl], finalStore,
    ?_, ?_, hpages, hstore⟩
  · simp only [List.length_append, hlength, List.length_cons, List.length_nil]
    change 35 + (25 * remaining + 1) + 1 = _
    omega
  · convert (setup.trans loopCost).trans exitCost using 1
    simp only [List.length_cons, List.length_nil]
    omega

private theorem initial_counter (n mid j : Nat) (hmid : mid ≤ n) (hj : j ≤ n - mid) :
    UInt32.ofNat mid - UInt32.ofNat n + UInt32.ofNat j =
      0 - UInt32.ofNat (n - mid - j) := by
  have sum : mid + j + (n - mid - j) = n := by omega
  calc
    _ = UInt32.ofNat (mid + j) - UInt32.ofNat n := by
      rw [UInt32.ofNat_add, UInt32.sub_eq_add_neg, UInt32.sub_eq_add_neg]
      ac_rfl
    _ = UInt32.ofNat (mid + j) -
        (UInt32.ofNat (mid + j) + UInt32.ofNat (n - mid - j)) := by
      rw [← UInt32.ofNat_add, sum]
    _ = 0 - UInt32.ofNat (n - mid - j) := by
      rw [UInt32.sub_eq_add_neg, UInt32.neg_add, UInt32.sub_eq_add_neg,
        ← UInt32.add_assoc]
      simp only [UInt32.add_neg_eq_sub, UInt32.sub_self]

/-- Natural-index interface for the whole right dispatcher. It derives the
negative counter, future loop guards and pointer ranges from the initial
full-array ranges. The exhausted-right case retains its sharper five-step
cost for composition with a positive left remainder. -/
theorem dispatch_cost (store : MachineStore α) (source scratch : UInt32)
    (n mid j : Nat) (aux6 aux8 aux9 aux11 aux12 : UInt32) (ctx : Context)
    (hmid : mid ≤ n) (hj : j ≤ n - mid)
    (hsourceWrap : source.toNat + 4 * n < UInt32.size)
    (hscratchWrap : scratch.toNat + 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace finalStore v6 v8 v9 v10 v11 v12 amount,
      trace.length = amount ∧ amount ≤ 25 * (n - mid - j) + 37 ∧
      (j = n - mid → amount ≤ 5) ∧
      CostedSteps (byteWork hostBytes)
        (start store (inputState source scratch n mid j aux6 aux8 aux9 aux11 aux12) ctx)
        trace
        ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
          (UInt32.ofNat mid) (UInt32.ofNat n) v6 (UInt32.ofNat (n - mid))
          v8 v9 v10 v11 v12 ctx.stack,
          sortBlock4.drop 7, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩,
          finalStore⟩ amount ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages ∧
      finalStore = { store with wasm := { store.wasm with mem := finalStore.wasm.mem } } := by
  let v := inputState source scratch n mid j aux6 aux8 aux9 aux11 aux12
  have hn : n < UInt32.size := by omega
  have hk : mid + j ≤ n := by omega
  have hkn : (UInt32.ofNat (mid + j)).toNat = mid + j :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  by_cases hexhausted : j = n - mid
  · have hsum : mid + j = n := by omega
    obtain ⟨trace, hlength, execution⟩ := skip_cost store v ctx
      (by simp only [v, inputState, hexhausted, UInt32.le_refl]) hostBytes
    refine ⟨trace, store, aux6, aux8, aux9, UInt32.ofNat j, aux11, aux12,
      5, hlength, by omega, by omega, ?_, rfl, rfl⟩
    simpa only [v, inputState, finish, locals, hsum] using execution
  · have hpositive : 0 < n - mid - j := by omega
    have hremaining : v.counter < v.rightLength := by
      change UInt32.ofNat j < UInt32.ofNat (n - mid)
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by omega : j < UInt32.size),
        UInt32.toNat_ofNat_of_lt' (by omega : n - mid < UInt32.size)]
      omega
    have hcount : v.count ≤ v.scratchLength := by
      change UInt32.ofNat (mid + j) ≤ UInt32.ofNat n
      rw [UInt32.le_iff_toNat_le, hkn, UInt32.toNat_ofNat_of_lt' hn]
      exact hk
    have hcounter : (prepared v).counter = 0 - UInt32.ofNat (n - mid - j) :=
      initial_counter n mid j hmid hj
    have hr : (prepared v).readPtr = source + 4 * UInt32.ofNat (mid + j) := by
      simp only [prepared, v, inputState, UInt32.ofNat_add, UInt32.mul_add, UInt32.add_assoc]
    have hw : (prepared v).writePtr = scratch + 4 * UInt32.ofNat (mid + j) := rfl
    have hrn : (prepared v).readPtr.toNat = source.toNat + 4 * (mid + j) := by
      rw [hr, wordOffset_toNat source (mid + j) (by omega)]
    have hwn : (prepared v).writePtr.toNat = scratch.toNat + 4 * (mid + j) := by
      rw [hw, wordOffset_toNat scratch (mid + j) (by omega)]
    obtain ⟨trace, finalStore, hlength, execution, hpages, hframe⟩ :=
      positive_cost store v ctx (n - mid - j) hpositive hremaining hcount hcounter
        (by change (UInt32.ofNat (mid + j)).toNat + _ ≤ (UInt32.ofNat n).toNat
            rw [hkn, UInt32.toNat_ofNat_of_lt' hn]; omega)
        (by rw [hrn]; omega) (by rw [hwn]; omega)
        (by rw [hrn]; omega) (by rw [hwn]; omega) hostBytes
    have hfinalCount : (finishedState (prepared v) (n - mid - j)).count = UInt32.ofNat n := by
      change UInt32.ofNat ((UInt32.ofNat (mid + j)).toNat + (n - mid - j)) = _
      rw [hkn, show mid + j + (n - mid - j) = n by omega]
    let final := finishedState (prepared v) (n - mid - j)
    refine ⟨trace, finalStore, final.aux6, final.readPtr, final.writePtr,
      final.counter, final.limit, final.aux12, 25 * (n - mid - j) + 37,
      hlength, le_rfl, by intro h; contradiction, ?_, hpages, hframe⟩
    have hf : locals final ctx.stack =
        sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
          (UInt32.ofNat mid) (UInt32.ofNat n) final.aux6 (UInt32.ofNat (n - mid))
          final.readPtr final.writePtr final.counter final.limit final.aux12 ctx.stack := by
      change sortLocals _ _ _ _ _ final.count _ _ _ _ _ _ _ _ = _
      rw [show final.count = UInt32.ofNat n from hfinalCount]
      rfl
    change CostedSteps (byteWork hostBytes) (start store v ctx) trace
      (finish finalStore final ctx) (25 * (n - mid - j) + 37) at execution
    simpa only [finish, hf] using execution

end Project.Mergesort.MergeRightDispatcherCost
