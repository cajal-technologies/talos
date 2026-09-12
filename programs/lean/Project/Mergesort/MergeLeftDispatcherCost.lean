import Project.Mergesort.MergeMainLoopCost
import Project.Mergesort.MergeLeftRemainderCost

/-! Operational cost of the generated left-remainder dispatcher. -/
namespace Project.Mergesort.MergeLeftDispatcherCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof
open Project.Mergesort.MergeChoiceCost Project.Mergesort.MergeMainLoopCost
open Project.Mergesort.Representations

def afterCode : Program := .block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7

def after (store : MachineStore α) (v : MergeLeftRemainderCost.State) (ctx : Context) : Config α :=
  ⟨.running ⟨MergeLeftRemainderCost.locals v ctx.stack, afterCode, ctx.arity, ctx.remainder,
    ctx.controls, ctx.calls⟩, store⟩

def asLeft (v : ChoiceState) : MergeLeftRemainderCost.State :=
  ⟨v.source, v.scratch, v.length, v.scratchLength, v.mid, v.count,
    v.rightBase, v.rightLength, v.destination, v.leftIndex, v.rightIndex,
    v.oldLeft, v.oldRight⟩

def prepared (v : ChoiceState) : MergeLeftRemainderCost.State :=
  { (asLeft v) with
    stop := v.leftIndex - v.mid,
    pointer := v.source + 4 * v.leftIndex,
    guard := v.count - v.scratchLength, counter := 0 }

def loopContext (ctx : Context) : MergeLeftRemainderCost.Context :=
  { stack := ctx.stack, continuation := [.localGet 5, .localGet 9, .sub, .localSet 5],
    arity := ctx.arity, remainder := ctx.remainder,
    controls := {
      kind := .block
      paramArity := 0
      resultArity := 0
      body := mergeLeftRemainderBody
      continuation := afterCode
      belowStack := ctx.stack } :: ctx.controls, calls := ctx.calls }

def setupTrace : List StepKind :=
  [.instruction (.block 0 0 mergeLeftRemainderBody),
    .instruction (.localGet 11), .instruction (.br_if 0),
    .instruction (.localGet 9), .instruction (.localGet 4), .instruction .sub,
    .instruction (.localSet 6), .instruction (.localGet 0),
    .instruction (.localGet 9), .instruction (.const 2), .instruction .shl,
    .instruction .add, .instruction (.localSet 11), .instruction (.localGet 5),
    .instruction (.localGet 3), .instruction (.localGet 5),
    .instruction (.localGet 3), .instruction (.localGet 5), .instruction .gtU,
    .instruction .select, .instruction .sub, .instruction (.localSet 12),
    .instruction (.const 0), .instruction (.localSet 9)]

/-- Block entry plus the actual scalar setup costs twenty-four transitions. -/
theorem setup_cost (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hflag : v.oldLeft = 0) (hcount : v.count < v.scratchLength)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) (done store v ctx) setupTrace
      ⟨.running ⟨MergeLeftRemainderCost.locals (prepared v) ctx.stack,
        .loop 0 0 mergeLeftLoopBody :: (loopContext ctx).continuation,
        ctx.arity, ctx.remainder, (loopContext ctx).controls, ctx.calls⟩, store⟩ 24 := by
  apply Steps.with_unit_cost
  · unfold done setupTrace prepared asLeft loopContext MergeLeftRemainderCost.locals
    rw [sortBlock4_remainder_shape]
    wasm_steps [.block]
    rw [mergeLeftRemainderBody_shape]
    wasm_steps [(.localGet rfl)]
    rw [hflag]
    wasm_steps [.brIfZero, (.localGet rfl), (.localGet rfl), .sub,
      (.localSet rfl), (.localGet rfl), (.localGet rfl), .const, .shl]
    rw [MemRegion.shl2_eq_mul4]
    wasm_steps [.add]
    rw [UInt32.add_comm (4 * v.leftIndex) v.source]
    wasm_steps [(.localSet rfl), (.localGet rfl), (.localGet rfl),
      (.localGet rfl), (.localGet rfl), (.localGet rfl),
      (.gtU (result := 1) (by simp [hcount])),
      (.select (selected := .i32 v.scratchLength) (by simp)), .sub,
      (.localSet rfl), .const]
    simp only [sortLocals, List.length_cons, List.length_nil, List.set, List.drop_zero, afterCode]
    exact Steps.single (.localSet (locals' :=
      MergeLeftRemainderCost.locals (prepared v) (.i32 0 :: ctx.stack)) rfl)
  · intro before kind after member
    simp only [setupTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The final count subtraction and enclosing block exit retain all caller frames. -/
theorem finish_cost (store : MachineStore α) (v : MergeLeftRemainderCost.State) (ctx : Context)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) (MergeLeftRemainderCost.resume store v (loopContext ctx))
      [.instruction (.localGet 5), .instruction (.localGet 9), .instruction .sub,
        .instruction (.localSet 5), .administrative .exitControl]
      (after store { v with count := v.count - v.counter } ctx) 5 := by
  apply Steps.with_unit_cost
  · unfold MergeLeftRemainderCost.resume loopContext after
    wasm_steps [(.localGet rfl), (.localGet rfl), .sub, (.localSet rfl)]
    exact Steps.single (.exitControl rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- An already exhausted left input branches directly out in three transitions. -/
theorem skip_cost (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hflag : v.oldLeft = 1) (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) (done store v ctx)
      [.instruction (.block 0 0 mergeLeftRemainderBody),
        .instruction (.localGet 11), .instruction (.br_if 0)]
      (after store (asLeft v) ctx) 3 := by
  apply Steps.with_unit_cost
  · unfold done after asLeft MergeLeftRemainderCost.locals
    rw [sortBlock4_remainder_shape]
    wasm_steps [.block]
    rw [mergeLeftRemainderBody_shape]
    wasm_steps [(.localGet rfl)]
    rw [hflag]
    exact Steps.single (.brIf (by decide) rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- Natural main-loop exit facts determine the whole left dispatcher. The
returned count is `mid+j`; the right index is retained for the next dispatcher.
Only physical full-array ranges are assumed, not future-loop execution facts. -/
theorem dispatcher_cost (store : MachineStore α) (source scratch : UInt32)
    (n mid i j : Nat) (flag last : UInt32) (ctx : Context)
    (hmid : mid ≤ n) (hi : i ≤ mid) (hj : j ≤ n - mid)
    (hexit : (flag = 1 ∧ i = mid) ∨ (flag = 0 ∧ i < mid ∧ j = n - mid))
    (hsourceWord : source.toNat + 4 * n < UInt32.size)
    (hscratchWord : scratch.toNat + 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace memory aux6 aux8 aux9 aux11 aux12 amount,
      CostedSteps (byteWork hostBytes)
        (done store (state source scratch n mid i j (i+j) flag last) ctx) trace
        ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
          (UInt32.ofNat mid) (UInt32.ofNat (mid+j)) aux6
          (UInt32.ofNat (n-mid)) aux8 aux9 (UInt32.ofNat j) aux11 aux12 ctx.stack,
          afterCode, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ amount ∧
      memory.pages = store.wasm.mem.pages ∧
      amount ≤ 23*(mid-i)+31 ∧ (flag = 1 → amount ≤ 3) := by
  rcases hexit with ⟨rfl, hiEq⟩ | ⟨rfl, hiLt, rfl⟩
  · subst i
    refine ⟨[.instruction (.block 0 0 mergeLeftRemainderBody),
      .instruction (.localGet 11), .instruction (.br_if 0)], store.wasm.mem, source + 4 * UInt32.ofNat mid,
      scratch + 4 * UInt32.ofNat (mid+j), UInt32.ofNat mid, 1, last,
      3, ?_, rfl, by omega, by omega⟩
    exact skip_cost store (state source scratch n mid mid j (mid+j) 1 last) ctx rfl hostBytes
  · let k := i + (n-mid)
    let r := mid-i
    let v := state source scratch n mid i (n-mid) k 0 last
    let p := prepared v
    have hir : i+r = mid := by dsimp [r]; omega
    have hkr : k+r = n := by dsimp [k, r]; omega
    have hpositive : 0 < r := by dsimp [r]; omega
    have hkLt : k < n := by omega
    have hkU : v.count < v.scratchLength := by
      change UInt32.ofNat k < UInt32.ofNat n
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by omega : k < UInt32.size),
        UInt32.toNat_ofNat_of_lt' (by omega : n < UInt32.size)]
      exact hkLt
    have cancel (a b : UInt32) : a - (a+b) = -b := by
      have haz : a + -a = 0 := by rw [← UInt32.sub_eq_add_neg, UInt32.sub_self]
      simp only [UInt32.sub_eq_add_neg, UInt32.neg_add]
      rw [← UInt32.add_assoc, haz, UInt32.zero_add]
    have hstop : p.stop = -UInt32.ofNat r := by
      change UInt32.ofNat i - UInt32.ofNat mid = _
      calc
        _ = UInt32.ofNat i - (UInt32.ofNat i + UInt32.ofNat r) := by
          rw [← UInt32.ofNat_add, hir]
        _ = _ := cancel _ _
    have hguard : p.guard = p.stop := by
      rw [hstop]
      change UInt32.ofNat k - UInt32.ofNat n = _
      calc
        _ = UInt32.ofNat k - (UInt32.ofNat k + UInt32.ofNat r) := by
          rw [← UInt32.ofNat_add, hkr]
        _ = _ := cancel _ _
    have hcounter : p.counter = p.stop + UInt32.ofNat r := by
      rw [hstop]
      change 0 = -UInt32.ofNat r + UInt32.ofNat r
      rw [UInt32.add_comm, ← UInt32.sub_eq_add_neg, UInt32.sub_self]
    have hpointer : p.pointer.toNat = source.toNat + 4*i :=
      wordOffset_toNat source i (by omega)
    have hdestination : p.destination.toNat = scratch.toNat + 4*k :=
      wordOffset_toNat scratch k (by omega)
    obtain ⟨tr, _, loop⟩ := MergeLeftRemainderCost.loop_enter_cost store p (loopContext ctx) r
      hpositive hguard hcounter (by rw [hpointer]; omega) (by rw [hdestination]; omega)
      (by rw [hpointer]; omega) (by rw [hdestination]; omega) hostBytes
    have setup := setup_cost store v ctx rfl hkU hostBytes
    have finish := finish_cost (MergeLeftRemainderCost.copyWords store p r)
      (MergeLeftRemainderCost.advance p r) ctx hostBytes
    have run := (setup.trans loop).trans finish
    have hcount : (MergeLeftRemainderCost.advance p r).count -
        (MergeLeftRemainderCost.advance p r).counter = UInt32.ofNat n := by
      rw [MergeLeftRemainderCost.advance_eq]
      change UInt32.ofNat k - (-UInt32.ofNat r + 0) = _
      rw [UInt32.add_zero, UInt32.sub_eq_add_neg, UInt32.neg_neg,
        ← UInt32.ofNat_add, hkr]
    have hmj : mid + (n-mid) = n := by omega
    refine ⟨(setupTrace ++ tr) ++
      [.instruction (.localGet 5), .instruction (.localGet 9), .instruction .sub,
        .instruction (.localSet 5), .administrative .exitControl],
      (MergeLeftRemainderCost.copyWords store p r).wasm.mem,
      (MergeLeftRemainderCost.advance p r).stop,
      (MergeLeftRemainderCost.advance p r).destination,
      (MergeLeftRemainderCost.advance p r).counter,
      (MergeLeftRemainderCost.advance p r).pointer,
      (MergeLeftRemainderCost.advance p r).guard,
      23*r+31, ?_, MergeLeftRemainderCost.copyWords_pages store p r, by dsimp [r]; omega, ?_⟩
    · have hstore := MergeLeftRemainderCost.copyWords_store store p r
      rw [hcount] at run
      rw [hstore] at run
      simpa only [after, MergeLeftRemainderCost.locals, hmj,
        MergeLeftRemainderCost.advance_eq, p, prepared, asLeft, v, state,
        k, show 24 + (23*r+2) + 5 = 23*r+31 by omega] using run
    · intro h
      exact absurd h (by decide : (0 : UInt32) ≠ 1)

end Project.Mergesort.MergeLeftDispatcherCost
