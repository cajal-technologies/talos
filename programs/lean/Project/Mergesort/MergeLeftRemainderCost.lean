import Project.Mergesort.SortProof
import CodeLib.SepLogic.CostedLoop

/-!
# Scalar cost of the generated left-remainder loop

The store and local-variable updates are the actual small-step effects. Each
scalar instruction costs one under byteWork; there are no host calls, growth,
or bulk transfers in this loop. The caller continuation is retained, not run.
-/

namespace Project.Mergesort.MergeLeftRemainderCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof

/-- The generated sort's four parameters and nine local slots. -/
structure State where
  source : UInt32
  scratch : UInt32
  length : UInt32
  scratchLength : UInt32
  mid : UInt32
  count : UInt32
  stop : UInt32
  rightLength : UInt32
  destination : UInt32
  counter : UInt32
  rightIndex : UInt32
  pointer : UInt32
  guard : UInt32

structure Context where
  stack : List Value := []
  continuation : Program := []
  arity : Nat := 0
  remainder : List Value := []
  controls : List ControlFrame := []
  calls : List CallFrame := []

def locals (v : State) (stack : List Value) : Locals :=
  sortLocals v.source v.scratch v.length v.scratchLength v.mid v.count
    v.stop v.rightLength v.destination v.counter v.rightIndex v.pointer v.guard stack

def next (v : State) : State :=
  { v with
    destination := 4 + v.destination
    pointer := 4 + v.pointer
    counter := 4294967295 + v.counter }

def written (store : MachineStore α) (v : State) : MachineStore α :=
  { store with wasm := { store.wasm with
    mem := store.wasm.mem.write32 (v.destination + 0) (store.wasm.mem.read32 (v.pointer + 0)) } }

def loopFrame (ctx : Context) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0, body := mergeLeftLoopBody,
      continuation := ctx.continuation, belowStack := ctx.stack }

def head (store : MachineStore α) (v : State) (ctx : Context) : Config α :=
  ⟨.running ⟨locals v ctx.stack, mergeLeftLoopBody, ctx.arity, ctx.remainder,
      loopFrame ctx :: ctx.controls, ctx.calls⟩, store⟩

def beforeBranch (store : MachineStore α) (v : State) (ctx : Context)
    (condition : UInt32) : Config α :=
  ⟨.running ⟨locals (next v) (.i32 condition :: ctx.stack), [.br_if 0],
      ctx.arity, ctx.remainder, loopFrame ctx :: ctx.controls, ctx.calls⟩,
    written store v⟩

def resume (store : MachineStore α) (v : State) (ctx : Context) : Config α :=
  ⟨.running ⟨locals v ctx.stack, ctx.continuation, ctx.arity, ctx.remainder,
      ctx.controls, ctx.calls⟩, store⟩

def prefixTrace : List StepKind :=
  [.instruction (.localGet 12), .instruction (.localGet 9), .instruction .eq,
    .instruction (.br_if 4), .instruction (.localGet 8), .instruction (.localGet 11),
    .instruction (.load32 0), .instruction (.store32 0),
    .instruction (.localGet 8), .instruction (.const 4), .instruction .add,
    .instruction (.localSet 8), .instruction (.localGet 11), .instruction (.const 4),
    .instruction .add, .instruction (.localSet 11), .instruction (.localGet 6),
    .instruction (.localGet 9), .instruction (.const 4294967295), .instruction .add,
    .instruction (.localTee 9), .instruction .ne]

/-- Execute the checked generated body through its last comparison. -/
theorem iteration_prefix_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hguard : v.guard ≠ v.counter)
    (hsource : v.pointer.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    prefixTrace.length = 22 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) prefixTrace
        (beforeBranch store v ctx (if v.stop ≠ (next v).counter then 1 else 0)) 22 := by
  have execution : Steps (head store v ctx) prefixTrace
      (beforeBranch store v ctx (if v.stop ≠ (next v).counter then 1 else 0)) := by
    unfold head beforeBranch prefixTrace
    rw [mergeLeftLoopBody_shape]
    simp only [locals, sortLocals, next]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.eq (result := 0) (by simp [hguard])), .brIfZero,
      (.localGet rfl), (.localGet rfl),
      (.load32 rfl (by simpa using hsource)),
      (.store32 rfl (by simpa using hdestination)),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), (.localGet rfl), .const, .add, (.localTee rfl)]
    exact Steps.single (.ne rfl)
  refine ⟨rfl, execution.with_unit_cost ?_⟩
  intro before kind after member
  simp only [prefixTrace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- One complete continuing iteration costs 23 and returns the actual next
loop head, including its write and both incremented pointers. -/
theorem iteration_continue_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hguard : v.guard ≠ v.counter) (hcontinue : v.stop ≠ (next v).counter)
    (hsource : v.pointer.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 23 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        (head (written store v) (next v) ctx) 23 := by
  obtain ⟨hlength, pre⟩ := iteration_prefix_cost store v ctx hguard hsource
    hdestination hostBytes
  simp only [if_pos hcontinue] at pre
  have branch : CostedSteps (byteWork hostBytes) (beforeBranch store v ctx 1)
      [.instruction (.br_if 0)] (head (written store v) (next v) ctx) 1 :=
    CostedSteps.single (.brIf (by decide) rfl)
  exact ⟨_, by simp [hlength], pre.trans branch⟩

/-- The last branch falls through after 23 scalar instructions. This endpoint
still has its loop frame; the frame exit is charged separately below. -/
theorem iteration_final_branch_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hguard : v.guard ≠ v.counter) (hstop : v.stop = (next v).counter)
    (hsource : v.pointer.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 23 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        ⟨.running ⟨locals (next v) ctx.stack, [], ctx.arity, ctx.remainder,
          loopFrame ctx :: ctx.controls, ctx.calls⟩, written store v⟩ 23 := by
  obtain ⟨hlength, pre⟩ := iteration_prefix_cost store v ctx hguard hsource
    hdestination hostBytes
  simp only [hstop, ne_eq, not_true_eq_false, if_false] at pre
  have branch : CostedSteps (byteWork hostBytes) (beforeBranch store v ctx 0)
      [.instruction (.br_if 0)]
      ⟨.running ⟨locals (next v) ctx.stack, [], ctx.arity, ctx.remainder,
        loopFrame ctx :: ctx.controls, ctx.calls⟩, written store v⟩ 1 :=
    CostedSteps.single .brIfZero
  exact ⟨_, by simp [hlength], pre.trans branch⟩

/-- Include the single administrative loop-frame exit, preserving the caller's
continuation, control and call frames without executing them. -/
theorem iteration_exit_cost (store : MachineStore α) (v : State) (ctx : Context)
    (hguard : v.guard ≠ v.counter) (hstop : v.stop = (next v).counter)
    (hsource : v.pointer.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 24 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        (resume (written store v) (next v) ctx) 24 := by
  obtain ⟨trace, hlength, iteration⟩ := iteration_final_branch_cost store v ctx
    hguard hstop hsource hdestination hostBytes
  have exit : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨locals (next v) ctx.stack, [], ctx.arity, ctx.remainder,
        loopFrame ctx :: ctx.controls, ctx.calls⟩, written store v⟩
      [.administrative .exitControl]
      (resume (written store v) (next v) ctx) 1 :=
    CostedSteps.single (.exitControl rfl)
  exact ⟨_, by simp [hlength], iteration.trans exit⟩

theorem written_pages (store : MachineStore α) (v : State) :
    (written store v).wasm.mem.pages = store.wasm.mem.pages := rfl

/-- The exact sequential memory effect, including reads from each updated
store. No disjointness or immutable-source assumption is hidden here. -/
def copyWords (store : MachineStore α) (v : State) : Nat → MachineStore α
  | 0 => store
  | n + 1 => copyWords (written store v) (next v) n

def advance (v : State) : Nat → State
  | 0 => v
  | n + 1 => advance (next v) n

/-- Every non-memory machine-store field is unchanged, including runtime,
globals, host state, other memories and physical cap metadata. -/
theorem copyWords_store (store : MachineStore α) (v : State) (n : Nat) :
    copyWords store v n =
      { store with wasm := { store.wasm with mem := (copyWords store v n).wasm.mem } } := by
  induction n generalizing store v with
  | zero => rfl
  | succ n ih => simpa only [copyWords, written] using ih (written store v) (next v)

theorem copyWords_pages (store : MachineStore α) (v : State) (n : Nat) :
    (copyWords store v n).wasm.mem.pages = store.wasm.mem.pages := by
  induction n generalizing store v with
  | zero => rfl
  | succ n ih => simpa only [copyWords, written_pages] using ih (written store v) (next v)

/-- Exact modular register updates; all other slots, including count, stop
and guard, retain their original values. -/
theorem advance_eq (v : State) (n : Nat) :
    advance v n = { v with
      destination := UInt32.ofNat (4 * n) + v.destination
      pointer := UInt32.ofNat (4 * n) + v.pointer
      counter := -UInt32.ofNat n + v.counter } := by
  induction n generalizing v with
  | zero => simp [advance]
  | succ n ih =>
    simp only [advance, ih, next, Nat.mul_add, Nat.mul_one, UInt32.ofNat_add,
      UInt32.neg_add, UInt32.sub_eq_add_neg, UInt32.add_assoc,
      show UInt32.ofNat 4 = (4 : UInt32) from rfl,
      show UInt32.ofNat 1 = (1 : UInt32) from rfl, UInt32.neg_one_eq]

private theorem counter_step (stop : UInt32) (n : Nat) :
    4294967295 + (stop + UInt32.ofNat (n + 1)) = stop + UInt32.ofNat n := by
  rw [UInt32.ofNat_add]
  change 4294967295 + (stop + (UInt32.ofNat n + 1)) = _
  calc
    _ = ((4294967295 : UInt32) + 1) + (stop + UInt32.ofNat n) := by ac_rfl
    _ = stop + UInt32.ofNat n := UInt32.zero_add _

private theorem counter_ne (stop : UInt32) (n : Nat)
    (hpositive : 0 < n) (hbound : n < UInt32.size) :
    stop ≠ stop + UInt32.ofNat n := by
  intro heq
  have hsub := congrArg (fun x : UInt32 => x - stop) heq
  rw [UInt32.add_comm stop (UInt32.ofNat n)] at hsub
  simp only [UInt32.sub_self, UInt32.add_sub_cancel] at hsub
  have hnat := congrArg UInt32.toNat hsub
  rw [UInt32.toNat_ofNat_of_lt' hbound] at hnat
  change 0 = n at hnat
  omega

/-- A positive left-remainder count determines the whole generated loop.
The guard and stop agree as in the left-remainder merge invariant; the
counter encodes the number still to copy relative to that stop. Contiguous
physical ranges and no address wrap justify every subsequent access.
The cost includes the final loop-frame exit, but not loop entry or caller code. -/
theorem loop_cost (store : MachineStore α) (v : State) (ctx : Context) (n : Nat)
    (hpositive : 0 < n) (hguard : v.guard = v.stop)
    (hcounter : v.counter = v.stop + UInt32.ofNat n)
    (hsourceWord : v.pointer.toNat + 4 * n < UInt32.size)
    (hdestinationWord : v.destination.toNat + 4 * n < UInt32.size)
    (hsource : v.pointer.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 23 * n + 1 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        (resume (copyWords store v n) (advance v n) ctx) (23 * n + 1) := by
  induction n generalizing store v with
  | zero => omega
  | succ n ih =>
    have hcountBound : n + 1 < UInt32.size := by omega
    have hguardNe : v.guard ≠ v.counter := by
      rw [hguard, hcounter]
      exact counter_ne v.stop (n + 1) (by omega) hcountBound
    have hsourceNow : v.pointer.toNat + 4 ≤ store.wasm.mem.pages * 65536 := by omega
    have hdestinationNow : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536 := by omega
    have hnextCounter : (next v).counter = v.stop + UInt32.ofNat n := by
      change 4294967295 + v.counter = _
      rw [hcounter]
      exact counter_step v.stop n
    by_cases hn : n = 0
    · subst n
      have hstop : v.stop = (next v).counter := by simpa using hnextCounter.symm
      obtain ⟨trace, hlength, execution⟩ := iteration_exit_cost store v ctx hguardNe
        hstop hsourceNow hdestinationNow hostBytes
      exact ⟨trace, hlength, execution⟩
    · have hcontinue : v.stop ≠ (next v).counter := by
        rw [hnextCounter]
        exact counter_ne v.stop n (by omega) (by omega)
      obtain ⟨firstTrace, hfirstLength, first⟩ := iteration_continue_cost store v ctx
        hguardNe hcontinue hsourceNow hdestinationNow hostBytes
      have hpointer : (next v).pointer.toNat = v.pointer.toNat + 4 := by
        change (4 + v.pointer : UInt32).toNat = _
        rw [UInt32.toNat_add]
        change (4 + v.pointer.toNat) % UInt32.size = _
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have hdestinationNext : (next v).destination.toNat = v.destination.toNat + 4 := by
        change (4 + v.destination : UInt32).toNat = _
        rw [UInt32.toNat_add]
        change (4 + v.destination.toNat) % UInt32.size = _
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      obtain ⟨restTrace, hrestLength, rest⟩ := ih (written store v) (next v)
        (by omega) hguard hnextCounter
        (by rw [hpointer]; omega) (by rw [hdestinationNext]; omega)
        (by rw [hpointer, written_pages]; omega)
        (by rw [hdestinationNext, written_pages]; omega)
      refine ⟨firstTrace ++ restTrace, ?_, ?_⟩
      · simp only [List.length_append, hfirstLength, hrestLength]
        omega
      · simpa only [copyWords, advance, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using first.trans rest

/-- Include entry through the actual generated loop instruction. The complete
loop segment costs `23*n+2`, ending before its caller continuation executes. -/
theorem loop_enter_cost (store : MachineStore α) (v : State) (ctx : Context) (n : Nat)
    (hpositive : 0 < n) (hguard : v.guard = v.stop)
    (hcounter : v.counter = v.stop + UInt32.ofNat n)
    (hsourceWord : v.pointer.toNat + 4 * n < UInt32.size)
    (hdestinationWord : v.destination.toNat + 4 * n < UInt32.size)
    (hsource : v.pointer.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 23 * n + 2 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨locals v ctx.stack, .loop 0 0 mergeLeftLoopBody :: ctx.continuation,
          ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩ trace
        (resume (copyWords store v n) (advance v n) ctx) (23 * n + 2) := by
  obtain ⟨trace, hlength, execution⟩ := loop_cost store v ctx n hpositive hguard
    hcounter hsourceWord hdestinationWord hsource hdestination hostBytes
  have enter : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨locals v ctx.stack, .loop 0 0 mergeLeftLoopBody :: ctx.continuation,
        ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩
      [.instruction (.loop 0 0 mergeLeftLoopBody)] (head store v ctx) 1 :=
    CostedSteps.single .loop
  refine ⟨[.instruction (.loop 0 0 mergeLeftLoopBody)] ++ trace, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, hlength]
    omega
  simpa only [show 1 + (23 * n + 1) = 23 * n + 2 by omega] using enter.trans execution

private def testState : State :=
  { source := 64, scratch := 120, length := 4, scratchLength := 4,
    mid := 2, count := 2, stop := 4294967294, rightLength := 2,
    destination := 128, counter := 0, rightIndex := 2, pointer := 64,
    guard := 4294967294 }

private def testContext : Context :=
  { stack := [.i32 77], continuation := [.unreachable], arity := 1,
    remainder := [.i32 66],
    controls := [{ kind := .block, paramArity := 0, resultArity := 0, body := [.nop], continuation := [.nop], belowStack := [.i32 55] }],
    calls := [{ locals := ⟨[], [], [.i32 44]⟩, continuation := [.nop], resultArity := 1, callerRemainder := [.i32 33], control := [], returningInstance := ⟨0⟩ }] }

private def testStore : MachineStore Universal.State :=
  { runtime := { instances := #[{ module := Project.Mergesort.module, host := Universal.envFor Project.Mergesort.module }], entry := ⟨0⟩ },
    wasm := {
      mem := (((((Mem.empty 17).write32 64 123).write32 68 456).write32 120 88).write32 124 99).write32 136 0xA5A5A5A5
      globals := ⟨[]⟩
      host := default
      memoryCaps := [Module.memoryHardCap] } }

set_option maxRecDepth 262144 in
/-- The universal theorem applies to a two-word remainder with nonempty
operand, remainder, control and call frames. -/
theorem two_word_cost :
    ∃ trace, trace.length = 47 ∧
      CostedSteps (byteWork (fun _ _ _ => 0)) (head testStore testState testContext) trace
        (resume (copyWords testStore testState 2) (advance testState 2) testContext) 47 :=
  loop_cost testStore testState testContext 2 (by decide) rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ => 0)

set_option maxRecDepth 262144 in
/-- Kernel-reduced execution validates both copies, unchanged adjacent words,
and exact resumption before the caller's unreachable instruction. -/
theorem two_word_runner :
    (runSteps 47 (head testStore testState testContext)).result.finalConfig?.map
      (fun c => (c.expr, c.store.wasm.mem.read32 128, c.store.wasm.mem.read32 132,
        c.store.wasm.mem.read32 120, c.store.wasm.mem.read32 124,
        c.store.wasm.mem.read32 136, c.store.wasm.mem.pages)) =
      some ((resume (copyWords testStore testState 2) (advance testState 2) testContext).expr,
        123, 456, 88, 99, 0xA5A5A5A5, 17) := by rfl

set_option maxRecDepth 262144 in
/-- One further transition executes the caller's trap, so the certified segment
does not silently include or assume behavior of the continuation. -/
theorem two_word_caller_traps :
    (runSteps 48 (head testStore testState testContext)).result.finalConfig?.map
      (fun c => c.expr) = some (.trapped .unreachable) := by rfl

end Project.Mergesort.MergeLeftRemainderCost
