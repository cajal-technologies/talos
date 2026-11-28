import Project.Mergesort.MergeLeftDispatcherCost
import Project.Mergesort.MergeRightDispatcherCost

/-!
# Complete generated merge work

The main loop and both remainder dispatchers execute against the same evolving
physical memory. The main budget charges emitted words; each remainder charges
only the words still to copy. The endpoint is the actual copy-back continuation,
with every enclosing operand stack and caller frame retained.
-/

namespace Project.Mergesort.MergeCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof
open Project.Mergesort.MergeChoiceCost Project.Mergesort.MergeMainLoopCost

/-- The generated continuation after both remainder blocks. -/
def finish (store : MachineStore α) (source scratch : UInt32) (n : Nat)
    (v4 v5 v6 v7 v8 v9 v10 v11 v12 : UInt32) (ctx : Context) : Config α :=
  ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
      v4 v5 v6 v7 v8 v9 v10 v11 v12 ctx.stack,
    sortBlock4.drop 7, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

/-- Adapt only the saved context representation, preserving every field used
by execution. The right dispatcher stores its generated continuation itself. -/
def rightContext (ctx : Context) : MergeRightRemainderCost.Context :=
  { stack := ctx.stack, arity := ctx.arity, remainder := ctx.remainder,
    controls := ctx.controls, calls := ctx.calls }

/-- Complete generated merge, including both remainder dispatchers. Natural
indices and initial physical ranges prove all access and branch obligations.
No premise supplies a future execution or assumes a merge cost. -/
theorem merge_cost (store : MachineStore α) (source scratch : UInt32)
    (n mid : Nat) (hpositive : 0 < mid) (hmid : mid < n)
    (hsourceWord : source.toNat + 4 * n < UInt32.size)
    (hscratchWord : scratch.toNat + 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (ctx : Context) (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace memory v4 v5 v6 v7 v8 v9 v10 v11 v12 amount,
      CostedSteps (byteWork hostBytes)
        (entry store (state source scratch n mid 0 0 0 0 0) ctx) trace
        (finish { store with wasm := { store.wasm with mem := memory } }
          source scratch n v4 v5 v6 v7 v8 v9 v10 v11 v12 ctx) amount ∧
      memory.pages = store.wasm.mem.pages ∧ amount ≤ 50 * n + 64 := by
  obtain ⟨mainTrace, mainMemory, i, j, flag, last, mainAmount,
    _, _, hi, hj, hexit, mainRun, mainPages, _, emittedBound⟩ :=
    main_loop_cost store source scratch n mid 0 0 0 0 hpositive (by omega) hmid
      hsourceWord hscratchWord hsource hscratch ctx hostBytes
  let mainStore := { store with wasm := { store.wasm with mem := mainMemory } }
  obtain ⟨leftTrace, leftMemory, aux6, aux8, aux9, aux11, aux12, leftAmount,
    leftRun, leftPages, leftBound, leftSkip⟩ :=
    MergeLeftDispatcherCost.dispatcher_cost mainStore source scratch n mid i j flag last ctx
      (by omega) hi hj hexit hsourceWord hscratchWord
      (by change _ ≤ mainMemory.pages * 65536; rw [mainPages]; exact hsource)
      (by change _ ≤ mainMemory.pages * 65536; rw [mainPages]; exact hscratch) hostBytes
  let leftStore := { mainStore with wasm := { mainStore.wasm with mem := leftMemory } }
  obtain ⟨rightTrace, finalStore, v6, v8, v9, v10, v11, v12, rightAmount,
    _, rightBound, rightSkip, rightRun, rightPages, rightStore⟩ :=
    MergeRightDispatcherCost.dispatch_cost leftStore source scratch n mid j
      aux6 aux8 aux9 aux11 aux12 (rightContext ctx) (by omega) hj
      hsourceWord hscratchWord
      (by change _ ≤ leftMemory.pages * 65536
          rw [leftPages]; change _ ≤ mainMemory.pages * 65536
          rw [mainPages]; exact hsource)
      (by change _ ≤ leftMemory.pages * 65536
          rw [leftPages]; change _ ≤ mainMemory.pages * 65536
          rw [mainPages]; exact hscratch) hostBytes
  have finalFrame : finalStore =
      { store with wasm := { store.wasm with mem := finalStore.wasm.mem } } := by
    rw [rightStore]
  have finalPages : finalStore.wasm.mem.pages = store.wasm.mem.pages := by
    calc
      finalStore.wasm.mem.pages = leftMemory.pages := rightPages
      _ = mainMemory.pages := leftPages
      _ = store.wasm.mem.pages := mainPages
  have joined := mainRun.trans leftRun
  have rightRun' : CostedSteps (byteWork hostBytes)
      ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
        (UInt32.ofNat mid) (UInt32.ofNat (mid+j)) aux6 (UInt32.ofNat (n-mid))
        aux8 aux9 (UInt32.ofNat j) aux11 aux12 ctx.stack,
        MergeLeftDispatcherCost.afterCode, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩,
        leftStore⟩ rightTrace
      (finish { store with wasm := { store.wasm with mem := finalStore.wasm.mem } }
        source scratch n (UInt32.ofNat mid) (UInt32.ofNat n) v6 (UInt32.ofNat (n-mid))
          v8 v9 v10 v11 v12 ctx) rightAmount := by
    rw [finalFrame] at rightRun
    exact rightRun
  refine ⟨mainTrace ++ leftTrace ++ rightTrace, finalStore.wasm.mem,
    UInt32.ofNat mid, UInt32.ofNat n, v6, UInt32.ofNat (n-mid),
    v8, v9, v10, v11, v12, mainAmount + leftAmount + rightAmount,
    joined.trans rightRun', finalPages, ?_⟩
  simp only [Nat.zero_add, Nat.sub_zero] at emittedBound
  rcases hexit with ⟨hflag, rfl⟩ | ⟨_, _, hr⟩
  · have hs := leftSkip hflag
    omega
  · have hs := rightSkip hr
    omega

end Project.Mergesort.MergeCost
