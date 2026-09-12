import Project.Mergesort.SortCallCost
import Project.Mergesort.SortCopyCost
import Project.Mergesort.MergeCost
import Project.Mergesort.SortWorkBudget

/-!
# Operational numerical bound for the complete recursive sort call

The proof composes both generated recursive calls, the complete merge, and the
actual copy-back and caller return. It preserves physical pages and all other
store fields. The cost counts semantic transitions and bulk-copy bytes.
-/

namespace Project.Mergesort.SortExecutionCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof
open Project.Mergesort.SortCallCost Project.Mergesort.Representations

private theorem natWord_sub {a b : Nat} (hle : b ≤ a) (ha : a < UInt32.size) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_sub,
    UInt32.toNat_ofNat_of_lt' ha,
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hle ha),
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le a b) ha)]
  have htoNatLt := (UInt32.ofNat a).toNat_lt
  rw [UInt32.toNat_ofNat_of_lt' ha] at htoNatLt
  omega

/-- The actual generated call 5 resumes its caller within the recursive budget.
The initial physical and no-wrap ranges discharge every descendant access;
there is no premise supplying successful child calls or a future trace. -/
theorem sort_call_cost (n : Nat) :
    ∀ (store : MachineStore α) (source scratch : UInt32)
      (callerLocals : Locals) (stack : List Value) (code : Program)
      (arity : Nat) (remainder : List Value)
      (controls : List ControlFrame) (calls : List CallFrame),
    store.runtime.currentModule = Project.Mergesort.module →
    source.toNat + 4 * n < UInt32.size →
    scratch.toNat + 4 * n < UInt32.size →
    source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536 →
    scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536 →
    ∀ (hostBytes : Config α → Nat → Config α → Nat),
    ∃ trace memory amount,
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨{ callerLocals with values :=
          [.i32 (UInt32.ofNat n), .i32 scratch, .i32 (UInt32.ofNat n), .i32 source] ++ stack },
          .call 5 :: code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ amount ∧
      memory.pages = store.wasm.mem.pages ∧ amount ≤ SortWorkBudget.budget n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro store source scratch callerLocals stack code arity remainder controls calls
      hmodule hsourceWord hscratchWord hsource hscratch hostBytes
    have hnSize : n < UInt32.size := by omega
    by_cases hbase : n < 2
    · have hwordBase : UInt32.ofNat n < 2 := by
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hnSize]
        exact hbase
      obtain ⟨trace, _, hcost⟩ := SortCostRecurrence.sort_base_call_cost
        store source scratch (UInt32.ofNat n) (UInt32.ofNat n)
        callerLocals stack code arity remainder controls calls hmodule hwordBase hostBytes
      refine ⟨trace, store.wasm.mem, 10, hcost, rfl, ?_⟩
      rw [SortWorkBudget.budget_base hbase]
    · have hn : 2 ≤ n := by omega
      let mid := n / 2
      let right := n - mid
      have hmid : 0 < mid := by dsimp [mid]; omega
      have hmidLt : mid < n := by dsimp [mid]; omega
      have hrightLt : right < n := by dsimp [right, mid]; omega
      have hsplit : mid + right = n := by dsimp [right, mid]; omega
      let frame := callerFrame store callerLocals stack code arity remainder controls
      let leftLocals := sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
        (UInt32.ofNat mid) 0 0 0 0 0 0 0 0 []
      obtain ⟨firstTrace, _, hfirst⟩ := first_recursive_call_setup store source scratch n
        hn hnSize callerLocals stack code arity remainder controls calls hmodule hostBytes
      obtain ⟨leftTrace, leftMemory, leftAmount, hleft, hleftPages, hleftAmount⟩ :=
        ih mid hmidLt store source scratch leftLocals [] (sortRecursiveBody.drop 12)
          0 [] recursiveControls (frame :: calls) hmodule
          (by omega) (by omega) (by omega) (by omega) hostBytes
      have hfirstLeft := hfirst.trans hleft
      let leftStore : MachineStore α :=
        { store with wasm := { store.wasm with mem := leftMemory } }
      obtain ⟨secondTrace, _, hsecond⟩ := second_recursive_call_setup leftStore source
        scratch (UInt32.ofNat n) (UInt32.ofNat mid) 0 [] recursiveControls
        (frame :: calls) hostBytes
      have hsub : UInt32.ofNat n - UInt32.ofNat mid = UInt32.ofNat right :=
        natWord_sub (by omega) hnSize
      rw [MemRegion.shl2_eq_mul4, hsub] at hsecond
      let rightSource := 4 * UInt32.ofNat mid + source
      let rightScratch := 4 * UInt32.ofNat mid + scratch
      let rightLocals := sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
        (UInt32.ofNat mid) (4 * UInt32.ofNat mid) rightSource (UInt32.ofNat right)
        0 0 0 0 0 []
      have hrightSource : rightSource.toNat = source.toNat + 4 * mid := by
        dsimp [rightSource]
        rw [UInt32.add_comm]
        exact wordOffset_toNat source mid (by omega)
      have hrightScratch : rightScratch.toNat = scratch.toNat + 4 * mid := by
        dsimp [rightScratch]
        rw [UInt32.add_comm]
        exact wordOffset_toNat scratch mid (by omega)
      obtain ⟨rightTrace, rightMemory, rightAmount, hright, hrightPages, hrightAmount⟩ :=
        ih right hrightLt leftStore rightSource rightScratch rightLocals []
          (sortRecursiveBody.drop 30) 0 [] recursiveControls (frame :: calls) hmodule
          (by rw [hrightSource]; omega) (by rw [hrightScratch]; omega)
          (by rw [hrightSource]; change source.toNat + 4 * mid + 4 * right ≤ leftMemory.pages * 65536
              rw [hleftPages]; omega)
          (by rw [hrightScratch]; change scratch.toNat + 4 * mid + 4 * right ≤ leftMemory.pages * 65536
              rw [hleftPages]; omega) hostBytes
      have hfirstRight := (hfirstLeft.trans hsecond).trans hright
      let rightStore : MachineStore α :=
        { store with wasm := { store.wasm with mem := rightMemory } }
      obtain ⟨setupTrace, _, hsetup⟩ := merge_setup rightStore source scratch
        (UInt32.ofNat n) (UInt32.ofNat mid) (4 * UInt32.ofNat mid) rightSource
        (UInt32.ofNat right) 0 [] recursiveControls (frame :: calls) hostBytes
      let ctx : MergeChoiceCost.Context :=
        { controls := [sortBlock4Frame, sortBlock3Frame, sortBlock2Frame, sortBlock1Frame],
          calls := frame :: calls }
      obtain ⟨mergeTrace, mergeMemory, v4, v5, v6, v7, v8, v9, v10, v11, v12,
        mergeAmount, hmergeRun, hmergePages, hmergeAmount⟩ :=
        MergeCost.merge_cost rightStore source scratch n mid hmid hmidLt hsourceWord hscratchWord
          (by change source.toNat + 4 * n ≤ rightMemory.pages * 65536
              rw [hrightPages, hleftPages]; exact hsource)
          (by change scratch.toNat + 4 * n ≤ rightMemory.pages * 65536
              rw [hrightPages, hleftPages]; exact hscratch) ctx hostBytes
      have hentryEq :
          MergeMainLoopCost.entry rightStore
            (MergeMainLoopCost.state source scratch n mid 0 0 0 0 0) ctx =
          ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
              (UInt32.ofNat mid) 0 rightSource (UInt32.ofNat right) scratch 0 0 0 0 [],
            [.loop 0 0 mergeMainLoopBody], 0, [], recursiveControls, frame :: calls⟩,
            rightStore⟩ := by
        simp [MergeMainLoopCost.entry, MergeMainLoopCost.state, ctx, right, rightSource,
          UInt32.add_comm, recursiveControls, sortRecursiveBodyFrame, sortRecursiveGuardFrame, emptyBlockFrame]
      rw [hentryEq] at hmergeRun
      have hsetupMerge := hsetup.trans hmergeRun
      let mergeStore : MachineStore α :=
        { store with wasm := { store.wasm with mem := mergeMemory } }
      obtain ⟨copyTrace, _, hcopy⟩ := SortCopyCost.sort_copyback_return_cost mergeStore
        source scratch n v4 v5 v6 v7 v8 v9 v10 v11 v12
        callerLocals stack code arity remainder controls calls (by omega) (by omega)
        (by change source.toNat + 4 * n ≤ mergeMemory.pages * 65536
            rw [hmergePages, hrightPages, hleftPages]; exact hsource)
        (by change scratch.toNat + 4 * n ≤ mergeMemory.pages * 65536
            rw [hmergePages, hrightPages, hleftPages]; exact hscratch) hostBytes
      refine ⟨((firstTrace ++ leftTrace) ++ secondTrace) ++ rightTrace ++
          (setupTrace ++ mergeTrace) ++ copyTrace,
        mergeMemory.copy source.toNat scratch.toNat (4 * n),
        ((22 + leftAmount + 17) + rightAmount) + (8 + mergeAmount) + (16 + 4 * n),
        ?_, ?_, ?_⟩
      · exact (hfirstRight.trans hsetupMerge).trans hcopy
      · exact hmergePages.trans (hrightPages.trans hleftPages)
      · rw [SortWorkBudget.budget_step hn]
        dsimp [mid, right] at hleftAmount hrightAmount
        omega

/-- An explicit logarithmic work bound and transition bound for the same
actual complete recursive call. This covers the internal sort call; the I/O
and allocation costs of the named export are separate operational segments. -/
theorem sort_call_log_cost (n : Nat)
    (store : MachineStore α) (source scratch : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hsourceWord : source.toNat + 4 * n < UInt32.size)
    (hscratchWord : scratch.toNat + 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace memory amount,
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨{ callerLocals with values :=
          [.i32 (UInt32.ofNat n), .i32 scratch, .i32 (UInt32.ofNat n), .i32 source] ++ stack },
          .call 5 :: code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ amount ∧
      memory.pages = store.wasm.mem.pages ∧ trace.length ≤ amount ∧
      amount ≤ 54 * n * Nat.clog 2 (n + 1) + 137 * n + 10 := by
  obtain ⟨trace, memory, amount, execution, pages, bound⟩ :=
    sort_call_cost n store source scratch callerLocals stack code arity remainder controls calls
      hmodule hsourceWord hscratchWord hsource hscratch hostBytes
  exact ⟨trace, memory, amount, execution, pages,
    execution.length_le (fun before kind after _ => byteWork_positive _ before kind after),
    bound.trans (SortWorkBudget.budget_log_bound n)⟩

end Project.Mergesort.SortExecutionCost
