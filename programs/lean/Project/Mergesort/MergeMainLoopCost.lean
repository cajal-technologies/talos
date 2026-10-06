import Project.Mergesort.MergeTailCost
import Project.Mergesort.Representations

/-!
# Numerical cost of the complete generated main merge loop

Natural indices and physical memory ranges discharge each actual access and
panic guard. One source index advances per choice, so the remaining element
count is a well-founded operational measure. No ordering or array-content
invariant is needed for this cost bound.
-/

namespace Project.Mergesort.MergeMainLoopCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof
open Project.Mergesort.MergeChoiceCost Project.Mergesort.MergeTailCost
open Project.Mergesort.Representations

/-- Natural indices attached to the exact generated locals. -/
def state (source scratch : UInt32) (n mid i j k : Nat)
    (left right : UInt32) : ChoiceState :=
  { source, scratch, length := UInt32.ofNat n, scratchLength := UInt32.ofNat n,
    mid := UInt32.ofNat mid, count := UInt32.ofNat k,
    rightBase := source + 4 * UInt32.ofNat mid,
    rightLength := UInt32.ofNat (n - mid),
    destination := scratch + 4 * UInt32.ofNat k,
    leftIndex := UInt32.ofNat i, rightIndex := UInt32.ofNat j,
    oldLeft := left, oldRight := right }

def done (store : MachineStore α) (v : ChoiceState) (ctx : Context) : Config α :=
  ⟨.running ⟨sortLocals v.source v.scratch v.length v.scratchLength
      v.mid v.count v.rightBase v.rightLength v.destination v.leftIndex v.rightIndex
      v.oldLeft v.oldRight ctx.stack,
    sortBlock4.drop 5, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

theorem advanced_state (source scratch : UInt32) (n mid i j k : Nat)
    (left right flag : UInt32) :
    advanced (state source scratch n mid i j k left right) flag =
      state source scratch n mid i j (k + 1) flag right := by
  unfold advanced state
  congr 1
  · change 1 + UInt32.ofNat k = UInt32.ofNat (k + 1)
    rw [UInt32.add_comm, UInt32.ofNat_succ]
  · change 4 + (scratch + 4 * UInt32.ofNat k) = scratch + 4 * UInt32.ofNat (k + 1)
    rw [← UInt32.ofNat_succ, UInt32.mul_add]
    simp only [UInt32.mul_one]
    ac_rfl

theorem exitHead_eq_done (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (flag : UInt32) : exitHead store v ctx flag = done store (advanced v flag) ctx := rfl

theorem left_address (source scratch : UInt32) (n mid i j k : Nat)
    (left right : UInt32) :
    leftAddress (state source scratch n mid i j k left right) =
      source + 4 * UInt32.ofNat i := by
  change (UInt32.ofNat i <<< (2 % 32 : UInt32)) + source = _
  rw [MemRegion.shl2_eq_mul4, UInt32.add_comm]

theorem right_address (source scratch : UInt32) (n mid i j k : Nat)
    (left right : UInt32) :
    rightAddress (state source scratch n mid i j k left right) =
      source + 4 * UInt32.ofNat (mid + j) := by
  change (UInt32.ofNat j <<< (2 % 32 : UInt32)) + (source + 4 * UInt32.ofNat mid) = _
  rw [MemRegion.shl2_eq_mul4, UInt32.ofNat_add, UInt32.mul_add]
  ac_rfl

theorem physical_accesses (store : MachineStore α) (source scratch : UInt32)
    (n mid i j : Nat) (left right : UInt32)
    (hi : i < mid) (hj : j < n - mid) (hmid : mid < n)
    (hsourceWord : source.toNat + 4 * n < UInt32.size)
    (hscratchWord : scratch.toNat + 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536) :
    let v := state source scratch n mid i j (i + j) left right
    (leftAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536 ∧
      (rightAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536 ∧
      v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536 ∧
      v.count < v.scratchLength := by
  dsimp only
  rw [left_address, right_address]
  rw [wordOffset_toNat source i (by omega),
    wordOffset_toNat source (mid + j) (by omega)]
  simp only [state]
  rw [wordOffset_toNat scratch (i + j) (by omega),
    UInt32.lt_iff_toNat_lt,
    UInt32.toNat_ofNat_of_lt' (by omega : i + j < UInt32.size),
    UInt32.toNat_ofNat_of_lt' (by omega : n < UInt32.size)]
  omega

theorem select_state (source scratch : UInt32) (n mid i j k : Nat)
    (oldLeft oldRight left right : UInt32) (takeLeft : Bool) :
    { state source scratch n mid i j k oldLeft oldRight with
      leftIndex := if takeLeft then 1 + UInt32.ofNat i else UInt32.ofNat i
      rightIndex := if takeLeft then UInt32.ofNat j else 1 + UInt32.ofNat j
      oldLeft := left, oldRight := right } =
      state source scratch n mid
        (if takeLeft then i + 1 else i) (if takeLeft then j else j + 1) k left right := by
  cases takeLeft <;> simp [state, ← UInt32.ofNat_succ, UInt32.add_comm]

private theorem natWord_lt (a b : Nat) (ha : a < UInt32.size) (hb : b < UInt32.size) :
    UInt32.ofNat a < UInt32.ofNat b ↔ a < b := by
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' ha, UInt32.toNat_ofNat_of_lt' hb]

private theorem natWord_le (a b : Nat) (ha : a < UInt32.size) (hb : b < UInt32.size) :
    UInt32.ofNat a ≤ UInt32.ofNat b ↔ a ≤ b := by
  rw [UInt32.le_iff_toNat_le_toNat, UInt32.toNat_ofNat_of_lt' ha, UInt32.toNat_ofNat_of_lt' hb]

/-- Every active choice advances one natural source index. The actual main
loop exits after bounded work, with its exact generated exit locals and all
non-memory store fields retained. -/
theorem body_cost (source scratch : UInt32) (n mid : Nat) (hmid : mid < n)
    (hsourceWord : source.toNat + 4 * n < UInt32.size)
    (hscratchWord : scratch.toNat + 4 * n < UInt32.size)
    (ctx : Context) (hostBytes : Config α → Nat → Config α → Nat)
    (remaining : Nat) :
    ∀ (store : MachineStore α) (i j : Nat) (oldLeft oldRight : UInt32),
    i < mid → j < n - mid → n - (i + j) = remaining →
    source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536 →
    scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536 →
    ∃ trace memory finalI finalJ flag last amount,
      i ≤ finalI ∧ j ≤ finalJ ∧ finalI ≤ mid ∧ finalJ ≤ n - mid ∧
      ((flag = 1 ∧ finalI = mid) ∨
        (flag = 0 ∧ finalI < mid ∧ finalJ = n - mid)) ∧
      CostedSteps (byteWork hostBytes)
        (head store (state source scratch n mid i j (i + j) oldLeft oldRight)
          (activeContext ctx)) trace
        (done { store with wasm := { store.wasm with mem := memory } }
          (state source scratch n mid finalI finalJ (finalI + finalJ) flag last) ctx) amount ∧
      memory.pages = store.wasm.mem.pages ∧ amount ≤ 50 * remaining ∧
      amount ≤ 50 * (finalI + finalJ - (i + j)) := by
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro store i j oldLeft oldRight hi hj hremaining hsource hscratch
    let v := state source scratch n mid i j (i + j) oldLeft oldRight
    let left := store.wasm.mem.read32 (leftAddress v + 0)
    let right := store.wasm.mem.read32 (rightAddress v + 0)
    let takeLeft := decide (left ≤ right)
    let nextI := if takeLeft then i + 1 else i
    let nextJ := if takeLeft then j else j + 1
    let nextStore := selectedStore store v (if takeLeft then left else right)
    let post := state source scratch n mid nextI nextJ (i + j) left right
    have hnext : i ≤ nextI ∧ j ≤ nextJ ∧ nextI ≤ mid ∧ nextJ ≤ n - mid ∧
        nextI + nextJ = i + j + 1 := by
      cases ht : takeLeft <;> simp [nextI, nextJ, ht] <;> omega
    rcases hnext with ⟨hiGrow, hjGrow, hiBound, hjBound, hnextSum⟩
    have hnWord : n < UInt32.size := by omega
    have hpages : nextStore.wasm.mem.pages = store.wasm.mem.pages := rfl
    have haccess := physical_accesses store source scratch n mid i j oldLeft oldRight
      hi hj hmid hsourceWord hscratchWord hsource hscratch
    rcases haccess with ⟨hleft, hright, hdestination, hroom⟩
    obtain ⟨choiceTrace, choiceAmount, _htrace, hchoiceBound, hchoice⟩ :=
      choice_cost store v (activeContext ctx) hleft hright hdestination hroom hostBytes
    rw [choice_tail_eq] at hchoice
    have hpost :
        { v with
          leftIndex := if takeLeft then 1 + v.leftIndex else v.leftIndex,
          rightIndex := if takeLeft then v.rightIndex else 1 + v.rightIndex,
          oldLeft := left, oldRight := right } = post :=
      select_state source scratch n mid i j (i + j) oldLeft oldRight left right takeLeft
    change CostedSteps (byteWork hostBytes) (head store v (activeContext ctx))
      choiceTrace (tailHead nextStore
        { v with
          leftIndex := if takeLeft then 1 + v.leftIndex else v.leftIndex,
          rightIndex := if takeLeft then v.rightIndex else 1 + v.rightIndex,
          oldLeft := left, oldRight := right } ctx) choiceAmount at hchoice
    rw [hpost] at hchoice
    have hadv (flag : UInt32) : advanced post flag =
        state source scratch n mid nextI nextJ (nextI + nextJ) flag right := by
      simpa only [post, hnextSum] using
        advanced_state source scratch n mid nextI nextJ (i + j) left right flag
    by_cases hleftDone : mid ≤ nextI
    · have huLeft : post.mid ≤ post.leftIndex :=
        (natWord_le mid nextI (by omega) (by omega)).2 hleftDone
      have htail := (left_exhausted nextStore post ctx huLeft hostBytes).2
      rw [exitHead_eq_done, hadv] at htail
      refine ⟨choiceTrace ++ leftExitTrace, nextStore.wasm.mem, nextI, nextJ,
        1, right, choiceAmount + 13, hiGrow, hjGrow, hiBound, hjBound,
        Or.inl ⟨rfl, by omega⟩, ?_, hpages, ?_, ?_⟩
      · simpa only [v, nextStore, selectedStore] using hchoice.trans htail
      · omega
      · omega
    · have hiNext : nextI < mid := by omega
      have huLeft : post.leftIndex < post.mid :=
        (natWord_lt nextI mid (by omega) (by omega)).2 hiNext
      by_cases hrightActive : nextJ < n - mid
      · have huRight : post.rightIndex < post.rightLength :=
          (natWord_lt nextJ (n - mid) (by omega) (by omega)).2 hrightActive
        have htail := (back_edge nextStore post ctx huLeft huRight hostBytes).2
        rw [hadv] at htail
        have hdecrease : n - (nextI + nextJ) < remaining := by omega
        obtain ⟨restTrace, memory, finalI, finalJ, flag, last, amount,
          hfi, hfj, hfiBound, hfjBound, hexit, hrest, hfinalPages, hrestBound, hrestEmitted⟩ :=
          ih (n - (nextI + nextJ)) hdecrease nextStore nextI nextJ 0 right
            hiNext hrightActive rfl (by simpa only [hpages] using hsource)
            (by simpa only [hpages] using hscratch)
        refine ⟨(choiceTrace ++ continueTrace) ++ restTrace, memory, finalI, finalJ,
          flag, last, (choiceAmount + 17) + amount,
          hiGrow.trans hfi, hjGrow.trans hfj, hfiBound, hfjBound, hexit, ?_,
          hfinalPages.trans hpages, ?_, ?_⟩
        · simpa only [v, nextStore, selectedStore] using (hchoice.trans htail).trans hrest
        · omega
        · omega
      · have huRight : ¬ post.rightIndex < post.rightLength := by
          rw [show post.rightIndex = UInt32.ofNat nextJ by rfl,
            show post.rightLength = UInt32.ofNat (n - mid) by rfl,
            natWord_lt nextJ (n - mid) (by omega) (by omega)]
          exact hrightActive
        have htail := (right_exhausted nextStore post ctx huLeft huRight hostBytes).2
        rw [exitHead_eq_done, hadv] at htail
        refine ⟨choiceTrace ++ rightExitTrace, nextStore.wasm.mem, nextI, nextJ,
          0, right, choiceAmount + 18, hiGrow, hjGrow, hiBound, hjBound,
          Or.inr ⟨rfl, hiNext, by omega⟩, ?_, hpages, ?_, ?_⟩
        · simpa only [v, nextStore, selectedStore] using hchoice.trans htail
        · omega
        · omega

/-- The actual generated loop instruction before its first main choice. -/
def entry (store : MachineStore α) (v : ChoiceState) (ctx : Context) : Config α :=
  ⟨.running ⟨sortLocals v.source v.scratch v.length v.scratchLength
      v.mid v.count v.rightBase v.rightLength v.destination v.leftIndex v.rightIndex
      v.oldLeft v.oldRight ctx.stack,
    [.loop 0 0 mergeMainLoopBody], ctx.arity, ctx.remainder,
    { sortRecursiveBodyFrame with belowStack := ctx.stack } ::
      { sortRecursiveGuardFrame with belowStack := ctx.stack } :: ctx.controls,
    ctx.calls⟩, store⟩

/-- Complete generated main-loop execution, including its actual entry.
The natural remaining-element count gives the explicit work bound. -/
theorem main_loop_cost (store : MachineStore α) (source scratch : UInt32)
    (n mid i j : Nat) (oldLeft oldRight : UInt32)
    (hi : i < mid) (hj : j < n - mid) (hmid : mid < n)
    (hsourceWord : source.toNat + 4 * n < UInt32.size)
    (hscratchWord : scratch.toNat + 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (ctx : Context) (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace memory finalI finalJ flag last amount,
      i ≤ finalI ∧ j ≤ finalJ ∧ finalI ≤ mid ∧ finalJ ≤ n - mid ∧
      ((flag = 1 ∧ finalI = mid) ∨
        (flag = 0 ∧ finalI < mid ∧ finalJ = n - mid)) ∧
      CostedSteps (byteWork hostBytes)
        (entry store (state source scratch n mid i j (i + j) oldLeft oldRight) ctx)
        trace
        (done { store with wasm := { store.wasm with mem := memory } }
          (state source scratch n mid finalI finalJ (finalI + finalJ) flag last) ctx) amount ∧
      memory.pages = store.wasm.mem.pages ∧ amount ≤ 50 * (n - (i + j)) + 1 ∧
      amount ≤ 50 * (finalI + finalJ - (i + j)) + 1 := by
  obtain ⟨trace, memory, finalI, finalJ, flag, last, amount,
    hfi, hfj, hfiBound, hfjBound, hexit, hbody, hpages, hamount, hemitted⟩ :=
    body_cost source scratch n mid hmid hsourceWord hscratchWord ctx hostBytes
      (n - (i + j)) store i j oldLeft oldRight hi hj rfl hsource hscratch
  have hentry : CostedSteps (byteWork hostBytes)
      (entry store (state source scratch n mid i j (i + j) oldLeft oldRight) ctx)
      [.instruction (.loop 0 0 mergeMainLoopBody)]
      (head store (state source scratch n mid i j (i + j) oldLeft oldRight)
        (activeContext ctx)) 1 := CostedSteps.single Step.loop
  refine ⟨[.instruction (.loop 0 0 mergeMainLoopBody)] ++ trace,
    memory, finalI, finalJ, flag, last, 1 + amount,
    hfi, hfj, hfiBound, hfjBound, hexit, hentry.trans hbody, hpages, ?_, ?_⟩ <;> omega

end Project.Mergesort.MergeMainLoopCost
