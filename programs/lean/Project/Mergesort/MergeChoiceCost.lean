import Project.Mergesort.SortProof
import CodeLib.SepLogic.CostedLoop

/-!
# Cost of an actual main-merge choice

The endpoints use the generated merge loop and the original sort locals.
Scalar loads and stores have unit charge under byteWork. These segments do
not contain host calls, bulk transfers, or memory growth. They are components
of a future sort recurrence, not an assumed recurrence or full export budget.
-/

namespace Project.Mergesort.MergeChoiceCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof

/-- The thirteen generated sort parameters and locals at a merge choice. -/
structure ChoiceState where
  source : UInt32
  scratch : UInt32
  length : UInt32
  scratchLength : UInt32
  mid : UInt32
  count : UInt32
  rightBase : UInt32
  rightLength : UInt32
  destination : UInt32
  leftIndex : UInt32
  rightIndex : UInt32
  oldLeft : UInt32
  oldRight : UInt32

/-- The actual loop is entered with its enclosing execution context intact. -/
structure Context where
  stack : List Value := []
  arity : Nat := 0
  remainder : List Value := []
  controls : List ControlFrame := []
  calls : List CallFrame := []

def leftAddress (v : ChoiceState) : UInt32 := (v.leftIndex <<< (2 : UInt32)) + v.source

def rightAddress (v : ChoiceState) : UInt32 := (v.rightIndex <<< (2 : UInt32)) + v.rightBase

def head (store : MachineStore α) (v : ChoiceState) (ctx : Context) : Config α :=
  ⟨.running ⟨sortLocals v.source v.scratch v.length v.scratchLength
      v.mid v.count v.rightBase v.rightLength v.destination v.leftIndex v.rightIndex
      v.oldLeft v.oldRight ctx.stack,
    mergeMainLoopBody, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

def selectedStore (store : MachineStore α) (v : ChoiceState) (selected : UInt32) :
    MachineStore α :=
  { store with wasm := { store.wasm with mem := store.wasm.mem.write32 (v.destination + 0) selected } }

def tail (store : MachineStore α) (v : ChoiceState) (ctx : Context) (takeLeft : Bool) :
    Config α :=
  let left := store.wasm.mem.read32 (leftAddress v + 0)
  let right := store.wasm.mem.read32 (rightAddress v + 0)
  ⟨.running ⟨sortLocals v.source v.scratch v.length v.scratchLength
      v.mid v.count v.rightBase v.rightLength v.destination
      (if takeLeft then 1 + v.leftIndex else v.leftIndex)
      (if takeLeft then v.rightIndex else 1 + v.rightIndex) left right ctx.stack,
    mergeMainLoopBody.drop 1, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩,
    selectedStore store v (if takeLeft then left else right)⟩

def leftTrace : List StepKind :=
  [.instruction (.block 0 0 mergeMainOuterBody),
   .instruction (.block 0 0 mergeMainChoiceBody),
   .instruction (.block 0 0 mergeMainCompareBody),
   .instruction (.localGet 0), .instruction (.localGet 9),
   .instruction (.const 2), .instruction .shl, .instruction .add,
   .instruction (.load32 0), .instruction (.localTee 11),
   .instruction (.localGet 6), .instruction (.localGet 10),
   .instruction (.const 2), .instruction .shl, .instruction .add,
   .instruction (.load32 0), .instruction (.localTee 12),
   .instruction .leU, .instruction (.br_if 0),
   .instruction (.block 0 0 mergeMainLeftBody),
   .instruction (.localGet 5), .instruction (.localGet 3),
   .instruction .geU, .instruction (.br_if 0),
   .instruction (.localGet 8), .instruction (.localGet 11),
   .instruction (.store32 0), .instruction (.localGet 9),
   .instruction (.const 1), .instruction .add,
   .instruction (.localSet 9), .instruction (.br 2)]

def rightTrace : List StepKind :=
  [.instruction (.block 0 0 mergeMainOuterBody),
   .instruction (.block 0 0 mergeMainChoiceBody),
   .instruction (.block 0 0 mergeMainCompareBody),
   .instruction (.localGet 0), .instruction (.localGet 9),
   .instruction (.const 2), .instruction .shl, .instruction .add,
   .instruction (.load32 0), .instruction (.localTee 11),
   .instruction (.localGet 6), .instruction (.localGet 10),
   .instruction (.const 2), .instruction .shl, .instruction .add,
   .instruction (.load32 0), .instruction (.localTee 12),
   .instruction .leU, .instruction (.br_if 0),
   .instruction (.localGet 5), .instruction (.localGet 3),
   .instruction .geU, .instruction (.br_if 1),
   .instruction (.localGet 8), .instruction (.localGet 12),
   .instruction (.store32 0), .instruction (.localGet 10),
   .instruction (.const 1), .instruction .add,
   .instruction (.localSet 10), .instruction (.br 2)]

/-- Actual left selection, including both loads, the comparison and capacity
checks, the exact scratch write, index update, and depth-two branch. -/
theorem left_choice_cost (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hleft : (leftAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hright : (rightAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hroom : v.count < v.scratchLength)
    (hle : store.wasm.mem.read32 (leftAddress v + 0) ≤
      store.wasm.mem.read32 (rightAddress v + 0))
    (hostBytes : Config α → Nat → Config α → Nat) :
    leftTrace.length = 32 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) leftTrace
        (tail store v ctx true) 32 := by
  have execution : Steps (head store v ctx) leftTrace (tail store v ctx true) := by
    unfold head tail
    dsimp only
    unfold leftTrace
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    simp only [sortLocals]
    wasm_steps [(.localGet rfl), (.localGet rfl), .const, .shl, .add,
      (.load32 rfl (by simpa [leftAddress] using hleft)), (.localTee rfl)]
    wasm_steps [(.localGet rfl), (.localGet rfl), .const, .shl, .add,
      (.load32 rfl (by simpa [rightAddress] using hright)), (.localTee rfl),
      (.leU (result := 1) (by simpa [leftAddress, rightAddress] using
        (show (1 : UInt32) = if store.wasm.mem.read32 (leftAddress v + 0) ≤
          store.wasm.mem.read32 (rightAddress v + 0) then 1 else 0 by rw [if_pos hle]))),
      (.brIf (by decide) rfl), .block]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.geU (result := 0) (by simp [UInt32.not_le.mpr hroom])), .brIfZero]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.store32 rfl (by simpa using hdestination))]
    wasm_steps [(.localGet rfl), .const, .add, (.localSet rfl)]
    exact Steps.single (.br rfl)
  refine ⟨rfl, execution.with_unit_cost ?_⟩
  intro before kind after member
  simp only [leftTrace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

/-- Actual right selection has the same physical effects and one fewer block entry. -/
theorem right_choice_cost (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hleft : (leftAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hright : (rightAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hroom : v.count < v.scratchLength)
    (hle : ¬ store.wasm.mem.read32 (leftAddress v + 0) ≤
      store.wasm.mem.read32 (rightAddress v + 0))
    (hostBytes : Config α → Nat → Config α → Nat) :
    rightTrace.length = 31 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) rightTrace
        (tail store v ctx false) 31 := by
  have execution : Steps (head store v ctx) rightTrace (tail store v ctx false) := by
    unfold head tail
    dsimp only
    unfold rightTrace
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    simp only [sortLocals]
    wasm_steps [(.localGet rfl), (.localGet rfl), .const, .shl, .add,
      (.load32 rfl (by simpa [leftAddress] using hleft)), (.localTee rfl)]
    wasm_steps [(.localGet rfl), (.localGet rfl), .const, .shl, .add,
      (.load32 rfl (by simpa [rightAddress] using hright)), (.localTee rfl),
      (.leU (result := 0) (by simpa [leftAddress, rightAddress] using
        (show (0 : UInt32) = if store.wasm.mem.read32 (leftAddress v + 0) ≤
          store.wasm.mem.read32 (rightAddress v + 0) then 1 else 0 by rw [if_neg hle]))),
      .brIfZero]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.geU (result := 0) (by simp [UInt32.not_le.mpr hroom])), .brIfZero]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.store32 rfl (by simpa using hdestination))]
    wasm_steps [(.localGet rfl), .const, .add, (.localSet rfl)]
    exact Steps.single (.br rfl)
  refine ⟨rfl, execution.with_unit_cost ?_⟩
  intro before kind after member
  simp only [rightTrace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- With both source reads and the destination physically available, the actual
comparison selects a normal branch costing at most thirty-two work units. -/
theorem choice_cost (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hleft : (leftAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hright : (rightAddress v).toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdestination : v.destination.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hroom : v.count < v.scratchLength)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace amount, trace.length = amount ∧ amount ≤ 32 ∧
      CostedSteps (byteWork hostBytes) (head store v ctx) trace
        (tail store v ctx (decide (store.wasm.mem.read32 (leftAddress v + 0) ≤
          store.wasm.mem.read32 (rightAddress v + 0)))) amount := by
  by_cases hle : store.wasm.mem.read32 (leftAddress v + 0) ≤
      store.wasm.mem.read32 (rightAddress v + 0)
  · refine ⟨leftTrace, 32, rfl, Nat.le_refl _, ?_⟩
    simpa only [hle, decide_true] using
      (left_choice_cost store v ctx hleft hright hdestination hroom hle hostBytes).2
  · refine ⟨rightTrace, 31, rfl, by decide, ?_⟩
    simpa only [hle, decide_false] using
      (right_choice_cost store v ctx hleft hright hdestination hroom hle hostBytes).2

end Project.Mergesort.MergeChoiceCost
