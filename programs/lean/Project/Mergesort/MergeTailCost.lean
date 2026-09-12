import Project.Mergesort.MergeChoiceCost

/-!
# Operational costs of the generated merge-loop tail

The post-choice indices determine one of three actual branches. These
segments retain the physical store, caller frames, and saved operand stack.
They make no assumptions about an entire loop execution or its termination.
-/

namespace Project.Mergesort.MergeTailCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof
open Project.Mergesort.MergeChoiceCost

/-- Generated control bodies with the explicitly saved operand stack. The
actual sort call uses the empty-stack instance of these frames. -/
def activeContext (ctx : Context) : Context :=
  { ctx with controls :=
      { emptyLoopFrame mergeMainLoopBody [] with belowStack := ctx.stack } ::
      { sortRecursiveBodyFrame with belowStack := ctx.stack } ::
      { sortRecursiveGuardFrame with belowStack := ctx.stack } :: ctx.controls }

def tailHead (store : MachineStore α) (v : ChoiceState) (ctx : Context) : Config α :=
  ⟨.running ⟨sortLocals v.source v.scratch v.length v.scratchLength
      v.mid v.count v.rightBase v.rightLength v.destination v.leftIndex v.rightIndex
      v.oldLeft v.oldRight ctx.stack,
    mergeMainLoopBody.drop 1, ctx.arity, ctx.remainder,
    (activeContext ctx).controls, ctx.calls⟩, store⟩

/-- The tail advances the output pointer/count and records whether the left
input was exhausted. All arithmetic here is the exact UInt32 operation. -/
def advanced (v : ChoiceState) (flag : UInt32) : ChoiceState :=
  { v with count := 1 + v.count, destination := 4 + v.destination, oldLeft := flag }

def exitHead (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (flag : UInt32) : Config α :=
  ⟨.running ⟨sortLocals v.source v.scratch v.length v.scratchLength
      v.mid (1 + v.count) v.rightBase v.rightLength (4 + v.destination)
      v.leftIndex v.rightIndex flag v.oldRight ctx.stack,
    sortBlock4.drop 5, ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

/-- The existing choice certificate ends at exactly this tail entry, with
the selected write and both loaded values retained in the actual state. -/
theorem choice_tail_eq (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (takeLeft : Bool) :
    tail store v (activeContext ctx) takeLeft =
      tailHead
        (selectedStore store v (if takeLeft then
          store.wasm.mem.read32 (leftAddress v + 0) else
          store.wasm.mem.read32 (rightAddress v + 0)))
        { v with
          leftIndex := if takeLeft then 1 + v.leftIndex else v.leftIndex
          rightIndex := if takeLeft then v.rightIndex else 1 + v.rightIndex
          oldLeft := store.wasm.mem.read32 (leftAddress v + 0)
          oldRight := store.wasm.mem.read32 (rightAddress v + 0) } ctx := rfl

def leftExitTrace : List StepKind :=
  [.instruction (.localGet 8), .instruction (.const 4), .instruction .add,
    .instruction (.localSet 8), .instruction (.localGet 5),
    .instruction (.const 1), .instruction .add, .instruction (.localSet 5),
    .instruction (.localGet 9), .instruction (.localGet 4),
    .instruction .geU, .instruction (.localTee 11), .instruction (.br_if 2)]

def continueTrace : List StepKind :=
  leftExitTrace ++ [.instruction (.localGet 10), .instruction (.localGet 7),
    .instruction .ltU, .instruction (.br_if 0)]

def rightExitTrace : List StepKind := continueTrace ++ [.instruction (.br 2)]

/-- Left exhaustion takes the depth-two branch after thirteen transitions.
The enclosing generated loop/body/guard frames are discharged exactly. -/
theorem left_exhausted (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hleft : v.mid ≤ v.leftIndex)
    (hostBytes : Config α → Nat → Config α → Nat) :
    leftExitTrace.length = 13 ∧
      CostedSteps (byteWork hostBytes) (tailHead store v ctx) leftExitTrace
        (exitHead store v ctx 1) 13 := by
  refine ⟨rfl, ?_⟩
  apply Steps.with_unit_cost
  · unfold tailHead exitHead leftExitTrace
    rw [mergeMainLoopBody_tail]
    wasm_steps [(.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), (.localGet rfl),
      (.geU (result := 1) (by simp [hleft])), (.localTee rfl)]
    exact Steps.single (.brIf (by decide) rfl)
  · intro before kind after member
    simp only [leftExitTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Both inputs remain active: seventeen transitions reach the generated
loop body again with its loop frame and all outer frames retained. -/
theorem back_edge (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hleft : v.leftIndex < v.mid) (hright : v.rightIndex < v.rightLength)
    (hostBytes : Config α → Nat → Config α → Nat) :
    continueTrace.length = 17 ∧
      CostedSteps (byteWork hostBytes) (tailHead store v ctx) continueTrace
        (head store (advanced v 0) (activeContext ctx)) 17 := by
  refine ⟨rfl, ?_⟩
  apply Steps.with_unit_cost
  · unfold tailHead head advanced continueTrace leftExitTrace
    simp only [List.cons_append, List.nil_append]
    rw [mergeMainLoopBody_tail]
    wasm_steps [(.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), (.localGet rfl),
      (.geU (result := 0) (by simp [UInt32.not_le.mpr hleft])),
      (.localTee rfl), .brIfZero, (.localGet rfl), (.localGet rfl),
      (.ltU (result := 1) (by simp [hright]))]
    exact Steps.single (.brIf (by decide) rfl)
  · intro before kind after member
    simp only [continueTrace, leftExitTrace, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Right exhaustion takes the final unconditional depth-two branch, after
eighteen transitions. The left-exhaustion flag remains zero. -/
theorem right_exhausted (store : MachineStore α) (v : ChoiceState) (ctx : Context)
    (hleft : v.leftIndex < v.mid) (hright : ¬v.rightIndex < v.rightLength)
    (hostBytes : Config α → Nat → Config α → Nat) :
    rightExitTrace.length = 18 ∧
      CostedSteps (byteWork hostBytes) (tailHead store v ctx) rightExitTrace
        (exitHead store v ctx 0) 18 := by
  refine ⟨rfl, ?_⟩
  apply Steps.with_unit_cost
  · unfold tailHead exitHead rightExitTrace continueTrace leftExitTrace
    simp only [List.cons_append, List.nil_append]
    rw [mergeMainLoopBody_tail]
    wasm_steps [(.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), (.localGet rfl),
      (.geU (result := 0) (by simp [UInt32.not_le.mpr hleft])),
      (.localTee rfl), .brIfZero, (.localGet rfl), (.localGet rfl),
      (.ltU (result := 0) (by simp [hright])), .brIfZero]
    exact Steps.single (.br rfl)
  · intro before kind after member
    simp only [rightExitTrace, continueTrace, leftExitTrace,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Project.Mergesort.MergeTailCost
