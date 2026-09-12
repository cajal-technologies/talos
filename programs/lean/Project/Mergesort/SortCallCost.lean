import Project.Mergesort.SortCostRecurrence

/-!
# Operational overhead around the two recursive sort calls

These scalar segments execute the generated body with arbitrary caller
frames and physical stores. Each preserves the complete store. Recursive
calls and the merge loop are explicit segment boundaries, so their work is
not hidden in the numerical constants below.
-/

namespace Project.Mergesort.SortCallCost

open Wasm Wasm.SmallStep Project.Mergesort.SortProof

def recursiveControls : List ControlFrame :=
  [sortRecursiveBodyFrame, sortRecursiveGuardFrame, sortBlock4Frame,
    sortBlock3Frame, sortBlock2Frame, sortBlock1Frame]

def callerFrame (store : MachineStore α) (locals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) : CallFrame :=
  { locals := { locals with values := stack }, continuation := code,
    resultArity := arity, callerRemainder := remainder, control := controls,
    returningInstance := store.runtime.entry }

private def firstTrace : List StepKind :=
  [.instruction (.call 5), .instruction (.block 0 0 sortBlock1),
    .instruction (.block 0 0 sortBlock2), .instruction (.block 0 0 sortBlock3),
    .instruction (.block 0 0 sortBlock4), .instruction (.localGet 1),
    .instruction (.const 2), .instruction .ltU, .instruction (.br_if 0),
    .instruction (.block 0 0 sortRecursiveGuard),
    .instruction (.block 0 0 sortRecursiveBody),
    .instruction (.localGet 3), .instruction (.localGet 1),
    .instruction (.const 1), .instruction .shrU, .instruction (.localTee 4),
    .instruction .ltU, .instruction (.br_if 0), .instruction (.localGet 0),
    .instruction (.localGet 4), .instruction (.localGet 2),
    .instruction (.localGet 4)]

private theorem shifted_half (n : Nat) (h : n < UInt32.size) :
    UInt32.ofNat n >>> (1 % 32 : UInt32) = UInt32.ofNat (n / 2) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat_of_lt' h,
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.div_le_self n 2) h)]
  rw [Nat.shiftRight_eq_div_pow]
  change n / 2 ^ 1 = n / 2
  simp

/-- Twenty-two actual transitions enter the outer sort call, discharge its
two arithmetic guards, and prepare the left recursive call. The child call
itself has not executed at the endpoint. -/
theorem first_recursive_call_setup (store : MachineStore α)
    (source scratch : UInt32) (n : Nat) (htwo : 2 ≤ n) (hsize : n < UInt32.size)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 22 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨{ callerLocals with values := (.i32 (UInt32.ofNat n) ::
          .i32 scratch :: .i32 (UInt32.ofNat n) :: .i32 source :: stack) },
          .call 5 :: code, arity, remainder, controls, calls⟩,
          store⟩ trace
        ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
          (UInt32.ofNat (n / 2)) 0 0 0 0 0 0 0 0
          [.i32 (UInt32.ofNat (n / 2)), .i32 scratch,
            .i32 (UInt32.ofNat (n / 2)), .i32 source],
          sortRecursiveBody.drop 11, 0, [], recursiveControls,
          callerFrame store callerLocals stack code arity remainder controls :: calls⟩,
          store⟩ 22 := by
  have hnotLt : ¬UInt32.ofNat n < 2 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hsize]
    change ¬n < 2
    omega
  have hhalf : ¬UInt32.ofNat n < UInt32.ofNat (n / 2) := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hsize,
      UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.div_le_self n 2) hsize)]
    omega
  refine ⟨firstTrace, rfl, ?_⟩
  apply Steps.with_unit_cost
  · unfold firstTrace
    apply Steps.cons (Step.call (fn := func2Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    simp only [func2Def, func2, Function.toLocals, Function.numParams]
    wasm_steps [.block, .block, .block, .block, (.localGet rfl), .const,
      (.ltU (result := 0) (by simp [hnotLt])), .brIfZero,
      .block, .block, (.localGet rfl), (.localGet rfl), .const, .shrU]
    rw [shifted_half n hsize]
    wasm_steps [(.localTee rfl), (.ltU (result := 0) (by simp [hhalf])),
      .brIfZero, (.localGet rfl), (.localGet rfl), (.localGet rfl)]
    exact Steps.single (.localGet rfl)
  · intro before kind after member
    simp only [firstTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def secondTrace : List StepKind :=
  [.instruction (.localGet 0), .instruction (.localGet 4),
    .instruction (.const 2), .instruction .shl, .instruction (.localTee 5),
    .instruction .add, .instruction (.localTee 6), .instruction (.localGet 1),
    .instruction (.localGet 4), .instruction .sub, .instruction (.localTee 7),
    .instruction (.localGet 2), .instruction (.localGet 5), .instruction .add,
    .instruction (.localGet 3), .instruction (.localGet 4), .instruction .sub]

/-- After the left child returns, seventeen scalar transitions prepare the
right child's actual pointer and length arguments. Wrapping arithmetic is
recorded exactly; the sort layout proof supplies its no-wrap interpretation. -/
theorem second_recursive_call_setup (store : MachineStore α)
    (source scratch length mid : UInt32)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 17 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨sortLocals source scratch length length mid 0 0 0 0 0 0 0 0 [],
          sortRecursiveBody.drop 12, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨sortLocals source scratch length length mid
          (mid <<< (2 % 32 : UInt32)) ((mid <<< (2 % 32 : UInt32)) + source)
          (length - mid) 0 0 0 0 0
          [.i32 (length - mid), .i32 ((mid <<< (2 % 32 : UInt32)) + scratch),
            .i32 (length - mid), .i32 ((mid <<< (2 % 32 : UInt32)) + source)],
          sortRecursiveBody.drop 29, arity, remainder, controls, calls⟩, store⟩ 17 := by
  refine ⟨secondTrace, rfl, ?_⟩
  apply Steps.with_unit_cost
  · unfold secondTrace
    wasm_steps [(.localGet rfl), (.localGet rfl), .const, .shl,
      (.localTee rfl), .add, (.localTee rfl), (.localGet rfl),
      (.localGet rfl), .sub, (.localTee rfl), (.localGet rfl),
      (.localGet rfl), .add, (.localGet rfl), (.localGet rfl)]
    exact Steps.single .sub
  · intro before kind after member
    simp only [secondTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def mergeSetupTrace : List StepKind :=
  [.instruction (.const 0), .instruction (.localSet 5),
    .instruction (.localGet 2), .instruction (.localSet 8),
    .instruction (.const 0), .instruction (.localSet 9),
    .instruction (.const 0), .instruction (.localSet 10)]

/-- The right child returns to eight scalar initializers before the generated
merge loop. The loop-entry instruction is still pending at the endpoint. -/
theorem merge_setup (store : MachineStore α)
    (source scratch length mid offset rightSource rightLength : UInt32)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 8 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨sortLocals source scratch length length
          mid offset rightSource rightLength 0 0 0 0 0 [],
          sortRecursiveBody.drop 30, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨sortLocals source scratch length length
          mid 0 rightSource rightLength scratch 0 0 0 0 [],
          [.loop 0 0 mergeMainLoopBody], arity, remainder, controls, calls⟩, store⟩ 8 := by
  refine ⟨mergeSetupTrace, rfl, ?_⟩
  apply Steps.with_unit_cost
  · unfold mergeSetupTrace
    wasm_steps [.const, (.localSet rfl), (.localGet rfl), (.localSet rfl),
      .const, (.localSet rfl), .const, (.localSet rfl)]
    exact Steps.refl _
  · intro before kind after member
    simp only [mergeSetupTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Project.Mergesort.SortCallCost
