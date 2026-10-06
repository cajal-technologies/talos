import Project.Mergesort.SortProof
import CodeLib.SepLogic.CostedLoop

/-!
# Cost of the generated sort copy-back

The checked instruction prefix discharges the generated equality and nonzero
length guards, then executes the actual bulk copy with its byte-sensitive cost.
The endpoint is the enclosing block's empty body; administrative return is a
separate segment. Physical access bounds remain explicit component premises.
-/

namespace Project.Mergesort.SortCopyCost

open Wasm Wasm.SmallStep
open Project.Mergesort.SortProof

private def copyPrefixTrace : List StepKind :=
  [.instruction (.localGet 1), .instruction (.localGet 3), .instruction .ne,
    .instruction (.br_if 3), .instruction (.localGet 1), .instruction (.const 2),
    .instruction .shl, .instruction (.localTee 5), .instruction .eqz,
    .instruction (.br_if 0), .instruction (.localGet 0),
    .instruction (.localGet 2), .instruction (.localGet 5)]

/-- Fourteen transitions and four bytes per word for the actual generated
copy-back, retaining the physical store update and enclosing caller context. -/
theorem sort_copyback_cost {α : Type} (store : MachineStore α)
    (source scratch : UInt32) (n : Nat)
    (v4 v5 v6 v7 v8 v9 v10 v11 v12 : UInt32)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hpositive : 0 < n) (hfit : 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 14 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
            v4 v5 v6 v7 v8 v9 v10 v11 v12 [],
          sortBlock4.drop 7, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
            v4 (4 * UInt32.ofNat n) v6 v7 v8 v9 v10 v11 v12 [],
          [], arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with
            mem := store.wasm.mem.copy source.toNat scratch.toNat (4 * n) } }⟩
        (14 + 4 * n) := by
  have hbytes : (4 * UInt32.ofNat n : UInt32).toNat = 4 * n := by
    change (UInt32.ofNat 4 * UInt32.ofNat n).toNat = _
    rw [← UInt32.ofNat_mul]
    exact UInt32.toNat_ofNat_of_lt hfit
  have hnonzero : (4 * UInt32.ofNat n : UInt32) ≠ 0 := by
    intro hz
    have impossible := congrArg UInt32.toNat hz
    rw [hbytes] at impossible
    simp only [UInt32.reduceToNat] at impossible
    omega
  have copyPrefixExecution : Steps
      ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
          v4 v5 v6 v7 v8 v9 v10 v11 v12 [],
        sortBlock4.drop 7, arity, remainder, controls, calls⟩, store⟩ copyPrefixTrace
      ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
          v4 (4 * UInt32.ofNat n) v6 v7 v8 v9 v10 v11 v12
          [.i32 (4 * UInt32.ofNat n), .i32 scratch, .i32 source],
        [.memoryCopy], arity, remainder, controls, calls⟩, store⟩ := by
    rw [sortBlock4_after_merge]
    wasm_steps [(.localGet rfl), (.localGet rfl), (.ne (result := 0) (by simp)), .brIfZero,
      (.localGet rfl), .const, .shl]
    rw [Wasm.MemRegion.shl2_eq_mul4]
    wasm_steps [(.localTee rfl), (.eqz (result := 0) (by simp [hnonzero])), .brIfZero,
      (.localGet rfl), (.localGet rfl)]
    exact Steps.single (.localGet rfl)
  have prefixCost := copyPrefixExecution.with_unit_cost (charge := byteWork hostBytes) (by
    intro before kind after member
    simp only [copyPrefixTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> rfl)
  have copyCost := memoryCopy32_costed store
    [.i32 source, .i32 (UInt32.ofNat n), .i32 scratch, .i32 (UInt32.ofNat n)]
    [.i32 v4, .i32 (4 * UInt32.ofNat n), .i32 v6, .i32 v7, .i32 v8,
      .i32 v9, .i32 v10, .i32 v11, .i32 v12]
    [] [] arity remainder controls calls source scratch (4 * UInt32.ofNat n)
    (by simpa only [hbytes] using hsource)
    (by simpa only [hbytes] using hscratch) hostBytes
  refine ⟨copyPrefixTrace ++ [.instruction .memoryCopy], rfl, ?_⟩
  simpa [copyPrefixTrace, hbytes, sortLocals, ← Nat.add_assoc] using
    prefixCost.trans copyCost


/-- Include the enclosing block exit and actual caller resumption after copying.
This is the complete post-merge suffix, with sixteen transitions and `4*n`
additional bulk-byte work. -/
theorem sort_copyback_return_cost {α : Type} (store : MachineStore α)
    (source scratch : UInt32) (n : Nat)
    (v4 v5 v6 v7 v8 v9 v10 v11 v12 : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hpositive : 0 < n) (hfit : 4 * n < UInt32.size)
    (hsource : source.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    let caller : CallFrame :=
      { locals := { callerLocals with values := stack }, continuation := code,
        resultArity := arity, callerRemainder := remainder, control := controls,
        returningInstance := store.runtime.entry }
    ∃ trace, trace.length = 16 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
            v4 v5 v6 v7 v8 v9 v10 v11 v12 [],
          sortBlock4.drop 7, 0, [],
          [sortBlock4Frame, sortBlock3Frame, sortBlock2Frame, sortBlock1Frame],
          caller :: calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with
            mem := store.wasm.mem.copy source.toNat scratch.toNat (4 * n) } }⟩
        (16 + 4 * n) := by
  intro caller
  let copied : MachineStore α :=
    { store with wasm := { store.wasm with
      mem := store.wasm.mem.copy source.toNat scratch.toNat (4 * n) } }
  obtain ⟨copyTrace, hlength, Hcopy⟩ := sort_copyback_cost store source scratch n
    v4 v5 v6 v7 v8 v9 v10 v11 v12 0 []
    [sortBlock4Frame, sortBlock3Frame, sortBlock2Frame, sortBlock1Frame]
    (caller :: calls) hpositive hfit hsource hscratch hostBytes
  have returned : Steps
      ⟨.running ⟨sortLocals source scratch (UInt32.ofNat n) (UInt32.ofNat n)
          v4 (4 * UInt32.ofNat n) v6 v7 v8 v9 v10 v11 v12 [],
        [], 0, [],
        [sortBlock4Frame, sortBlock3Frame, sortBlock2Frame, sortBlock1Frame],
        caller :: calls⟩, copied⟩
      [.administrative .exitControl, .administrative .returnFromCall]
      ⟨.running ⟨{ callerLocals with values := stack },
        code, arity, remainder, controls, calls⟩, copied⟩ := by
    apply Steps.cons (Step.exitControl rfl)
    exact Steps.single (Step.returnFromCallExplicit rfl)
  have returnCost := returned.with_unit_cost (charge := byteWork hostBytes) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)
  refine ⟨copyTrace ++ [.administrative .exitControl,
    .administrative .returnFromCall], ?_, ?_⟩
  · simp only [List.length_append, hlength, List.length_cons, List.length_nil]
  · simpa [copied, Nat.add_right_comm] using Hcopy.trans returnCost

end Project.Mergesort.SortCopyCost
