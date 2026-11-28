import Project.Mergesort.OutputCost

/-! # Work of the generated stdio reader

Call 13 enters the generated reader, invokes the Universal host, and returns
to the caller. The host charge counts bytes actually transferred.
-/

namespace Project.Mergesort.StdIOMemoryEffects

open Wasm Wasm.SmallStep Wasm.SmallStep.CostedStdIO

/-- Exact generated reader body and result signature. -/
theorem read_shim_generated :
    func10 = [.localGet 1, .localGet 0, .call 0] ∧
      func10Def.results = [.i32] := ⟨rfl, rfl⟩

def readTrace : List StepKind :=
  [.instruction (.call 13), .instruction (.localGet 1),
    .instruction (.localGet 0), .host 0, .administrative .returnFromCall]

/-- Actual host transfer count; the requested length need not be available. -/
def readCount (store : MachineStore Universal.State) (length : UInt32) : Nat :=
  min length.toNat store.wasm.host.stdio.input.length

def readFinalStore (store : MachineStore Universal.State) (length pointer : UInt32) :
    MachineStore Universal.State :=
  { store with wasm := readStore store.wasm length pointer }

/-- The returned count is exact in UInt32, including a maximal request. -/
theorem read_count_toNat (store : MachineStore Universal.State) (length : UInt32) :
    (UInt32.ofNat (readCount store length)).toNat = readCount store length := by
  apply UInt32.toNat_ofNat_of_lt'
  have hlength := length.toBitVec.isLt
  change length.toNat < UInt32.size at hlength
  exact lt_of_le_of_lt (min_le_left _ _) hlength

/-- A successful actual call 13 returns its transfer count and preserves all
caller frames. Its physical bound covers the bytes actually read, not the
possibly larger requested length. -/
theorem read_shim_cost
    (store : MachineStore Universal.State)
    (params localValues values : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (length pointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[0]? = some readHost)
    (hbound : pointer.toNat + readCount store length ≤ store.wasm.mem.pages * 65536) :
    CostedSteps work
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 13 :: code, arity, remainder, controls, calls⟩, store⟩
      readTrace
      ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (readCount store length)) :: values⟩,
        code, arity, remainder, controls, calls⟩, readFinalStore store length pointer⟩
      (readCount store length + 5) := by
  let caller : CallFrame :=
    { locals := ⟨params, localValues, values⟩, continuation := code,
      resultArity := arity, callerRemainder := remainder, control := controls,
      returningInstance := store.runtime.entry }
  have preExecution : Steps
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 13 :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction (.call 13), .instruction (.localGet 1), .instruction (.localGet 0)]
      ⟨.running ⟨⟨[.i32 pointer, .i32 length], [], [.i32 pointer, .i32 length]⟩,
        [.call 0], 1, [], [], caller :: calls⟩, store⟩ := by
    wasm_steps [(.call (fn := func10Def) (by rw [hmodule]; decide)
      (by rw [hmodule]; rfl)), (.localGet rfl)]
    exact Steps.single (.localGet rfl)
  have prefixCost := preExecution.with_cost_eq_length (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl)
  have transfer := read_call_costed store 0 [.i32 pointer, .i32 length] [] [] []
    1 [] [] (caller :: calls) length pointer
    (by rw [hmodule]; decide) (by simpa only [hmodule] using
      (show Project.Mergesort.module.imports[0] = StdIO.imports[0] from rfl)) hhost
    (by simpa only [List.length_take, readCount] using hbound)
  have suffix : CostedSteps work
      ⟨.running ⟨⟨[.i32 pointer, .i32 length], [],
          [.i32 (UInt32.ofNat (readCount store length))]⟩,
        [], 1, [], [], caller :: calls⟩, readFinalStore store length pointer⟩
      [.administrative .returnFromCall]
      ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (readCount store length)) :: values⟩,
        code, arity, remainder, controls, calls⟩, readFinalStore store length pointer⟩ 1 :=
    CostedSteps.single (.returnFromCallFallthrough rfl)
  simp only [List.length_take] at transfer
  convert prefixCost.trans (transfer.trans suffix) using 1 <;>
    simp [readTrace, readCount]
  omega

end Project.Mergesort.StdIOMemoryEffects
