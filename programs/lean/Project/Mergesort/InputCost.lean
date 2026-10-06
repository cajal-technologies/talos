import Project.Mergesort.DriverProof
import Project.Mergesort.StdIOMemoryEffects
import CodeLib.SepLogic.CostedStepsStdIO
import CodeLib.SepLogic.CostedLoop

/-!
# Actual host-transfer and scalar costs of the generated input reader

The byte charge is the transfer performed by the Universal host, including
zero bytes at EOF. Saved caller frames and the actual updated physical store
are retained at each component boundary.
-/

namespace Project.Mergesort.InputCost

open Wasm Wasm.SmallStep Wasm.SmallStep.CostedStdIO
open Project.Mergesort.DriverProof Project.Mergesort.Representations

def readResult (store : MachineStore Universal.State) (requested pointer : UInt32) :
    MachineStore Universal.State :=
  { store with wasm := readStore store.wasm requested pointer }

def readCount (store : MachineStore Universal.State) (requested : UInt32) : Nat :=
  min requested.toNat store.wasm.host.stdio.input.length

/-- The complete generated read shim, including actual host call and caller
return. Five transitions plus exactly the transferred bytes are charged. -/
theorem read_shim_cost (store : MachineStore Universal.State)
    (pointer requested : UInt32) (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hbound : pointer.toNat + readCount store requested ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length = 5 ∧
      CostedSteps work
        ⟨.running ⟨{ callerLocals with values := .i32 requested :: .i32 pointer :: stack },
          .call 13 :: code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := .i32 (UInt32.ofNat (readCount store requested)) :: stack },
          code, arity, remainder, controls, calls⟩, readResult store requested pointer⟩
        (5 + readCount store requested) := by
  refine ⟨StdIOMemoryEffects.readTrace, rfl, ?_⟩
  have execution := StdIOMemoryEffects.read_shim_cost store callerLocals.params
    callerLocals.locals stack code arity remainder controls calls requested pointer hmodule
    (by rw [hhost]; exact readHost_resolves Project.Mergesort.module 0 (by decide) rfl) hbound
  simpa only [StdIOMemoryEffects.readCount, StdIOMemoryEffects.readFinalStore,
    readCount, readResult, Nat.add_comm] using execution

/-- Actual generated chunk-read prefix, independent of subsequent EOF handling. -/
theorem read_chunk_cost (store : MachineStore Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (hlocal : callerLocals.get 0 = some (.i32 driverBase))
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hbound : (driverBase + 12).toNat + readCount store 256 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length = 9 ∧
      CostedSteps work
        ⟨.running ⟨{ callerLocals with values := stack },
          [.localGet 0, .const 12, .add, .const 256, .call 13] ++ code,
          arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := .i32 (UInt32.ofNat (readCount store 256)) :: stack },
          code, arity, remainder, controls, calls⟩, readResult store 256 (driverBase + 12)⟩
        (9 + readCount store 256) := by
  have scalarRun : Steps
      ⟨.running ⟨{ callerLocals with values := stack },
        [.localGet 0, .const 12, .add, .const 256, .call 13] ++ code,
        arity, remainder, controls, calls⟩, store⟩
      [.instruction (.localGet 0), .instruction (.const 12), .instruction .add,
        .instruction (.const 256)]
      ⟨.running ⟨{ callerLocals with values := .i32 256 :: .i32 (driverBase + 12) :: stack },
        .call 13 :: code, arity, remainder, controls, calls⟩, store⟩ := by
    have hget : ({ callerLocals with values := stack } : Locals).get 0 =
        some (.i32 driverBase) := hlocal
    wasm_steps [(.localGet hget), .const, .add]
    rw [show (12 : UInt32) + driverBase = driverBase + 12 by decide]
    exact Steps.single Step.const
  have prefixCost := scalarRun.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl)
  obtain ⟨trace, hlength, readCost⟩ := read_shim_cost store (driverBase + 12) 256
    callerLocals stack code arity remainder controls calls hmodule hhost hbound
  refine ⟨[.instruction (.localGet 0), .instruction (.const 12), .instruction .add,
      .instruction (.const 256)] ++ trace, ?_, ?_⟩
  · simp only [List.length_append, hlength, List.length_cons, List.length_nil]
  · convert prefixCost.trans readCost using 1
    simp only [List.length_cons, List.length_nil]
    omega

/-- A chunk read always returns a representable length, including zero at EOF. -/
theorem readCount_bound (store : MachineStore Universal.State) : readCount store 256 ≤ 256 :=
  min_le_left _ _

theorem readCount_zero_iff (store : MachineStore Universal.State) :
    readCount store 256 = 0 ↔ store.wasm.host.stdio.input = [] := by
  simp only [readCount, UInt32.reduceToNat, Nat.min_eq_zero_iff, Nat.reduceEqDiff, false_or,
    List.length_eq_zero_iff]

theorem readResult_pages (store : MachineStore Universal.State) (requested pointer : UInt32) :
    (readResult store requested pointer).wasm.mem.pages = store.wasm.mem.pages := rfl

theorem readResult_input (store : MachineStore Universal.State) (requested pointer : UInt32) :
    (readResult store requested pointer).wasm.host.stdio.input =
      store.wasm.host.stdio.input.drop (readCount store requested) := by
  simp only [readResult, readStore, readCount, List.length_take]

/-- The actual chunk read, local-count update and EOF classification. The
generated branch instruction remains pending at this component boundary. -/
theorem read_classify_cost (store : MachineStore Universal.State)
    (dataPtr previousCurrent length aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (stack : List Value) (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hbound : (driverBase + 12).toNat + readCount store 256 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length = 11 ∧
      CostedSteps work
        ⟨.running ⟨func3AppendLocals dataPtr previousCurrent length
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          func3ReadClassifyBody ++ code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨func3AppendLocals dataPtr (UInt32.ofNat (readCount store 256)) length
          aux2 aux4 aux5 aux7 aux8 aux9 aux10
          (.i32 (if readCount store 256 = 0 then 1 else 0) :: stack),
          code, arity, remainder, controls, calls⟩, readResult store 256 (driverBase + 12)⟩
        (11 + readCount store 256) := by
  let L := func3AppendLocals dataPtr previousCurrent length aux2 aux4 aux5 aux7 aux8 aux9 aux10 []
  obtain ⟨trace, hlength, Hread⟩ := read_chunk_cost store L stack ([.localTee 3, .eqz] ++ code)
    arity remainder controls calls rfl hmodule hhost hbound
  have countNat : (UInt32.ofNat (readCount store 256)).toNat = readCount store 256 :=
    UInt32.toNat_ofNat_of_lt' (by have := readCount_bound store; norm_num [UInt32.size]; omega)
  have countZero : UInt32.ofNat (readCount store 256) = 0 ↔ readCount store 256 = 0 := by
    constructor
    · intro h
      have h' := congrArg UInt32.toNat h
      simpa only [countNat, UInt32.toNat_zero] using h'
    · intro h
      rw [h]
      rfl
  have classify : Steps
      ⟨.running ⟨{ L with values := .i32 (UInt32.ofNat (readCount store 256)) :: stack },
        [.localTee 3, .eqz] ++ code, arity, remainder, controls, calls⟩,
        readResult store 256 (driverBase + 12)⟩
      [.instruction (.localTee 3), .instruction .eqz]
      ⟨.running ⟨func3AppendLocals dataPtr (UInt32.ofNat (readCount store 256)) length
        aux2 aux4 aux5 aux7 aux8 aux9 aux10
        (.i32 (if readCount store 256 = 0 then 1 else 0) :: stack),
        code, arity, remainder, controls, calls⟩,
        readResult store 256 (driverBase + 12)⟩ := by
    wasm_steps [(.localTee rfl)]
    exact Steps.single (Step.eqz (by simp [countZero]))
  have classifyCost := classify.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)
  refine ⟨trace ++ [.instruction (.localTee 3), .instruction .eqz], ?_, ?_⟩
  · simp only [List.length_append, hlength, List.length_cons, List.length_nil]
  · simpa only [L, func3AppendLocals, func3ReadClassifyBody, List.cons_append, List.nil_append,
      List.length_cons, List.length_nil, show 9 + readCount store 256 + (1 + (1 + 0)) =
        11 + readCount store 256 by omega] using Hread.trans classifyCost

end Project.Mergesort.InputCost
