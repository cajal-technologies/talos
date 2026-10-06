import Interpreter.Wasm.SmallStep

/-! ## Example: cross-instance tail calls

    Two hand-built modules exercise the three new cross-instance tail-call
    constructors (`returnCallCrossInstance`, `returnCallIndirectFuncAddrCrossInstance`,
    `returnCallRefCrossInstance`) as well as the cross-instance type-mismatch trap
    (`returnCallIndirectFuncAddrCrossInstanceTypeMismatch`).

    Module A (instance 0) exports one function `inc` that adds 1 to its i32
    argument.  Module B (instance 1) imports `inc` and wraps it in four
    tail-calling functions that reach it via `return_call`, `return_call_indirect`,
    and `return_call_ref`.

    Each test: an explicit relational `Steps` proof tracing the cross-instance
    dispatch, plus a `decide +kernel` check pinning the returned value and the
    final `runtime.entry` (which ends at ⟨0⟩, the callee's instance, because a
    tail call at the outermost frame inherits the empty call stack — there is no
    return frame to restore the caller's instance). -/

namespace Wasm
open SmallStep

namespace CrossInstanceTailCall

/-! ### Module and instance definitions -/

def Incr : Program := [.localGet 0, .const 1, .add]

/-- The callee: one function `inc` with type `(param i32) (result i32)`. -/
def m_a : Module :=
  { funcs := [{ params := [.i32], body := Incr, results := [.i32] }]
    exports := [{ name := "inc", funcIdx := 0 }] }

/-- The caller: imports `inc`, holds it in a table, and exposes four wrappers. -/
def m_b : Module :=
  { imports  := [{ «module» := "a", name := "inc", params := [.i32], results := [.i32] }]
    types    := [{ params := [.i32], results := [.i32] }   -- 0: matches inc
               , { params := [],     results := [.i32] }]  -- 1: does not match
    tables   := [{ min := 1 }]
    elements := [{ tableIdx := some 0, offset := some 0, funcs := [some 0] }]
    funcs    :=
      [ { params := [.i32], body := [.localGet 0, .returnCall 0],
          results := [.i32] }                                             -- 0: via return_call
      , { params := [.i32], body := [.localGet 0, .const 0,
            .returnCallIndirect 0 0], results := [.i32] }                 -- 1: via return_call_indirect (match)
      , { params := [.i32], body := [.localGet 0, .const 0,
            .returnCallIndirect 1 0], results := [.i32] }                 -- 2: via return_call_indirect (mismatch)
      , { params := [.i32], body := [.localGet 0, .refFunc 0,
            .returnCallRef 0], results := [.i32] }                        -- 3: via return_call_ref
      ] }

/-- Instance A: no imports; owns function address 0. -/
def inst_a : ModuleInstance Unit := { module := m_a, host := {}, funcaddrs := #[0] }

/-- Instance B: resolves import 0 to instance 0's function 0, so its import
slot aliases address 0; its own four functions get the fresh addresses 1–4. -/
def inst_b : ModuleInstance Unit :=
  { module := m_b, host := {}, resolvedImports := #[.wasm ⟨0⟩ 0]
    funcaddrs := #[0, 1, 2, 3, 4] }

/-- The addresses above are exactly what `instantiate` allocates when it links
`m_b` against `inst_a`, so the examples below do not rely on the identity
default (which would make both instances own address 0). -/
theorem inst_b_from_instantiate :
    ((instantiate
        ⟨.done [], { runtime := { instances := #[inst_a], entry := ⟨0⟩ }
                     wasm := m_b.initialStore }⟩
        m_b {} [("a", ⟨0⟩)]).toOption.map
      fun r => (r.2, r.1.store.runtime.instances.map (·.funcaddrs))) =
      some (⟨1⟩, #[inst_a.funcaddrs, inst_b.funcaddrs]) := by
  decide +kernel

theorem runtime_wellFormed :
    ({ instances := #[inst_a, inst_b], entry := ⟨1⟩ } : RuntimeEnv Unit).funcaddrsWellFormed =
      true := by
  decide +kernel

/-- The two-instance store with B as the current entry (the caller). -/
def callerStore : MachineStore Unit :=
  { runtime := { instances := #[inst_a, inst_b], entry := ⟨1⟩ }
    wasm := m_b.initialStore }

/-- After the cross-instance tail call the entry is A's instance (⟨0⟩). -/
def calleeStore : MachineStore Unit :=
  { runtime := { instances := #[inst_a, inst_b], entry := ⟨0⟩ }
    wasm := m_b.initialStore }

def returnCallConfig (n : UInt32) : Config Unit :=
  { expr  := .running { locals := { params := [.i32 n] }
                        code := [.localGet 0, .returnCall 0]
                        resultArity := 1, callerRemainder := [] }
    store := callerStore }

def returnCallIndirectConfig (n : UInt32) : Config Unit :=
  { expr  := .running { locals := { params := [.i32 n] }
                        code := [.localGet 0, .const 0, .returnCallIndirect 0 0]
                        resultArity := 1, callerRemainder := [] }
    store := callerStore }

def returnCallIndirectMismatchConfig (n : UInt32) : Config Unit :=
  { expr  := .running { locals := { params := [.i32 n] }
                        code := [.localGet 0, .const 0, .returnCallIndirect 1 0]
                        resultArity := 1, callerRemainder := [] }
    store := callerStore }

def returnCallRefConfig (n : UInt32) : Config Unit :=
  { expr  := .running { locals := { params := [.i32 n] }
                        code := [.localGet 0, .refFunc 0, .returnCallRef 0]
                        resultArity := 1, callerRemainder := [] }
    store := callerStore }

/-! ### (a) return_call cross-instance -/

private theorem return_call_steps (n : UInt32) :
    Steps (returnCallConfig n)
      [.instruction (.localGet 0), .administrative .callCrossInstance,
       .instruction (.localGet 0), .instruction (.const 1), .instruction .add,
       .administrative .finish]
      ⟨.done [.i32 (n + 1)], calleeStore⟩ := by
  wasm_steps [(.localGet rfl)]
  apply Steps.cons (.returnCallCrossInstance (by decide) rfl (by decide) rfl rfl rfl)
  wasm_steps [(.localGet rfl), .const, .add, .finish]
  simpa [returnCallConfig, callerStore, calleeStore, inst_a, inst_b, m_a, m_b, Incr,
         Function.toLocals, UInt32.add_comm] using
    Steps.refl ⟨.done [.i32 (n + 1)], calleeStore⟩

theorem return_call_runs :
    (runSteps 6 (returnCallConfig 7)).result.values? = some [.i32 8] ∧
    (runSteps 6 (returnCallConfig 7)).result.finalConfig?.map (·.store.runtime.entry) =
      some ⟨0⟩ := by
  decide +kernel

theorem return_call_terminates (n : UInt32) :
    TerminatesWith (returnCallConfig n) (fun values _ => values = [.i32 (n + 1)]) :=
  runSteps_values_terminates
    (congrArg RunnerResult.values? (runSteps_eq_success_of_steps (return_call_steps n)))

/-! ### (b) return_call_indirect cross-instance (type match) -/

private theorem return_call_indirect_steps (n : UInt32) :
    Steps (returnCallIndirectConfig n)
      [.instruction (.localGet 0), .instruction (.const 0),
       .administrative .callCrossInstance,
       .instruction (.localGet 0), .instruction (.const 1), .instruction .add,
       .administrative .finish]
      ⟨.done [.i32 (n + 1)], calleeStore⟩ := by
  wasm_steps [(.localGet rfl), .const]
  apply Steps.cons
    (.returnCallIndirectFuncAddrCrossInstance (owner := ⟨0⟩) (fnIdx := 0) rfl rfl rfl (by decide +kernel)
      (by decide) rfl rfl (by decide) rfl (by decide))
  wasm_steps [(.localGet rfl), .const, .add, .finish]
  simpa [returnCallIndirectConfig, callerStore, calleeStore, inst_a, inst_b, m_a, m_b, Incr,
         Function.toLocals, UInt32.add_comm] using
    Steps.refl ⟨.done [.i32 (n + 1)], calleeStore⟩

theorem return_call_indirect_runs :
    (runSteps 7 (returnCallIndirectConfig 7)).result.values? = some [.i32 8] ∧
    (runSteps 7 (returnCallIndirectConfig 7)).result.finalConfig?.map (·.store.runtime.entry) =
      some ⟨0⟩ := by
  decide +kernel

theorem return_call_indirect_terminates (n : UInt32) :
    TerminatesWith (returnCallIndirectConfig n) (fun values _ => values = [.i32 (n + 1)]) :=
  runSteps_values_terminates
    (congrArg RunnerResult.values? (runSteps_eq_success_of_steps (return_call_indirect_steps n)))

/-! ### (b) return_call_indirect type mismatch (cross-instance) -/

private theorem return_call_indirect_mismatch_steps (n : UInt32) :
    Steps (returnCallIndirectMismatchConfig n)
      [.instruction (.localGet 0), .instruction (.const 0),
       .instruction (.returnCallIndirect 1 0)]
      ⟨.trapped .indirectCallTypeMismatch, callerStore⟩ := by
  wasm_steps [(.localGet rfl), .const]
  exact Steps.cons
    (.returnCallIndirectFuncAddrCrossInstanceTypeMismatch (owner := ⟨0⟩) (fnIdx := 0) rfl rfl rfl
      (by decide +kernel) (by decide) rfl rfl (by decide) rfl (by decide))
    (Steps.refl _)

theorem return_call_indirect_mismatch_runs :
    (runSteps 3 (returnCallIndirectMismatchConfig 7)).result.trapReason? =
      some .indirectCallTypeMismatch := by
  decide +kernel

theorem return_call_indirect_mismatch_trapsWith (n : UInt32) :
    TrapsWith (returnCallIndirectMismatchConfig n) .indirectCallTypeMismatch
      (fun store => store = callerStore) :=
  TrapsWith.of_steps (return_call_indirect_mismatch_steps n) rfl

/-! ### (c) return_call_ref cross-instance -/

private theorem return_call_ref_steps (n : UInt32) :
    Steps (returnCallRefConfig n)
      [.instruction (.localGet 0), .instruction (.refFunc 0),
       .administrative .callCrossInstance,
       .instruction (.localGet 0), .instruction (.const 1), .instruction .add,
       .administrative .finish]
      ⟨.done [.i32 (n + 1)], calleeStore⟩ := by
  wasm_steps [(.localGet rfl)]
  apply Steps.cons (Step.refFunc (addr := 0) (by decide +kernel))
  apply Steps.cons (.returnCallRefCrossInstance (owner := ⟨0⟩) (fnIdx := 0) (by decide +kernel) (by decide) rfl
    (by decide) rfl)
  wasm_steps [(.localGet rfl), .const, .add, .finish]
  simpa [returnCallRefConfig, callerStore, calleeStore, inst_a, inst_b, m_a, m_b, Incr,
         Function.toLocals, UInt32.add_comm] using
    Steps.refl ⟨.done [.i32 (n + 1)], calleeStore⟩

theorem return_call_ref_runs :
    (runSteps 7 (returnCallRefConfig 7)).result.values? = some [.i32 8] ∧
    (runSteps 7 (returnCallRefConfig 7)).result.finalConfig?.map (·.store.runtime.entry) =
      some ⟨0⟩ := by
  decide +kernel

theorem return_call_ref_terminates (n : UInt32) :
    TerminatesWith (returnCallRefConfig n) (fun values _ => values = [.i32 (n + 1)]) :=
  runSteps_values_terminates
    (congrArg RunnerResult.values? (runSteps_eq_success_of_steps (return_call_ref_steps n)))

end CrossInstanceTailCall
end Wasm
