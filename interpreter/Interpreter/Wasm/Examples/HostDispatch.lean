import Interpreter.Wasm.SmallStep

/-! ## Example: host-function dispatch

Concrete checks cover host return, host trap, host exception propagation,
and host memory reads. The symbolic theorem is parametric over any host
environment satisfying the `inc` contract and constructs an authoritative
relational host step.
-/

namespace Wasm
open SmallStep
namespace HostDispatch

def incHost : HostFn Unit :=
  { params := [.i32]
    results := [.i32]
    invoke := fun st args => match args with
      | [.i32 x] => .Return [.i32 (x + 1)] st
      | _ => .Trap st "inc: bad arity" }

def incEnv : HostEnv Unit := { funcs := [incHost] }

def incModule : Module :=
  { imports := [{
      «module» := "env", name := "inc"
      params := [.i32], results := [.i32] }]
    funcs := [{
      params := [.i32]
      body := [.localGet 0, .call 0]
      results := [.i32] }] }

def abortHost : HostFn Unit :=
  { invoke := fun st _ => .Trap st "host abort" }

def abortEnv : HostEnv Unit := { funcs := [abortHost] }

def abortModule : Module :=
  { imports := [{ «module» := "env", name := "abort" }]
    funcs := [{ body := [.call 0, .unreachable] }] }

def throwHost : HostFn Unit :=
  { invoke := fun st _ => .Throw st 0 [.i32 7] }

def throwEnv : HostEnv Unit := { funcs := [throwHost] }

def throwTailModule : Module :=
  { imports := [{ «module» := "env", name := "throw" }]
    tags := [{ params := [.i32] }]
    funcs := [{ body := [.returnCall 0] }] }

def throwIndirectModule : Module :=
  { types := [{}]
    imports := [{ «module» := "env", name := "throw" }]
    tags := [{ params := [.i32] }]
    tables := [{ min := 1 }]
    elements := [{
      tableIdx := some 0
      offset := some 0
      funcs := [some 0] }]
    funcs := [{ body := [.const 0, .callIndirect 0 0] }] }

def throwIndirectTailModule : Module :=
  { throwIndirectModule with
    funcs := [{ body := [.const 0, .returnCallIndirect 0 0] }] }

def throwCallRefModule : Module :=
  { types := [{}]
    imports := [{ «module» := "env", name := "throw" }]
    tags := [{ params := [.i32] }]
    funcs := [{ body := [.refFunc 0, .callRef 0] }] }

def throwReturnCallRefModule : Module :=
  { throwCallRefModule with
    funcs := [{ body := [.refFunc 0, .returnCallRef 0] }] }

def memLoadHost : HostFn Unit :=
  { params := [.i32]
    results := [.i32]
    invoke := fun st args => match args with
      | [.i32 addr] =>
        if addr.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "memLoad: out of bounds"
        else
          .Return [.i32 (st.mem.read32 addr)] st
      | _ => .Trap st "memLoad: bad arity" }

def memLoadEnv : HostEnv Unit := { funcs := [memLoadHost] }

def memLoadModule : Module :=
  { imports := [{
      «module» := "env", name := "memLoad"
      params := [.i32], results := [.i32] }]
    funcs := [{
      params := [.i32]
      body := [.localGet 0, .call 0]
      results := [.i32] }]
    memory := some {
      pagesMin := 1
      data := [{ offset := some 0, bytes := [42, 0, 0, 0] }] } }

private def internalConfig (m : Module) (env : HostEnv Unit)
    (args : List Value) : Config Unit :=
  { expr := .running
      { locals := m.funcs[0]!.toLocals args.reverse
        code := m.funcs[0]!.body
        resultArity := m.funcs[0]!.results.length
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := m, host := env }], entry := ⟨0⟩ }
        wasm := m.initialStore } }

def incConfig : Config Unit :=
  internalConfig incModule incEnv [.i32 41]

def abortConfig : Config Unit :=
  internalConfig abortModule abortEnv []

def throwTailConfig : Config Unit :=
  internalConfig throwTailModule throwEnv []

def throwIndirectConfig : Config Unit :=
  internalConfig throwIndirectModule throwEnv []

def throwIndirectTailConfig : Config Unit :=
  internalConfig throwIndirectTailModule throwEnv []

def throwCallRefConfig : Config Unit :=
  internalConfig throwCallRefModule throwEnv []

def throwReturnCallRefConfig : Config Unit :=
  internalConfig throwReturnCallRefModule throwEnv []

def memLoadConfig : Config Unit :=
  internalConfig memLoadModule memLoadEnv [.i32 0]

theorem inc_returns_plus_one :
    (runSteps 3 incConfig).result.values? = some [.i32 42] := by
  native_decide

theorem abort_propagates_trap :
    (match (runSteps 1 abortConfig).result with
      | .trapped reason _ => some reason.message
      | _ => none) = some "host abort" := by
  native_decide

theorem abort_trapsWith :
    TrapsWith abortConfig (.host "host abort")
      (fun store => store = abortConfig.store) := by
  apply runSteps_trapped_trapsWith (fuel := 1)
    (store := abortConfig.store) <;> rfl

theorem imported_tail_call_propagates_exception :
    (runSteps 2 throwTailConfig).result =
      .trapped (.uncaughtException 0 [.i32 7]) throwTailConfig.store := by
  rfl

theorem imported_tail_call_exception_trapsWith :
    TrapsWith throwTailConfig (.uncaughtException 0 [.i32 7])
      (fun store => store = throwTailConfig.store) := by
  apply runSteps_trapped_trapsWith imported_tail_call_propagates_exception
  rfl

theorem imported_indirect_call_propagates_exception :
    (runSteps 3 throwIndirectConfig).result =
      .trapped (.uncaughtException 0 [.i32 7]) throwIndirectConfig.store := by
  rfl

theorem imported_indirect_call_exception_trapsWith :
    TrapsWith throwIndirectConfig (.uncaughtException 0 [.i32 7])
      (fun store => store = throwIndirectConfig.store) := by
  apply runSteps_trapped_trapsWith imported_indirect_call_propagates_exception
  rfl

theorem remaining_imported_call_forms_propagate_exceptions :
    (runSteps 3 throwIndirectTailConfig).result =
        .trapped (.uncaughtException 0 [.i32 7])
          throwIndirectTailConfig.store ∧
      (runSteps 3 throwCallRefConfig).result =
        .trapped (.uncaughtException 0 [.i32 7])
          throwCallRefConfig.store ∧
      (runSteps 3 throwReturnCallRefConfig).result =
        .trapped (.uncaughtException 0 [.i32 7])
          throwReturnCallRefConfig.store := by
  exact ⟨rfl, rfl, rfl⟩

theorem memLoad_reads_caller_memory :
    (runSteps 3 memLoadConfig).result.values? = some [.i32 42] := by
  native_decide

def incCallConfig (env : HostEnv Unit) (st : Store Unit)
    (n : UInt32) : Config Unit :=
  { expr := .running
      { locals := { values := [.i32 n] }
        code := [.call 0]
        resultArity := 1
        callerRemainder := [] }
    store := { runtime := { instances := #[{ module := incModule, host := env }], entry := ⟨0⟩ }, wasm := st } }

def incContract : HostContract Unit :=
  fun st args result =>
    ∀ x, args = [.i32 x] →
      result = .Return [.i32 (x + 1)] st

def incSpec : HostSpec Unit := { contracts := [incContract] }

theorem incHost_satisfies : incEnv.Satisfies incModule incSpec := by
  intro i hi
  have hi0 : i = 0 := by simpa [incModule] using hi
  subst i
  refine ⟨incHost, incContract, rfl, rfl, ?_⟩
  intro st args x hargs
  subst args
  rfl

private theorem inc_import_exists : 0 < incModule.imports.length := by
  decide

theorem inc_call_steps_abstract
    (env : HostEnv Unit) (hSat : env.Satisfies incModule incSpec)
    (st : Store Unit) (n : UInt32) :
    Steps (incCallConfig env st n)
      [(.host 0), (.administrative .finish)]
      ⟨.done [.i32 (n + 1)], (incCallConfig env st n).store⟩ := by
  obtain ⟨hostFunction, hhost, hcontract⟩ :=
    hSat.lookup_contract (i := 0) (by decide) (c := incContract) rfl
  have hinvoke :
      hostFunction.invoke st [.i32 n] =
        .Return [.i32 (n + 1)] st :=
    hcontract st [.i32 n] n rfl
  apply Steps.cons (.callHostReturn inc_import_exists rfl hhost hinvoke)
  exact Steps.cons .finish (Steps.refl _)

theorem inc_call_terminates_abstract
    (env : HostEnv Unit) (hSat : env.Satisfies incModule incSpec)
    (st : Store Unit) (n : UInt32) :
    TerminatesWith (incCallConfig env st n)
      (fun values store =>
        values = [.i32 (n + 1)] ∧ store.wasm = st) := by
  refine ⟨_, _, _, inc_call_steps_abstract env hSat st n, rfl, rfl⟩

theorem inc_call_partial_abstract
    (env : HostEnv Unit) (hSat : env.Satisfies incModule incSpec)
    (st : Store Unit) (n : UInt32) :
    PartiallyMeets (incCallConfig env st n)
      (fun values store =>
        values = [.i32 (n + 1)] ∧ store.wasm = st) := by
  intro trace values store execution
  obtain ⟨rfl, rfl⟩ :=
    steps_done_deterministic
      (inc_call_steps_abstract env hSat st n) execution
  exact ⟨rfl, rfl⟩

end HostDispatch
end Wasm
