import Interpreter.Wasm.SmallStep

/-! ## Example: store-wide function addresses across three instances

Regression checks for `instantiate`'s address allocation and for
cross-instance dispatch through `call_ref` / `call_indirect` (and their tail
forms) when the target address belongs to another instance.

* Instance 0 (`X`) owns one function `x` returning `100`.
* Instance 1 (`E`) imports the host function `seven` (index 0) and `X.x`
  (index 1, a `.wasm` alias), and owns `e` returning `42` (index 2, exported).
* Instance 2 (`I`) imports `E.e` (index 0) and owns one function.

`instantiate` gives `E` the addresses `#[1, 0, 2]` (fresh host slot, alias of
`x`, fresh `e`) and `I` the addresses `#[2, 3]`: `I`'s import aliases `e`'s
address, which sits at `E.funcaddrs[E.imports.length + 0]`. Indexing
`E.funcaddrs` with the *local* index `0` instead would alias `I`'s import to
`E`'s host import `seven`.

Address `1` is owned by `E`'s **host import** slot. Calling it from `I`
through `call_ref` / `call_indirect` (or their tail forms) must invoke the host
function `seven`, not one of `E`'s wasm functions. -/

namespace Wasm
open SmallStep

namespace CrossInstanceFuncaddrs

def sevenHost : HostFn Unit :=
  { results := [.i32], invoke := fun st _ => .Return [.i32 7] st }

def envE : HostEnv Unit := { funcs := [sevenHost] }

def mX : Module :=
  { funcs := [{ results := [.i32], body := [.const 100] }]
    exports := [{ name := "x", funcIdx := 0 }] }

def mE : Module :=
  { imports :=
      [ { «module» := "env", name := "seven", results := [.i32] }
      , { «module» := "X", name := "x", results := [.i32] } ]
    funcs := [{ results := [.i32], body := [.const 42] }]
    exports := [{ name := "e", funcIdx := 2 }] }

def mI : Module :=
  { imports := [{ «module» := "E", name := "e", results := [.i32] }]
    types := [{ results := [.i32] }, { params := [.i32], results := [.i32] }]
    tables := [{ min := 1 }]
    funcs := [{ results := [.i32], body := [.refFunc 0, .callRef 0] }] }

def emptyStore : Store Unit :=
  { globals := { globals := [] }, mem := Mem.empty 0, host := () }

/-- `X` alone; a single instance may keep the identity `funcaddrs`. -/
def instX : ModuleInstance Unit := { module := mX, host := {} }

def baseConfig : Config Unit :=
  { expr := .done [], store := { runtime := { instances := #[instX], entry := ⟨0⟩ }, wasm := emptyStore } }

def registry : ImportRegistry := [("X", ⟨0⟩), ("E", ⟨1⟩)]

/-- Link `E` then `I` on top of `X` with `instantiate`. -/
def linked : Except InstantiationError (Config Unit) := do
  let (afterE, _) ← instantiate baseConfig mE envE registry
  let (afterI, _) ← instantiate afterE mI {} registry
  return afterI

/-! ### What `instantiate` allocates -/

theorem linked_funcaddrs :
    (linked.toOption.map fun c => c.store.runtime.instances.map (·.funcaddrs)) =
      some #[#[0], #[1, 0, 2], #[2, 3]] := by
  decide +kernel

theorem linked_wellFormed :
    (linked.toOption.map (·.store.runtime.funcaddrsWellFormed)) = some true := by
  decide +kernel

/-- `I`'s import resolves to `E`'s function `e`, not to `E`'s host import. -/
theorem linked_import_resolves_to_e :
    (linked.toOption.map fun c => c.store.runtime.resolveFunc 2) = some (some (⟨1⟩, 2)) := by
  decide +kernel

/-! ### Hand-written copy of the linked runtime, used by the step proofs -/

def instE : ModuleInstance Unit :=
  { module := mE, host := envE
    resolvedImports := #[.host sevenHost, .wasm ⟨0⟩ 0]
    funcaddrs := #[1, 0, 2] }

def instI : ModuleInstance Unit :=
  { module := mI, host := {}
    resolvedImports := #[.wasm ⟨1⟩ 0]
    funcaddrs := #[2, 3] }

def linkedRuntime : RuntimeEnv Unit :=
  { instances := #[instX, instE, instI], entry := ⟨2⟩ }

private def ResolvedImport.target? : ResolvedImport α → Option (Nat × Nat)
  | .wasm callee k => some (callee.id, k)
  | .host _ => none

/-- The hand-written runtime agrees with `instantiate` on everything address
resolution reads. -/
theorem linkedRuntime_eq_linked :
    (linked.toOption.map fun c =>
        c.store.runtime.instances.map fun inst =>
          (inst.funcaddrs, inst.resolvedImports.map ResolvedImport.target?)) =
      some (linkedRuntime.instances.map fun inst =>
          (inst.funcaddrs, inst.resolvedImports.map ResolvedImport.target?)) := by
  decide +kernel

theorem linkedRuntime_wellFormed : linkedRuntime.funcaddrsWellFormed = true := by
  decide +kernel

/-- Run `code` in instance `I` with `values` already on the stack and the
shared table holding `table`. -/
def runIn (code : Program) (values : List Value := []) (table : TableInst := []) :
    Config Unit :=
  { expr := .running
      { locals := { values }, code, resultArity := 1, callerRemainder := [] }
    store := { runtime := linkedRuntime, wasm := { emptyStore with tables := [table] } } }

/-! ### `ref.func` + `call_ref` on the imported `e` reaches instance `E` -/

theorem refFunc_callRef_runs :
    (runSteps 10 (runIn [.refFunc 0, .callRef 0])).result.values? = some [.i32 42] := by
  decide +kernel

theorem callIndirect_alias_runs :
    (runSteps 10 (runIn [.const 0, .callIndirect 0 0] [] [.funcref (some 2)])).result.values? =
      some [.i32 42] := by
  decide +kernel

/-! ### Address `1` is `E`'s host import: every indirect form calls `seven` -/

theorem callRef_host_runs :
    (runSteps 4 (runIn [.callRef 0] [.funcref (some 1)])).result.values? = some [.i32 7] ∧
    (runSteps 4 (runIn [.callRef 0] [.funcref (some 1)])).result.finalConfig?.map
      (·.store.runtime.entry) = some ⟨2⟩ := by
  decide +kernel

theorem returnCallRef_host_runs :
    (runSteps 4 (runIn [.returnCallRef 0] [.funcref (some 1)])).result.values? =
      some [.i32 7] := by
  decide +kernel

theorem callIndirect_host_runs :
    (runSteps 4 (runIn [.const 0, .callIndirect 0 0] [] [.funcref (some 1)])).result.values? =
      some [.i32 7] := by
  decide +kernel

theorem returnCallIndirect_host_runs :
    (runSteps 4 (runIn [.const 0, .returnCallIndirect 0 0] [] [.funcref (some 1)])).result.values? =
      some [.i32 7] := by
  decide +kernel

/-- Type `1` is `[i32] → [i32]`, but `seven : [] → [i32]`: the cross-instance
host dispatch type-checks and traps. -/
theorem callIndirect_host_mismatch_traps :
    (runSteps 4 (runIn [.const 0, .callIndirect 1 0] [] [.funcref (some 1)])).result.trapReason? =
      some .indirectCallTypeMismatch := by
  decide +kernel

/-! ### Symbolic trace for the cross-instance host `call_indirect` -/

private theorem callIndirect_host_steps :
    Steps (runIn [.const 0, .callIndirect 0 0] [] [.funcref (some 1)])
      [.instruction (.const 0), .host 0, .administrative .finish]
      ⟨.done [.i32 7], { runtime := linkedRuntime, wasm := { emptyStore with tables := [[.funcref (some 1)]] } }⟩ := by
  wasm_steps [.const]
  apply Steps.cons
    (.callIndirectFuncAddrCrossInstanceHostReturn (owner := ⟨1⟩) (fnIdx := 0)
      (calleeInstance := instE) (imp := mE.imports[0]) (hostFunction := sevenHost)
      (signature := { results := [.i32] }) (expected := { results := [.i32] })
      (results := [.i32 7]) (wasm := { emptyStore with tables := [[.funcref (some 1)]] })
      rfl rfl rfl (by decide +kernel) (by decide) rfl rfl (by decide) rfl rfl rfl
      (by decide +kernel) rfl)
  wasm_steps [.finish]
  exact Steps.refl _

theorem callIndirect_host_terminates :
    TerminatesWith (runIn [.const 0, .callIndirect 0 0] [] [.funcref (some 1)])
      (fun values _ => values = [.i32 7]) :=
  runSteps_values_terminates
    (congrArg RunnerResult.values? (runSteps_eq_success_of_steps callIndirect_host_steps))

/-! ### Why the identity default is single-instance only -/

/-- Two instances left at the default identity `funcaddrs` both own address
`0`; `resolveFunc` sends it to the first, so instance 1's own `ref.func 0`
would dispatch into instance 0. `funcaddrsWellFormed` rejects the runtime. -/
def collidingRuntime : RuntimeEnv Unit :=
  { instances := #[instX, { module := mX, host := {} }], entry := ⟨1⟩ }

theorem colliding_resolves_to_first : collidingRuntime.resolveFunc 0 = some (⟨0⟩, 0) := by
  decide +kernel

theorem colliding_not_wellFormed : collidingRuntime.funcaddrsWellFormed = false := by
  decide +kernel

end CrossInstanceFuncaddrs
end Wasm
