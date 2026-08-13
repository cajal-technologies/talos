import Interpreter.Wasm.SmallStep

/-!
# Entering a module through its host

`HostEnv` says what a host *does*; this file says how a module is *started*
under one, and what it means for that run to finish.  Both definitions are
parametric in the host state `α`, exactly as `HostFn`, `HostEnv`, `HostSpec`
and `HostContract` already are, so a host introduced later reuses them
unchanged.

`RunsWith` is the shape a user-facing specification wants: an export name, the
host state the run begins in, and a predicate on the host state it must end
in.  Fuel, linear memory and the machine's administrative bookkeeping stay
inside the relation.

These definitions cannot live in `Interpreter/Wasm/Host.lean` beside `HostEnv`
itself: that file is imported by `Semantics`, which `SmallStep` is built on, so
naming `SmallStep.Config` there would close an import cycle.
-/

namespace Wasm

/-- Initialize `m` at its export named `op`, running under `env` from host
state `initial` over the module's own initial memory, globals and tables.
`none` when `m` exports no such name, or when the entry point that name
resolves to cannot be entered. -/
def startConfig? [Inhabited α] (env : HostEnv α) (m : Module) (op : String)
    (initial : α) : Option (SmallStep.Config α) := do
  let entry ← m.findExport op
  (SmallStep.initConfig
    { module := m, host := env }
    entry { (m.initialStore : Store α) with host := initial } []).toOption

/-- Export `op` of `m`, started under `env` in host state `initial`, terminates
having returned no values and left a host state satisfying `post`. -/
def RunsWith [Inhabited α] (env : HostEnv α) (m : Module) (op : String)
    (initial : α) (post : α → Prop) : Prop :=
  ∃ config,
    startConfig? env m op initial = some config ∧
    SmallStep.TerminatesWith config (fun values final =>
      values = [] ∧ post final.wasm.host)

end Wasm
