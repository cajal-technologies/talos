import Interpreter.Wasm.Host

/-!
# Terminal out-of-memory host

`talos.oom : () -> ()` is the distinguished terminal notification used by
Talos's tiny Wasm allocator.  The Wasm signature has no result because Wasm
function types do not express non-returning calls; its host implementation and
contract trap on every well-shaped invocation instead.

The boolean marker in `State` makes OOM a typed observable fact in addition to
the stable host-trap message.  Malformed calls trap without setting it, so they
cannot be mistaken for resource exhaustion.
-/

namespace Wasm.OOM

/-- Stable message carried by the structural host trap. -/
def trapMessage : String := "talos.oom"

/-- Mutable evidence that the distinguished terminal call was reached. -/
structure State where
  raised : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- Pure implementation of `talos.oom`. A valid call records the event and
traps; it never returns control to Wasm. -/
def oomResult (store : Store State) (args : List Value) : HostResult State :=
  match args with
  | [] => .Trap { store with host := { raised := true } } trapMessage
  | _ => .Trap store "talos.oom: expected no arguments"

/-- A well-shaped OOM notification is terminal and records typed evidence in
the trap's final store. -/
theorem oomResult_nil (store : Store State) :
    oomResult store [] =
      .Trap { store with host := { raised := true } } trapMessage :=
  rfl

/-- Concrete implementation of the terminal OOM import. -/
def oomHost : HostFn State :=
  { params := []
    results := []
    invoke := oomResult }

/-- The single import declaration emitted by the allocator. -/
def imports : List ImportDecl :=
  [{ «module» := "talos", name := "oom", params := [], results := [] }]

/-- Executable environment for the OOM host. -/
def env : HostEnv State := { funcs := [oomHost] }

/-- Exact relational contract for the terminal OOM call. -/
def oomContract : HostContract State :=
  fun store args result => result = oomResult store args

/-- Relational specification corresponding to `OOM.imports`. -/
def spec : HostSpec State := { contracts := [oomContract] }

/-- The concrete environment satisfies the OOM specification for a module
whose import list consists exactly of the terminal OOM function. -/
theorem env_satisfies (module : Module) (himports : module.imports = imports) :
    env.Satisfies module spec := by
  intro index hindex
  rw [himports] at hindex
  have hzero : index = 0 := by
    simpa [imports] using hindex
  subst index
  refine ⟨oomHost, oomContract, rfl, rfl, ?_⟩
  intro store args
  rfl

end Wasm.OOM
