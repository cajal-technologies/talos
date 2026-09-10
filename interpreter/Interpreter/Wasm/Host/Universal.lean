import Interpreter.Wasm.Host.Registry
import Interpreter.Wasm.Host.StdIO
import Interpreter.Wasm.Host.Random
import Interpreter.Wasm.Host.OOM

/-!
# The universal host

One host environment offering every host function the interpreter knows about,
so a specification never has to choose a host.

A module is served by `Universal.envFor «module»` whatever it imports: all of
`StdIO`, all of `Random`, some of each, in any order, or nothing at all. The
functions a module does not import are still present in the state and simply
unreachable — no `call` resolves to them.

`Universal.State` is a plain record with one field per host, each defaulted.
Adding a host means adding a field and one `component` term, both here; the host
itself is written in the ordinary way and needs no knowledge that this file
exists. Because every field has a default, existing construction sites keep
compiling, and because the record is what specifications name, existing theorems
keep holding — a bigger state is still the same type constructor.

`envFor_satisfies` needs no hypothesis about the module's imports, which is the
concrete sense in which a proof stops choosing a host: the environment and the
spec are both built by walking `m.imports`, so they agree by construction.
-/

namespace Wasm.Universal

/-- The composite host state: one field per host, each defaulted so that adding
a host later leaves existing construction sites untouched. -/
structure State where
  stdio : StdIO.State := default
  random : Random.State := default
  oom : OOM.State := default
deriving Inhabited

/-- Every host function the interpreter knows, over the composite state.

Each host contributes one `component` term: its own `imports` and `env.funcs`,
and the field it occupies. This is the only file in the repo that knows hosts
get composed at all — a host is written exactly as `Host/StdIO.lean` and
`Host/Random.lean` are, and mentions none of this. -/
def registry : HostRegistry State :=
  .component StdIO.imports StdIO.env.funcs
      State.stdio (fun whole part => { whole with stdio := part })
  ++ .component Random.imports Random.env.funcs
      State.random (fun whole part => { whole with random := part })
  ++ .component OOM.imports OOM.env.funcs
      State.oom (fun whole part => { whole with oom := part })

/-- The environment `m` sees: its own imports, resolved by name, in its own
order. -/
def envFor (m : Module) : HostEnv State := registry.envFor m

/-- The specification matching `envFor m`, entry for entry. -/
def specFor (m : Module) : HostSpec State := registry.specFor m

/-- The universal environment satisfies the universal specification for **every**
module, with no hypothesis on what that module imports.

Compare `StdIO.env_satisfies`, which holds only when `m.imports = StdIO.imports`
exactly. -/
theorem envFor_satisfies (m : Module) : (envFor m).Satisfies m (specFor m) :=
  registry.envFor_satisfies m

/-- No two entries claim the same `(module, name)`. Resolution takes the first
match, so a duplicate key would silently shadow a host function; this is the
guard against that, and a new host must keep it true. -/
theorem registry_keys_nodup :
    (registry.map fun entry => (entry.decl.«module», entry.decl.name)).Nodup := by decide +kernel

/-- Whether every import `m` declares is one the universal host implements.
A spec carries this as a smoke test: an unimplemented import still runs, but
traps, and this check says so up front rather than letting the trap masquerade
as program behaviour. -/
def covers (m : Module) : Bool := registry.covers m

/-! ## Starting a run -/

/-- Start with `input` readable on `stdio` and no entropy consumed. -/
def State.ofInput (input : List UInt8) : State :=
  { stdio := StdIO.State.ofInput input }

/-- Start with `input` readable on `stdio` and `oracle` supplying `random`. -/
def State.ofInputAndOracle (input : List UInt8) (oracle : Random.Oracle) :
    State :=
  { stdio := StdIO.State.ofInput input
    random := Random.State.ofOracle oracle }

/-- Export `op` of `m`, started under the universal host in state `initial`,
terminates having returned no values and left a host state satisfying `post`.

This is the host-agnostic entry point: `m` may import anything. -/
def Runs (m : Module) (op : String) (initial : State) (post : State → Prop) :
    Prop :=
  RunsWith (envFor m) m op initial post

/-- Export `op` of `m`, run on `input`, terminates having written exactly
`output` — the `StdIO` reading of `Runs`, available to any module regardless of
what else it imports. -/
def RunsBytes (m : Module) (op : String) (input output : List UInt8) : Prop :=
  Runs m op (State.ofInput input) fun final => final.stdio.output = output

end Wasm.Universal
