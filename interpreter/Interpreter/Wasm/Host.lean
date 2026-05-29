import Interpreter.Wasm.Syntax

/-!
# Host environment

`HostEnv` is the executor-side counterpart to `Module.imports`. It supplies
the actual code behind each declared import: a function from
`(Store, args)` to either a `Return` (new store + result values) or a
`Trap` (new store carrying any side effects committed before the trap +
message). Imports occupy the low indices of the unified function index
space, so `HostEnv.funcs[i]` resolves `call i` for `i < imports.length`.

`HostEnv` lives alongside `Module`, not inside `Store`: it is immutable
runtime data, not Wasm-visible program state. Keeping it separate means
existing `Store` invariants don't need to mention the host.

For reasoning, programs are stated parametric over any `HostEnv`
satisfying a `HostSpec` (introduced in a later milestone) — the
contracts in a `HostSpec` constrain what the host is *allowed* to do,
without committing to a particular implementation.
-/

namespace Wasm

inductive HostResult where
  /-- The host call returned successfully with the given result values.
  The store carries every side effect the host committed. -/
  | Return : List Value → Store → HostResult
  /-- The host call trapped. The store carries every side effect
  committed *before* the trap was raised — matches the wasm spec's
  atomicity rule for `unreachable` and out-of-bounds memory. -/
  | Trap   : Store → String → HostResult

/-- A single host-resolved function. `params`/`results` describe the
declared signature so callers and validators can sanity-check it; the
interpreter currently trusts these on faith. `invoke` is the actual
host code, called with the popped arguments in wasm calling-convention
order (first declared param first, top-of-stack last). -/
structure HostFn where
  params  : List ValueType := []
  results : List ValueType := []
  invoke  : Store → List Value → HostResult

/-- A host environment: positional list of resolved host functions,
indexed identically to the declaring module's `imports` field. -/
structure HostEnv where
  funcs : List HostFn := []

@[inline] def HostEnv.empty : HostEnv := {}

instance : Inhabited HostEnv := ⟨{}⟩

/-! ## Contracts and specifications

`HostContract` is the proof-side counterpart to `HostFn`: instead of
naming a particular implementation, it constrains the relation between
the pre-store/args and the host's outcome (`Return` or `Trap`). Program
theorems are stated *parametric* over any `HostEnv` satisfying a chosen
`HostSpec` — so a verified program runs against any host whose
behaviour fits the contract, including hosts that don't yet exist.

This is the classical "abstract oracle" pattern (CompCert, seL4): the
executor and proof sides share the contract; only the executor side
fixes a concrete implementation. -/

/-- A host contract is a relation on `(pre-store, args, outcome)`. A
host function satisfies the contract iff every call it produces is
related to its inputs. Both `Return` and `Trap` outcomes are subject
to the relation, so contracts can constrain or forbid trapping. -/
abbrev HostContract := Store → List Value → HostResult → Prop

/-- A host specification: positional list of per-import contracts,
indexed identically to the declaring module's `imports` field.
The relation to a particular `Module` is established at `Satisfies`
time so the same `HostSpec` can be reused across modules with
matching import shapes. -/
structure HostSpec where
  contracts : List HostContract := []

/-- A `HostEnv` satisfies a `HostSpec` *for module `m`* when:
* every declared import index has both a resolver and a contract;
* every concrete invocation of the resolver respects the contract.

Program theorems quantify over such satisfying environments — the
proof only ever uses the relational facts, never the concrete
`HostFn.invoke`. -/
def HostEnv.Satisfies (env : HostEnv) (m : Module) (spec : HostSpec) : Prop :=
  ∀ i, i < m.imports.length →
    ∃ hf c, env.funcs[i]? = some hf ∧ spec.contracts[i]? = some c ∧
            ∀ st args, c st args (hf.invoke st args)

end Wasm
