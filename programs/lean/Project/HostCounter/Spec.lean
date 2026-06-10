import Project.HostCounter.Program
import Project.HostCounter.Host

/-!
# Specification for `host_counter`

The exported `step()` calls `host_get`; if the returned counter is
strictly less than `10`, it calls `host_inc` to bump it. We claim
that this preserves the invariant `counter ≤ 10`: if it held before
the call, it holds after — regardless of which `HostEnv`
implementation is supplied, as long as it satisfies `counterSpec`.

The spec is stated as `PartiallyMeets`: every successful run lands in
a state where the invariant holds. Termination is not part of the
claim, though for this branch-only program it would hold too.
-/

namespace Project.HostCounter.Spec

open Wasm
open Project.HostCounter.Host

/-- The program-level invariant `step` preserves: the host counter is
at most `10`. This is a property of the *program* (its guarded
increment never lets the counter exceed `10`), not of the host —
the host on its own permits arbitrary counter values. -/
def CounterInv (st : Store CounterState) : Prop :=
  st.host.counter ≤ 10

/-- The unified function index of the exported `step` wrapper in the
decoded module. Imports occupy the low end of the index space
(`host_get = 0`, `host_inc = 1`), so the in-module functions start at
`2`: `func0` (the guarded-increment body) is unified index `2`, and
the exported `step` wrapper `func1` (which just `call 2`s into it) is
unified index `3` — matching `exports` in the generated `Program.lean`. -/
def stepIdx : Nat := 3

/-- `step` preserves the counter-invariant.

Stated as partial correctness over every `HostEnv` satisfying
`counterSpec`. The proof will reason only via the contracts, never
the concrete `incHost` / `getHost`. -/
@[spec_of "rust-exported" "host_counter::step"]
def StepPreservesInv : Prop :=
  ∀ (env : HostEnv CounterState) (initial : Store CounterState),
    env.Satisfies «module» counterSpec →
    CounterInv initial →
    PartiallyMeets env «module» stepIdx initial []
      (fun st _ => CounterInv st)

end Project.HostCounter.Spec
