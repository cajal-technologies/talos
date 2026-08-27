import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Float
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation
import Interpreter.Wasm.Semantics
import Interpreter.Wasm.Semantics.Lemmas
import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Host.Registry
import Interpreter.Wasm.Host.StdIO
import Interpreter.Wasm.Host.OOM
import Interpreter.Wasm.Host.Random.Probability
import Interpreter.Wasm.Host.Universal
import Interpreter.Wasm.MeasureTermination
import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Wp.Atomic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Spec.Termination

/-! # Wasm

A minimal Wasm core paired with a weakest-precondition reasoning framework.
This umbrella module re-exports the public core surface; the implementation is
split into:

* `Wasm.Syntax`            — instructions, programs, functions, modules
* `Wasm.Float`             — `f32`/`f64` operations over IEEE-754 bit patterns
* `Wasm.Locals`            — per-frame locals/value-stack state + helpers
* `Wasm.Continuation`      — `Continuation` / `Result` outcome types
* `Wasm.Semantics`         — `execOne` / `exec` / `run` mutual interpreter
* `Wasm.Semantics.Lemmas`  — bridge lemmas between `exec` and `wp`
                                 (fuel monotonicity, atomic unfoldings, …)
* `Wasm.Wp.*`              — `wp` framework: definitions, atomic
                                 equations, block / loop / call rules, and
                                 the `wp_run` / `wp_done` tactics
* `Wasm.Host.Registry`     — name-keyed host registries: resolve a
                                 module's own imports, in its own order,
                                 into the positional `HostEnv` the
                                 interpreter expects
* `Wasm.Host.OOM`          — terminal `talos.oom` notification used only by
                                 the tiny Rust allocator
* `Wasm.Host.Universal`    — one host offering every host function; the
                                 default for specifications, so a proof
                                 never has to choose a host
* `Wasm.Spec.Termination`  — fuel-free `TerminatesWith` /
                                 `PartiallyMeets` predicates (user-facing
                                 spec API)

Worked examples live under `Interpreter.Wasm.Examples.*` and are bundled by
`Interpreter.Wasm.Examples.Basic`; decoder internals live under
`Interpreter.Wasm.Decoder.*`. They are intentionally not re-exported here so
downstream proof packages can import the core API without depending on examples
or verifier plumbing.
-/
