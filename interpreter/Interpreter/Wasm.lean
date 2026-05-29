import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation
import Interpreter.Wasm.Semantics
import Interpreter.Wasm.Semantics.Lemmas
import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Wp.Atomic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Spec.Termination
import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Examples.Basic

/-! # Wasm

A minimal Wasm core paired with a weakest-precondition reasoning framework.
This umbrella module re-exports the public surface; the implementation is
split into:

* `Wasm.Syntax`            — instructions, programs, functions, modules
* `Wasm.Locals`            — per-frame locals/value-stack state + helpers
* `Wasm.Continuation`      — `Continuation` / `Result` outcome types
* `Wasm.Semantics`         — `execOne` / `exec` / `run` mutual interpreter
* `Wasm.Semantics.Lemmas`  — bridge lemmas between `exec` and `wp`
                                 (fuel monotonicity, atomic unfoldings, …)
* `Wasm.Wp.*`              — `wp` framework: definitions, atomic
                                 equations, block / loop / call rules, and
                                 the `wp_run` / `wp_done` tactics
* `Wasm.Spec.Termination`  — fuel-free `TerminatesWith` /
                                 `PartiallyMeets` predicates (user-facing
                                 spec API)
* `Wasm.Examples.Basic`    — umbrella import for the bundled worked
                                 examples
-/
