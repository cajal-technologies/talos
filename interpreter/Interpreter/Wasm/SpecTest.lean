import Interpreter.Wasm.SpecTest.Rng
import Interpreter.Wasm.SpecTest.Run
import Interpreter.Wasm.SpecTest.Verdict
import Interpreter.Wasm.SpecTest.Gen.Basic
import Interpreter.Wasm.SpecTest.Gen.Module
import Interpreter.Wasm.SpecTest.Gen.Word
import Interpreter.Wasm.SpecTest.Json
import Interpreter.Wasm.SpecTest.Main

/-!
# Execution-based specification testing

A specification is only worth proving if it is true. `SpecTest` checks a
problem's public contract on concrete inputs before any proof is attempted, by
running the compiled module through the authoritative small-step interpreter
exactly as the specification starts it, and evaluating the executable mirror of
its postcondition (`@[spec_test] post`) on what the run observably did.

* `Run` — a constant-stack step loop (`run`) proved to return exactly
  `SmallStep.runSteps`'s result, instrumented with a step count and the set of
  functions entered;
* `Verdict` — the shape of a specification (`total-stream`,
  `total-disjunctive-stream`, `partial-stream`, `value-level`) and the uniform
  verdict table over run outcomes;
* `Gen` — input families shared by every problem, per input type: edge values,
  exhaustive small domains, values and sizes derived from the module's own
  constants, and seeded size-biased random inputs with shrinking;
* `Main` — the `spec_test` command line a problem workspace instantiates with
  its module, start configuration, codec and `post`.
-/
