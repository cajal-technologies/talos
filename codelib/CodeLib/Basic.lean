import Interpreter.Wasm

/-!
# CodeLib.Basic — public re-exports

Downstream code (especially the auto-generated `Program.lean` files emitted
by `lake exe verifier check`) should `import CodeLib`, never the interpreter
directly. This module forwards the Wasm public surface (typed AST,
fuel-bounded interpreter, `wp` framework, `TerminatesWith` predicate).

The WAT decoder is intentionally **not** re-exported; it exists only as
internal scaffolding for the verifier's `.wasm → WAT → Lean source` pipeline
(see `verifier/Verifier/Emit.lean`).

Bundled worked examples are also kept out of this downstream surface; import
`Interpreter.Wasm.Examples.Basic` explicitly when developing the interpreter's
example corpus.
-/
