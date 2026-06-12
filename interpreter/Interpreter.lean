import Interpreter.Wasm
import Interpreter.Wasm.Examples.Basic

/-!
# Interpreter — public surface

The Wasm formalisation lives in `Interpreter.Wasm`: typed AST,
fuel-bounded interpreter, `wp` framework, `TerminatesWith` predicate, and
WAT decoder. Downstream code should `import` this module (or transitively
via `CodeLib`).
-/
