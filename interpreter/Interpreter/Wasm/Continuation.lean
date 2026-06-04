import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Locals

/-!
# Continuation and Result types

`Continuation` is the outcome of a single instruction or block evaluation:
the interpreter returns one of these at every step and callers pattern-match
on it to decide how to continue. `Result` is the coarser outcome reported to
the caller of `run` — it collapses the in-flight control-flow variants
(`Fallthrough`, `Break`, `Return`) into a single `Success`.
-/

namespace Wasm

inductive Continuation (α : Type) where
| Fallthrough : Store α → Locals → Continuation α
| Break       : Nat → Store α → Locals → Continuation α
| Return      : Store α → List Value → Continuation α
/-- A trap aborts the current invocation. Per the wasm spec, side
effects already committed before the trap (memory writes, global
updates) are visible in the store carried here — only the in-flight
operand/locals state is lost. -/
| Trap        : Store α → String → Continuation α
| Invalid     : String → Continuation α
| OutOfFuel   : Continuation α
deriving Repr

inductive Result (α : Type) where
  | Success   : List Value → Store α → Result α
  /-- See `Continuation.Trap`: the store reflects every side effect
  committed before the trap was raised. -/
  | Trap      : Store α → String → Result α
  | Invalid   : String → Result α
  | OutOfFuel : Result α
deriving Repr

end Wasm
