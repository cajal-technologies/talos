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
/-- A pending tail call (`return_call` / `return_call_indirect`): the
current frame is being replaced by an invocation of function `id` with
the carried operand stack. `run` resolves it by re-dispatching; it never
escapes past `run`. -/
| ReturnCall  : Nat → Store α → List Value → Continuation α
/-- An exception in flight (`throw` tag with the popped arguments, in
stack order). It unwinds like a trap until a `try_table` with a matching
catch clause intercepts it; the carried `Locals` are the frame state at
the throw point (locals mutations made before the throw stay visible to
an in-frame catch, exactly as for `Break`). -/
| Throwing    : Nat → List Value → Store α → Locals → Continuation α
deriving Repr

inductive Result (α : Type) where
  | Success   : List Value → Store α → Result α
  /-- See `Continuation.Trap`: the store reflects every side effect
  committed before the trap was raised. -/
  | Trap      : Store α → String → Result α
  | Invalid   : String → Result α
  | OutOfFuel : Result α
  /-- An exception escaped the invocation uncaught: tag index and the
  thrown arguments (stack order). Callers re-raise it in their own frame
  (`execOne`'s call arms) or report it (`assert_exception`). -/
  | Thrown    : Nat → List Value → Store α → Result α
deriving Repr

end Wasm
