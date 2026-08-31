import Interpreter.Wasm.Syntax

/-!
# Local variables and call-frame state

Defines `Locals` — the per-invocation frame holding parameter slots, local
variable slots, and the operand stack — together with indexed get/set
operations used by the interpreter.
-/

namespace Wasm

/-- Per-call frame: parameter slots, non-param local slots, and the operand
stack (head = top). All three are `Value` lists; the simple shape (no `Store`,
no labels) is deliberate — control flow is encoded by Lean's call stack via
the structural recursion of `exec`. -/
structure Locals where
  params : List Value := []
  locals : List Value := []
  values : List Value := []
deriving Repr, Inhabited

/-- Initialise a callee frame: copy the args into `params`, zero-init `locals`
per their declared type, and start with an empty value stack. -/
def Function.toLocals (f : Function) (args : List Value) : Locals :=
  { params := args
    locals := f.locals.map ValueType.zero
    values := [] }

@[simp]
def Locals.get (s : Locals) (i : Nat) : Option Value :=
  if i < s.params.length then s.params[i]?
  else if i < s.params.length + s.locals.length then s.locals[i - s.params.length]?
  else none

@[simp]
def Locals.set? (s : Locals) (i : Nat) (v : Value) : Option Locals :=
  if i < s.params.length then some { s with params := s.params.set i v }
  else if i < s.params.length + s.locals.length then some { s with locals := s.locals.set (i - s.params.length) v }
  else none

end Wasm
