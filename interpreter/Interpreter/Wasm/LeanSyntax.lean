import Interpreter.Wasm.Syntax
import Lean.Elab.Term

/-!
# Compact Lean syntax for generated Wasm modules

These elaborators reduce committed source size without changing the elaborated
Wasm AST. In particular, `hexBytes%` expands to an ordinary literal
`List UInt8`; it does not leave a decoder call for proofs to unfold later.
-/

namespace Wasm

open Lean Elab Term

syntax (name := hexBytes) "hexBytes% " str : term

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decodeHex : List Char → Except String (List Nat)
  | [] => .ok []
  | hi :: lo :: rest => do
      let some h := hexDigit? hi | throw s!"invalid hex digit `{hi}`"
      let some l := hexDigit? lo | throw s!"invalid hex digit `{lo}`"
      return (16 * h + l) :: (← decodeHex rest)
  | [_] => .error "hex byte literal must contain an even number of digits"

@[term_elab hexBytes] def elabHexBytes : TermElab := fun stx expectedType? => do
  let `(hexBytes% $value:str) := stx | throwUnsupportedSyntax
  let bytes ← match decodeHex value.getString.toList with
    | .ok bytes => pure bytes
    | .error message => throwError message
  let source := "[" ++ String.intercalate ", " (bytes.map toString) ++ "]"
  let parsed ← match Parser.runParserCategory (← getEnv) `term source with
    | .ok parsed => pure parsed
    | .error message => throwError message
  elabTerm parsed expectedType?

end Wasm
