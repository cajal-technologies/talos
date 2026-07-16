import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import Interpreter.Wasm

/-! # Prop-level Weakest Precondition for Wasm

`wp_wasm_prop` — the fuel-abstracted Prop-level weakest precondition:
some fuel exists under which the program runs to completion (fallthrough
or return) in a state satisfying `Q`. This is the layer program proofs
compose in: see the `wp_wasm_prop_*` rules in `Adequacy.lean`, which also
defines the iProp-level `wp_wasm` fixpoint and the adequacy bridge from
it down to this predicate. -/

namespace Wasm.SepLogic

open Iris Wasm

def wp_wasm_prop (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : Prop :=
  ∃ fuel, match exec fuel m st locals prog env with
  | .Fallthrough st' _ => Q st' []
  | .Return st' vals => Q st' vals
  | _ => False

end Wasm.SepLogic
