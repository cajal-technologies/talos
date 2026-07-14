import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import Interpreter.Wasm

/-! # Weakest Precondition for Wasm

Prop-level WP for termination. Per-instruction iProp rules for
ownership transfer. General iProp WP fixpoint deferred until
the instruction rules are validated on swap_elements.
-/

namespace Wasm.SepLogic

open Iris Wasm

variable [inst : WasmHeapGS]

def wp_wasm_prop (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : Prop :=
  ∃ fuel, match exec fuel m st locals prog env with
  | .Fallthrough st' _ => Q st' []
  | .Return st' vals => Q st' vals
  | _ => False

/-! ## Per-instruction ownership rules in iProp

Each rule describes how one instruction transforms ownership.
These compose sequentially for straight-line code (swap).
For loops, bi_least_fixpoint wraps the composition. -/

-- load64: need ownership to read, ownership preserved
def wp_load64 (addr : UInt32) (v : UInt64)
    (Q : IProp WasmHeapGF) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 addr v) ∗ (pointsTo_u64 addr v -∗ Q)

-- store64: consume old ownership, produce new
def wp_store64 (addr : UInt32) (old_v new_v : UInt64)
    (Q : IProp WasmHeapGF) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 addr old_v) ∗ (pointsTo_u64 addr new_v -∗ Q)


end Wasm.SepLogic
