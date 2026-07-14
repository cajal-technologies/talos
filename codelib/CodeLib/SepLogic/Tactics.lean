import Lean
import Iris.ProofMode
open Lean Elab Tactic

-- wpure rule
-- apply a pure wasm instruction rule and discharge hstep with σ' = σ.
-- rule must leave only hstep unresolved after apply; pass any side conditions
-- in the rule term:
--   wpure wp_wasm_const               (v inferred from goal)
--   wpure (wp_wasm_localGet hget)     (hget : locals.get i = some v)
--   wpure (wp_wasm_add hstack)        (hstack : locals.values = ...)
-- the wp_wasm continuation goal is left open after the macro runs.
elab "wpure" rule:term : tactic => do
  evalTactic (← `(tactic| apply $rule))
  evalTactic (← `(tactic| intro σ))
  evalTactic (← `(tactic| iintro Hσ))
  evalTactic (← `(tactic| imodintro))
  evalTactic (← `(tactic| iexists σ))
  evalTactic (← `(tactic| isplitl [Hσ]))
  evalTactic (← `(tactic| next => iexact Hσ))

-- wmem: future pattern for memory load/store instructions.
-- load/store rules change σ (σ' ≠ σ), so the heap-unchanged proof above
-- does not apply.  ownership transfer via pointsTo_u64 must happen before
-- the hstep obligation can be closed.  use wp_load64/wp_store64 manually
-- until a wmem tactic is added here.
