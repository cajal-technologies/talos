import Interpreter.Wasm.Wp.Atomic
import Interpreter.Wasm.Wp.Block

/-! ### Tactics.

    `wp_run` symbolically executes straight-line code by reducing the atomic
    `wp_*_cons` equations. It stops at control-flow boundaries (`block`,
    `loop`, `iff`, `call`), where the user supplies invariants / specs
    explicitly. -/

namespace Wasm

macro "wp_run" : tactic => `(tactic|
  simp only [wp_simp,
    -- Helpers
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD])

macro "wp_done" : tactic => `(tactic| (wp_run; first | rfl | grind))

/-- Peel low-information structural boundaries, then simplify straight-line
code. This deliberately does not cross loops or calls: those still require an
explicit invariant/specification boundary. -/
macro "wp_peel" : tactic => `(tactic|
  ((repeat (first
    | apply wp_block_cons
    | refine wp_iff_cons rfl ?_));
   wp_run;
   simp))

end Wasm
