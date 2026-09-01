import Interpreter.Wasm.Wp.Atomic
import Interpreter.Wasm.Wp.Block

/-! ### Tactics.

    `wp_run` symbolically executes straight-line code by reducing the atomic
    `wp_*_cons` equations. It stops at control-flow boundaries (`block`,
    `loop`, `iff`, `call`), where the user supplies invariants / specs
    explicitly. -/

namespace Wasm

/-- Symbolically execute straight-line code: reduce the atomic `wp_*_cons`
equations together with the frame helpers they expose, stopping at control-flow
boundaries (`block`, `loop`, `iff`, `call`).

`wp_run [foo, bar]` appends `foo, bar` to that fixed set, so a proof needing one
extra rewrite (a local hypothesis, a numeric simproc, a memory lemma) can add it
rather than fork the whole list. -/
syntax (name := wpRun) "wp_run" (Lean.Parser.Tactic.simpArgs)? : tactic

macro_rules
  | `(tactic| wp_run $[[$args,*]]?) => do
    let extra := args.map (·.getElems) |>.getD #[]
    `(tactic|
      simp only [wp_simp,
        -- Helpers
        Locals.get, Locals.set?,
        Function.toLocals, Function.numParams,
        List.take, List.drop, List.replicate, List.length, List.map,
        ValueType.zero,
        $extra,*])

macro "wp_done" : tactic => `(tactic| (wp_run; first | rfl | grind))

end Wasm
