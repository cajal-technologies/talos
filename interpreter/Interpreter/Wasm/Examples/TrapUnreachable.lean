import Interpreter.Wasm.Wp.Tactic

/-! ## Example: TrapUnreachable

    Unconditional trap for `unreachable`: rustc lowers panics and
    "impossible" control-flow arms to this instruction. Complements
    `TrapDivZero`, which shows a *conditional* arithmetic trap. -/

namespace Wasm

def TrapUnreachable : Program := [.unreachable]

theorem trapUnreachableSpec (m : Module) (st : Store) :
    wp m TrapUnreachable
        (fun c => c = .Trap st "unreachable")
        st { params := [], locals := [], values := [] } := by
  unfold TrapUnreachable
  wp_run

end Wasm
