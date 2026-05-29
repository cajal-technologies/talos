import Interpreter.Wasm.Wp.Tactic

/-! ## Example: EarlyBrInvalid

    A top-level `.br k` with `k ≥ 1` targets a label that does not exist
    on the function's static label stack. Wasm validation would reject
    this program; the unvalidated interpreter surfaces it as `.Invalid`
    with the dedicated "scope out of function" message. -/

namespace Wasm

def EarlyBrInvalid : Program := [.localGet 0, .br 1]

def earlyBrInvalidModule : Module := {
  funcs := [{ params := [.i32], results := [.i32], body := EarlyBrInvalid }]
}

/-- Project the invalid message (if any) out of a `Result Unit`, so we can
    `native_decide` against it without needing `DecidableEq Store Unit`. -/
private def runInvalidMsg (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store Unit) (args : List Value) : Option String :=
  match run fuel m idx st args with
  | .Invalid msg => some msg
  | _            => none

theorem early_br_out_of_scope_is_invalid :
    runInvalidMsg 10 earlyBrInvalidModule 0
        earlyBrInvalidModule.initialStore [.i32 42]
      = some "Unexpected break targeting scope out of function" := by
  native_decide

end Wasm
