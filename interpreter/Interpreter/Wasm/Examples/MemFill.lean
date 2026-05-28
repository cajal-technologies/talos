import Interpreter.Wasm.Wp.Tactic

/-! ## Example: memory.fill

    `memory.fill` pops `[dst, val, len]` (top = `len`) and writes
    `val.low8` into `mem[dst, dst+len)`. The instruction traps before
    any write when the destination range escapes the legal byte span. -/

namespace Wasm

/-- Fill the first 8 bytes with `0xAB`, then read them back as one i64.
    The expected payload is the byte `0xAB` repeated eight times. -/
def fillThenReadBody : Program := [
  .const 0,        -- dst
  .const 0xAB,     -- val (only the low byte is used)
  .const 8,        -- len
  .memoryFill,
  .const 0, .load64 0
]

/-- Trap case: dst (65 530) + len (100) overflows the only page. -/
def fillTrapBody : Program := [
  .const 65530, .const 0xCD, .const 100,
  .memoryFill
]

def fillModule : Module :=
  { funcs := [{ body := fillThenReadBody, results := [.i64] }, { body := fillTrapBody }]
    memory := some { pagesMin := 1 } }

private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

/-- Project the trap message (if any) out of a `Result`, so we can
    `native_decide` against it without needing `DecidableEq Store`. -/
private def runTrapMsg (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : Option String :=
  match run fuel m idx st args with
  | .Trap _ msg => some msg
  | _ => none

theorem fill_then_load_returns_repeated_byte :
    runValues 10 fillModule 0 fillModule.initialStore []
      = [.i64 0xABABABABABABABAB] := by
  native_decide

theorem fill_out_of_bounds_traps :
    runTrapMsg 10 fillModule 1 fillModule.initialStore []
      = some "out of bounds memory access" := by
  native_decide

end Wasm
