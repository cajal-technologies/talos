import Interpreter.Wasm.Wp.Tactic

/-! ## Example: memory.size / memory.grow

    Three sanity checks:

    1. `memory.size` returns the initial page count.
    2. `memory.grow delta` returns the *previous* page count and bumps
       `memory.size` by `delta` when the request is in range.
    3. Asking for more pages than the cap allows leaves the memory
       untouched and pushes `-1` (`0xFFFFFFFF`). -/

namespace Wasm

/-- Push the current page count. -/
def sizeBody : Program := [.memorySize]

/-- Grow by 2 pages, drop the old-size return value, then push the new
    size. -/
def growThenSizeBody : Program := [
  .const 2, .memoryGrow,
  .drop,
  .memorySize
]

/-- Try to grow far beyond `memoryHardCap` (65536 pages). Wasm specifies
    that this leaves the memory alone and pushes `-1`. We then push the
    unchanged size, so the value stack ends as `[size, -1]` (top = size). -/
def growFailBody : Program := [
  .const 0xFFFFFF00, .memoryGrow,
  .memorySize
]

def growModule : Module :=
  { funcs :=
      [ { body := sizeBody,          results := [.i32] }
      , { body := growThenSizeBody,  results := [.i32] }
      -- growFailBody leaves `[size, -1]` on the stack (top = size), so the
      -- function returns two i32s under Wasm's standard convention.
      , { body := growFailBody,      results := [.i32, .i32] } ]
    memory := some { pagesMin := 1 } }

private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

theorem memorySize_reads_pagesMin :
    runValues 10 growModule 0 growModule.initialStore [] = [.i32 1] := by
  native_decide

theorem memoryGrow_bumps_size :
    runValues 10 growModule 1 growModule.initialStore [] = [.i32 3] := by
  native_decide

/-- Grow request exceeds the cap → `-1` (`0xFFFFFFFF`) is returned and the
    memory still reports its original size on top of the stack. -/
theorem memoryGrow_oversize_returns_neg_one :
    runValues 10 growModule 2 growModule.initialStore []
      = [.i32 1, .i32 0xFFFFFFFF] := by
  native_decide

end Wasm
