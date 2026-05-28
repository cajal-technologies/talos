import Interpreter.Wasm.Wp.Tactic

/-! ## Example: memory.copy

    `memory.copy` pops `[dst, src, len]` (top = `len`) and copies `len`
    bytes from `mem[src, src+len)` to `mem[dst, dst+len)` with
    `memmove` semantics (overlapping ranges resolve against the
    pre-copy bytes). The instruction traps before any write when
    either range escapes the legal byte span. -/

namespace Wasm

private def initBytes : List UInt8 :=
  [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]

/-- Non-overlapping copy: move 4 bytes from address 0 to address 8,
    then read the destination as one little-endian u32. Expected
    payload: `0x44332211`. -/
def copyDisjointBody : Program := [
  .const 8,        -- dst
  .const 0,        -- src
  .const 4,        -- len
  .memoryCopy,
  .const 8, .load32 0
]

/-- Overlapping copy: shift 4 bytes from address 0 to address 2.
    After the copy mem[0..8] = [0x11, 0x22, 0x11, 0x22, 0x33, 0x44, 0x77, 0x88]
    so reading 8 bytes LE at 0 gives `0x8877443322112211`. -/
def copyOverlapBody : Program := [
  .const 2,        -- dst
  .const 0,        -- src
  .const 4,        -- len
  .memoryCopy,
  .const 0, .load64 0
]

/-- Trap case: the destination range escapes the only page. -/
def copyTrapBody : Program := [
  .const 65530, .const 0, .const 100,
  .memoryCopy
]

def copyModule : Module :=
  { funcs :=
      [ { body := copyDisjointBody, results := [.i32] }
      , { body := copyOverlapBody,  results := [.i64] }
      , { body := copyTrapBody } ]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := initBytes }] } }

private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

private def runTrapMsg (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : Option String :=
  match run fuel m idx st args with
  | .Trap _ msg => some msg
  | _ => none

theorem copy_disjoint_moves_bytes :
    runValues 10 copyModule 0 copyModule.initialStore [] = [.i32 0x44332211] := by
  native_decide

theorem copy_overlap_uses_pre_copy_bytes :
    runValues 10 copyModule 1 copyModule.initialStore []
      = [.i64 0x8877443322112211] := by
  native_decide

theorem copy_out_of_bounds_traps :
    runTrapMsg 10 copyModule 2 copyModule.initialStore []
      = some "out of bounds memory access" := by
  native_decide

end Wasm
