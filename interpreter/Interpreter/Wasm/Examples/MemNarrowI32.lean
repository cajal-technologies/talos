import Interpreter.Wasm.Wp.Tactic

/-! ## Example: i32 narrow loads/stores

    Sanity checks for the i32 narrow memory accesses:
    `load8_u`, `load8_s`, `load16_u`, `load16_s`, `store8`, `store16`.

    The module has a one-page memory whose first eight bytes are
    `[0x42, 0xFF, 0xCD, 0xAB, 0xCD, 0xFF, 0, 0]`. Each function reads
    one of those bytes/half-words with a specific width and signedness,
    so the four loads exercise zero- vs. sign-extension at both widths.
    The store functions write a known constant and read it back through
    the matching unsigned load. -/

namespace Wasm

private def initBytes : List UInt8 :=
  [0x42, 0xFF, 0xCD, 0xAB, 0xCD, 0xFF, 0, 0]

def load8UBody : Program := [.const 0, .load8U 0]
def load8SBody : Program := [.const 1, .load8S 0]
def load16UBody : Program := [.const 2, .load16U 0]
def load16SBody : Program := [.const 4, .load16S 0]

/-- Write byte 0xAB at address 0, then read it back as a zero-extended u8. -/
def store8RoundtripBody : Program := [
  .const 0, .const 0xAB, .store8 0,
  .const 0, .load8U 0
]

/-- Write half-word 0xABCD at address 4, then read it back as a zero-extended u16. -/
def store16RoundtripBody : Program := [
  .const 4, .const 0xABCD, .store16 0,
  .const 4, .load16U 0
]

def narrowI32Module : Module :=
  { funcs :=
      [ { body := load8UBody,  results := [.i32] }
      , { body := load8SBody,  results := [.i32] }
      , { body := load16UBody, results := [.i32] }
      , { body := load16SBody, results := [.i32] }
      , { body := store8RoundtripBody,  results := [.i32] }
      , { body := store16RoundtripBody, results := [.i32] } ]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := initBytes }] } }

/-- Project the value stack out of a `Result`. `Store` carries a function-
    valued `Mem`, so it has no decidable equality; comparing the values
    alone keeps the `native_decide` checks below well-typed. -/
private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

theorem load8U_returns_byte :
    runValues 10 narrowI32Module 0 narrowI32Module.initialStore [] = [.i32 0x42] := by
  native_decide

theorem load8S_sign_extends :
    runValues 10 narrowI32Module 1 narrowI32Module.initialStore [] = [.i32 0xFFFFFFFF] := by
  native_decide

theorem load16U_returns_halfword :
    runValues 10 narrowI32Module 2 narrowI32Module.initialStore [] = [.i32 0xABCD] := by
  native_decide

theorem load16S_sign_extends :
    runValues 10 narrowI32Module 3 narrowI32Module.initialStore [] = [.i32 0xFFFFFFCD] := by
  native_decide

theorem store8_roundtrip :
    runValues 10 narrowI32Module 4 narrowI32Module.initialStore [] = [.i32 0xAB] := by
  native_decide

theorem store16_roundtrip :
    runValues 10 narrowI32Module 5 narrowI32Module.initialStore [] = [.i32 0xABCD] := by
  native_decide

end Wasm
