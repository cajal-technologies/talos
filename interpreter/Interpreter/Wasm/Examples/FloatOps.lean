import Interpreter.Wasm.Semantics

/-! ## Example: floating-point operations

End-to-end checks that the interpreter executes `f32`/`f64` instructions
faithfully: arithmetic, comparison, square root, min, the integer↔float
conversions, a bitwise `reinterpret`, and a `f64` memory round-trip. Each
function builds its operands from constants, so the results are concrete and
checkable by `native_decide` (which runs the native float operations the
semantics delegate to).

Expected values are written as `Float`/`Float32` literals decoded to bits via
`toBits`, so each theorem reads as the IEEE arithmetic it stands for. -/

namespace Wasm

/-- `(2.0 + 3.0) * 4.0` in `f64` ⇒ `20.0`. -/
def f64Arith : Program :=
  [ .f64Const (2.0 : Float).toBits, .f64Const (3.0 : Float).toBits, .f64Add,
    .f64Const (4.0 : Float).toBits, .f64Mul ]

/-- `1.5 * 2.0` in `f32` ⇒ `3.0`. -/
def f32Arith : Program :=
  [ .f32Const (1.5 : Float32).toBits, .f32Const (2.0 : Float32).toBits, .f32Mul ]

/-- `2.0 < 3.0` ⇒ `i32` `1`. -/
def f64Compare : Program :=
  [ .f64Const (2.0 : Float).toBits, .f64Const (3.0 : Float).toBits, .f64Lt ]

/-- `sqrt 9.0` ⇒ `3.0`. -/
def f64Root : Program :=
  [ .f64Const (9.0 : Float).toBits, .f64Sqrt ]

/-- `min 3.0 2.0` ⇒ `2.0`. -/
def f64Minimum : Program :=
  [ .f64Const (3.0 : Float).toBits, .f64Const (2.0 : Float).toBits, .f64Min ]

/-- `i32 7` → `f64` → back to `i32` ⇒ `7` (round-trip through the conversions). -/
def convRoundtrip : Program :=
  [ .const 7, .f64ConvertI32S, .i32TruncF64S ]

/-- `0x3f80_0000` reinterpreted as `f32` is `1.0`. -/
def reinterpret : Program :=
  [ .const 0x3f800000, .f32ReinterpretI32 ]

/-- Store `3.5 : f64` at address 0 and load it back. -/
def memRoundtrip : Program :=
  [ .const 0, .f64Const (3.5 : Float).toBits, .f64Store 0,
    .const 0, .f64Load 0 ]

def floatModule : Module :=
  { funcs :=
      [ { body := f64Arith,     results := [.f64] }
      , { body := f32Arith,     results := [.f32] }
      , { body := f64Compare,   results := [.i32] }
      , { body := f64Root,      results := [.f64] }
      , { body := f64Minimum,   results := [.f64] }
      , { body := convRoundtrip, results := [.i32] }
      , { body := reinterpret,  results := [.f32] }
      , { body := memRoundtrip, results := [.f64] } ]
    memory := some { pagesMin := 1 } }

/-- Project the value stack out of a `Result Unit`; `Store Unit` carries a
    function-valued `Mem` and so has no decidable equality. -/
private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store Unit) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

theorem f64_arith :
    runValues 10 floatModule 0 floatModule.initialStore [] = [.f64 (20.0 : Float).toBits] := by
  native_decide

theorem f32_arith :
    runValues 10 floatModule 1 floatModule.initialStore [] = [.f32 (3.0 : Float32).toBits] := by
  native_decide

theorem f64_compare :
    runValues 10 floatModule 2 floatModule.initialStore [] = [.i32 1] := by
  native_decide

theorem f64_sqrt :
    runValues 10 floatModule 3 floatModule.initialStore [] = [.f64 (3.0 : Float).toBits] := by
  native_decide

theorem f64_min :
    runValues 10 floatModule 4 floatModule.initialStore [] = [.f64 (2.0 : Float).toBits] := by
  native_decide

theorem conv_roundtrip :
    runValues 10 floatModule 5 floatModule.initialStore [] = [.i32 7] := by
  native_decide

theorem reinterpret_one :
    runValues 10 floatModule 6 floatModule.initialStore [] = [.f32 (1.0 : Float32).toBits] := by
  native_decide

theorem mem_roundtrip :
    runValues 10 floatModule 7 floatModule.initialStore [] = [.f64 (3.5 : Float).toBits] := by
  native_decide

end Wasm
