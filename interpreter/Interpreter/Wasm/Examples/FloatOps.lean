import Interpreter.Wasm.SmallStep

/-! Floating-point instruction checks against exact IEEE bit patterns.
The reference interpreter uses pure integer arithmetic, and every check is
verified by Lean's kernel. -/

set_option maxRecDepth 100000

namespace Wasm
open SmallStep

/-- `(2.0 + 3.0) * 4.0` in `f64` ⇒ `20.0`. -/
def f64Arith : Program :=
  [ .f64Const 0x4000000000000000, .f64Const 0x4008000000000000, .f64Add,
    .f64Const 0x4010000000000000, .f64Mul ]

/-- `1.5 * 2.0` in `f32` ⇒ `3.0`. -/
def f32Arith : Program :=
  [ .f32Const 0x3FC00000, .f32Const 0x40000000, .f32Mul ]

/-- `2.0 < 3.0` ⇒ `i32` `1`. -/
def f64Compare : Program :=
  [ .f64Const 0x4000000000000000, .f64Const 0x4008000000000000, .f64Lt ]

/-- `sqrt 9.0` ⇒ `3.0`. -/
def f64Root : Program :=
  [ .f64Const 0x4022000000000000, .f64Sqrt ]

/-- `min 3.0 2.0` ⇒ `2.0`. -/
def f64Minimum : Program :=
  [ .f64Const 0x4008000000000000, .f64Const 0x4000000000000000, .f64Min ]

/-- `i32 7` → `f64` → back to `i32` ⇒ `7` (round-trip through the conversions). -/
def convRoundtrip : Program :=
  [ .const 7, .f64ConvertI32S, .i32TruncF64S ]

/-- `0x3f80_0000` reinterpreted as `f32` is `1.0`. -/
def reinterpret : Program :=
  [ .const 0x3f800000, .f32ReinterpretI32 ]

/-- Store `3.5 : f64` at address 0 and load it back. -/
def memRoundtrip : Program :=
  [ .const 0, .f64Const 0x400C000000000000, .f64Store 0,
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

def floatConfig (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}
        code := floatModule.funcs[index]!.body
        resultArity := floatModule.funcs[index]!.results.length
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := floatModule, host := {} }], entry := ⟨0⟩ }
        wasm := floatModule.initialStore } }

theorem f64_arith :
    (runSteps 10 (floatConfig 0)).result.values? =
      some [.f64 0x4034000000000000] := by decide +kernel

theorem f32_arith :
    (runSteps 10 (floatConfig 1)).result.values? =
      some [.f32 0x40400000] := by decide +kernel

theorem f64_compare :
    (runSteps 10 (floatConfig 2)).result.values? = some [.i32 1] := by decide +kernel

theorem f64_sqrt :
    (runSteps 10 (floatConfig 3)).result.values? =
      some [.f64 0x4008000000000000] := by decide +kernel

theorem f64_min :
    (runSteps 10 (floatConfig 4)).result.values? =
      some [.f64 0x4000000000000000] := by decide +kernel

theorem conv_roundtrip :
    (runSteps 10 (floatConfig 5)).result.values? = some [.i32 7] := by decide +kernel

theorem reinterpret_one :
    (runSteps 10 (floatConfig 6)).result.values? =
      some [.f32 0x3F800000] := by decide +kernel

theorem mem_roundtrip :
    (runSteps 10 (floatConfig 7)).result.values? =
      some [.f64 0x400C000000000000] := by decide +kernel

theorem mem_roundtrip_terminates :
    TerminatesWith (floatConfig 7)
      (fun values _ => values = [.f64 0x400C000000000000]) :=
  runSteps_values_terminates mem_roundtrip

theorem mem_roundtrip_partial :
    PartiallyMeets (floatConfig 7)
      (fun values _ => values = [.f64 0x400C000000000000]) :=
  mem_roundtrip_terminates.toPartiallyMeets

end Wasm
