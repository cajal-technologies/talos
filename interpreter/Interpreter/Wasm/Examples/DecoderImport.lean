import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.SmallStep

/-! ## Example: decoding a WAT module with imports (M9)

    Exercises the `(import "mod" "name" (func …))` syntax end-to-end:
    1. A hand-written `.wat`-flavored string is decoded.
    2. The resulting `Module.imports` matches the expected signature.
    3. The imported function lives at unified index `0`; the in-module
       caller lives at index `1`.
    4. Calling the wasm function with a concrete host produces the
       expected return value. -/

namespace Wasm
open SmallStep
namespace DecoderImport

/-- A `.wat` module with a single host import (`env.inc : i32 → i32`)
and a single in-module function `caller(x)` that forwards `x` to the
import. The import lands at unified index `0`; `caller` at index `1`. -/
def importWat : String := "
(module
  (import \"env\" \"inc\" (func $inc (param i32) (result i32)))
  (func $caller (export \"caller\") (param $x i32) (result i32)
    local.get $x
    call $inc))
"

/-- Decoder roundtrip: extract the decoded `Module` and assert the
shape of its `imports`, `funcs` body, and `exports`. We project each
field rather than comparing whole `Module`s because `Module` has no
`DecidableEq` instance. -/
private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode importWat with
  | .ok module => module
  | .error _ => default

/-- The single import is `env.inc : i32 → i32`. -/
theorem importWat_imports :
    decoded.imports = [{ «module» := "env"
                         name     := "inc"
                         params   := [.i32]
                         results  := [.i32] }] := by
  native_decide

/-- Exactly one in-module function, with the expected params/results. -/
theorem importWat_funcs_shape :
    decoded.funcs.length = 1 ∧
    decoded.funcs.head?.map (·.params)  = some [.i32] ∧
    decoded.funcs.head?.map (·.results) = some [.i32] := by
  native_decide

/-- The export `caller` resolves to unified index `1`
(`imports.length + 0`), not `0`. -/
theorem importWat_exports_funcIdx :
    decoded.exports = [{ name := "caller", funcIdx := 1 }] := by
  native_decide

def typedStructuredWat : String := "
(module
  (func (param i32) (result i64)
    local.get 0
    block (param i32) (result i64)
      i64.extend_i32_u
    end))
"

private def typedStructuredDecoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode typedStructuredWat with
  | .ok module => module
  | .error _ => default

def decodedBlockSignature :
    Option (Nat × Nat × List ValueType × List ValueType) :=
  match typedStructuredDecoded.funcs.head?.bind
      (fun (function : Wasm.Function) => function.body[1]?) with
  | some (Wasm.Instruction.block
      paramArity resultArity _ paramTypes resultTypes) =>
      some (paramArity, resultArity, paramTypes, resultTypes)
  | _ => none

theorem decoder_retains_exact_block_signature :
    decodedBlockSignature = some (1, 1, [.i32], [.i64]) := by
  native_decide

/-- The decoded module is byte-for-byte identical to a hand-built one
that pairs with the same `inc` host. End-to-end smoke test: decoding
+ dispatch + return all line up. -/
def incHost : HostFn Unit :=
  { params  := [.i32]
    results := [.i32]
    invoke  := fun st args => match args with
      | [.i32 x] => .Return [.i32 (x + 1)] st
      | _        => .Trap st "inc: bad arity" }

def incEnv : HostEnv Unit := { funcs := [incHost] }

/-- Small-step entry configuration for the decoded in-module caller. -/
def callerConfig : Config Unit :=
  { expr := .running
      { locals := decoded.funcs[0]!.toLocals [.i32 41]
        code := decoded.funcs[0]!.body
        resultArity := decoded.funcs[0]!.results.length
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := decoded, host := incEnv }], entry := ⟨0⟩ }
        wasm := decoded.initialStore } }

/-- Calling `caller(41)` against `incEnv` returns `[42]` through the
authoritative host-call step. -/
theorem caller_against_incEnv :
    (runSteps 3 callerConfig).result.values? = some [.i32 42] := by
  native_decide

theorem caller_against_incEnv_spec :
    TerminatesWith callerConfig (fun values _ => values = [.i32 42]) :=
  runSteps_values_terminates caller_against_incEnv

theorem caller_against_incEnv_partial :
    PartiallyMeets callerConfig (fun values _ => values = [.i32 42]) :=
  runSteps_values_partiallyMeets caller_against_incEnv

end DecoderImport
end Wasm
