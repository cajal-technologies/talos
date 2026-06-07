import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Wp.Tactic

/-! ## Example: reference instructions (`ref.null`, `ref.func`, `ref.is_null`)

    `funcref` values are modelled by `Value.funcref (Option Nat)`: `none` is
    the null reference and `some i` is a reference to function index `i`.
    These three instructions only push/inspect such values — they never read
    the store — so the spec below holds for *any* module `m` and *any*
    store `st`.

    Two halves:
    * `refReflectSpec` is a Hoare-style proof about the AST directly.
    * the `Decoded` section feeds real `.wat` text through the decoder and
      checks, by computation (`native_decide`), that the text lowers to the
      right instructions and runs to the right values — covering the
      parser path the AST proof can't see. -/

namespace Wasm

/-- `RefReflect` pushes the null reference and tests it (`ref.is_null` ⇒ 1),
then pushes a reference to function 0 and tests that (`ref.is_null` ⇒ 0),
leaving the operand stack `[.i32 0, .i32 1]` (top first). -/
def RefReflect : Program := [
  .refNull,   .refIsNull,   -- null reference      → push i32 1 (is null)
  .refFunc 0, .refIsNull    -- reference to func 0 → push i32 0 (not null)
]

theorem refReflectSpec (m : Module) (st : Store Unit) :
    wp m RefReflect
        (fun c => c = .Fallthrough st
                    { params := [], locals := [], values := [.i32 0, .i32 1] })
        st { params := [], locals := [], values := [] } := by
  unfold RefReflect
  wp_run
  simp

namespace Decoded

/-- A `.wat` module exercising all three reference instructions.
`$f` is function index 0; `null_is_null` (index 1) returns `ref.is_null`
of the null reference (⇒ 1); `func_is_null` (index 2) returns
`ref.is_null` of a reference to `$f` (⇒ 0). -/
def refWat : String := "
(module
  (func $f (result i32) i32.const 7)
  (func $null_is_null (export \"null_is_null\") (result i32)
    ref.null func
    ref.is_null)
  (func $func_is_null (export \"func_is_null\") (result i32)
    ref.func $f
    ref.is_null))
"

private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode refWat with
  | .ok m    => m
  | .error _ => default

/-- Decoding succeeds with all three functions (rules out the `default`
fallback above; `Instruction` has no `DecidableEq`, so we check a
decidable projection rather than the bodies directly). -/
theorem decodes_three_funcs : decoded.funcs.length = 3 := by native_decide

private def runVals (idx : Nat) : List Value :=
  match run 10 decoded idx (decoded.initialStore (α := Unit)) [] with
  | .Success vs _ => vs
  | _ => []

/-- End-to-end (decode → run): the null reference is null, so
`null_is_null` returns `[1]`. A mis-decoded `ref.null`/`ref.is_null`
would change this value, so the run pins down the parser too. -/
theorem null_is_null_runs : runVals 1 = [.i32 1] := by native_decide

/-- End-to-end (decode → run): a function reference is not null, so
`func_is_null` returns `[0]`. This also pins down `ref.func $f`
resolving the name `$f` to a non-null reference. -/
theorem func_is_null_runs : runVals 2 = [.i32 0] := by native_decide

end Decoded
end Wasm
