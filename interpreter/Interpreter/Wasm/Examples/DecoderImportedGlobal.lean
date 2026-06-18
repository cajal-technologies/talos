import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-! ## Example: imported-global index offset in the WAT decoder

    Regression test for `collectGlobalNames`. Per the wasm spec, imported
    globals occupy the low indices (`0 … N-1`) and a module's own declared
    globals follow (`N …`). A `global.get $declared` must therefore resolve
    to `N`, not `0` (under-count: imports ignored) and not `2N` (over-count:
    imports counted twice).

    Nothing in the Rust corpus imports globals, so this offset is invisible
    to ordinary builds. This module exercises one imported + one declared
    global end-to-end so a future miscount fails the build. -/

namespace Wasm
namespace DecoderImportedGlobal

/-- A `.wat` module with one imported global `spectest.ig : i32` (unified
index `0`) and one declared global `$d` (index `1`) initialised to `99`.
`getD` reads `$d`; its decoded body must be `global.get 1`. -/
def importedGlobalWat : String := "
(module
  (import \"spectest\" \"ig\" (global $ig i32))
  (global $d i32 (i32.const 99))
  (func $getD (export \"getD\") (result i32)
    global.get $d))
"

private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode importedGlobalWat with
  | .ok m    => m
  | .error _ => default

/-- One imported global at index `0`, one declared global at index `1`. -/
theorem importedGlobalWat_global_layout :
    decoded.importedGlobals = [("spectest", "ig")] ∧
    decoded.globals.length = 2 ∧
    decoded.globals.getLast?.map (·.init) = some (.i32 99) := by
  native_decide

/-- Index baked into the first `global.get` of the first function, if any.
Projected to `Option Nat` because `Instruction` has no `DecidableEq`. -/
private def firstGlobalGetIdx (m : Module) : Option Nat :=
  match m.funcs.head?.map (·.body) with
  | some (Instruction.globalGet i :: _) => some i
  | _                                   => none

/-- The crux: `global.get $d` resolves to index `1` (`importedGlobals.length
+ 0`). A double-counted import would bake in `2`, a dropped import `0`. -/
theorem importedGlobalWat_getD_index :
    firstGlobalGetIdx decoded = some 1 := by
  native_decide

/-- End-to-end: running `getD` reads the declared global and returns `99`.
A wrong index would read the import's zero slot (`0`) or trap out of
bounds (empty result). -/
private def emptyEnv : HostEnv Unit := { funcs := [] }

private def runVals (m : Module) (env : HostEnv Unit) (idx : Nat)
    (st : Store Unit) (args : List Value) : List Value :=
  match run 10 m idx st args env with
  | .Success vs _ => vs
  | _ => []

theorem importedGlobalWat_getD_returns_99 :
    runVals decoded emptyEnv 0 (decoded.initialStore (α := Unit)) []
      = [.i32 99] := by
  native_decide

end DecoderImportedGlobal
end Wasm
