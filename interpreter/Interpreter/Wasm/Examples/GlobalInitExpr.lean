import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.SmallStep

/-! ## Example: constant-expression global initializers

    Extended constant expressions and GC allocation expressions are evaluated
    during instantiation. The resulting physical stores are then observed by
    the authoritative small-step machine.
-/

namespace Wasm
open SmallStep
namespace GlobalInitExpr

private def decodeWat (wat : String) : Wasm.Module :=
  match Wasm.Decoder.Wat.decode wat with
  | .ok module => module
  | .error _ => default

private def initializedStore (module : Module) : Store Unit :=
  module.runConstGlobals 64 (module.initialStore (α := Unit)) {}

private def initializedConfig (module : Module) : Config Unit :=
  { expr := .running
      { locals := {}
        code := module.funcs[0]!.body
        resultArity := module.funcs[0]!.results.length
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module, host := {} }], entry := ⟨0⟩ }
        wasm := initializedStore module } }

def globalInitExprWat : String := "
(module
  (global $g i32 (i32.sub (i32.mul (i32.const 20) (i32.const 3)) (i32.const 18)))
  (func $getG (export \"getG\") (result i32)
    global.get $g))
"

private def decoded : Wasm.Module := decodeWat globalInitExprWat

theorem decoded_global_keeps_initExpr :
    (decoded.globals[0]?.map (·.initExpr.isEmpty)).getD true = false := by
  native_decide

theorem runConstGlobals_evaluates_initExpr :
    (initializedStore decoded).globals.globals[0]? = some (.i32 42) := by
  native_decide

def getGConfig : Config Unit := initializedConfig decoded

theorem getG_returns_42 :
    (runSteps 2 getGConfig).result.values? = some [.i32 42] := by
  native_decide

theorem getG_spec :
    TerminatesWith getGConfig (fun values _ => values = [.i32 42]) :=
  runSteps_values_terminates getG_returns_42

theorem getG_partial :
    PartiallyMeets getGConfig (fun values _ => values = [.i32 42]) :=
  runSteps_values_partiallyMeets getG_returns_42

/-! ### GC allocator initializers (issue #109) -/

def structGlobalLeafWat : String := "
(module
  (type $s (struct (field i32)))
  (global $g (ref $s) (struct.new $s (i32.const 100)))
  (func $f (export \"f\") (result i32)
    (struct.get $s 0 (global.get $g))))
"

def structGlobalArithWat : String := "
(module
  (type $s (struct (field i32)))
  (global $g (ref $s) (struct.new $s (i32.add (i32.const 50) (i32.const 50))))
  (func $f (export \"f\") (result i32)
    (struct.get $s 0 (global.get $g))))
"

private def decodedLeaf : Wasm.Module := decodeWat structGlobalLeafWat
private def decodedArith : Wasm.Module := decodeWat structGlobalArithWat

theorem leaf_struct_new_keeps_initExpr :
    (decodedLeaf.globals[0]?.map (·.initExpr.isEmpty)).getD true = false := by
  native_decide

def leafStructConfig : Config Unit := initializedConfig decodedLeaf
def arithStructConfig : Config Unit := initializedConfig decodedArith

theorem leaf_struct_new_returns_100 :
    (runSteps 4 leafStructConfig).result.values? =
      some [.i32 100] := by
  native_decide

theorem leaf_struct_new_spec :
    TerminatesWith leafStructConfig
      (fun values _ => values = [.i32 100]) :=
  runSteps_values_terminates leaf_struct_new_returns_100

theorem leaf_struct_new_partial :
    PartiallyMeets leafStructConfig
      (fun values _ => values = [.i32 100]) :=
  runSteps_values_partiallyMeets leaf_struct_new_returns_100

theorem arith_struct_new_returns_100 :
    (runSteps 4 arithStructConfig).result.values? =
      some [.i32 100] := by
  native_decide

theorem arith_struct_new_spec :
    TerminatesWith arithStructConfig
      (fun values _ => values = [.i32 100]) :=
  runSteps_values_terminates arith_struct_new_returns_100

theorem arith_struct_new_partial :
    PartiallyMeets arithStructConfig
      (fun values _ => values = [.i32 100]) :=
  runSteps_values_partiallyMeets arith_struct_new_returns_100

end GlobalInitExpr
end Wasm
