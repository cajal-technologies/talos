import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Examples.Harness

kernel_decoder

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## Example: constant-expression global initializers

    Extended constant expressions and GC allocation expressions are evaluated
    during instantiation. The resulting physical stores are then observed by
    the authoritative small-step machine.
-/

namespace Wasm
open SmallStep
namespace GlobalInitExpr

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

private def decoded : Wasm.Module :=
  Wasm.Examples.decodeOrDefault globalInitExprWat

theorem decoded_global_keeps_initExpr :
    (decoded.globals[0]?.map (·.initExpr.isEmpty)).getD true = false := by cbv

theorem runConstGlobals_evaluates_initExpr :
    (initializedStore decoded).globals.globals[0]? = some (.i32 42) := by cbv

def getGConfig : Config Unit := initializedConfig decoded

theorem getG_returns_42 :
    (runSteps 2 getGConfig).result.values? = some [.i32 42] := by cbv

theorem getG_terminates :
    TerminatesWith getGConfig (fun values _ => values = [.i32 42]) :=
  runSteps_values_terminates getG_returns_42

theorem getG_partial :
    PartiallyMeets getGConfig (fun values _ => values = [.i32 42]) :=
  getG_terminates.toPartiallyMeets

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

private def decodedLeaf : Wasm.Module :=
  Wasm.Examples.decodeOrDefault structGlobalLeafWat
private def decodedArith : Wasm.Module :=
  Wasm.Examples.decodeOrDefault structGlobalArithWat

theorem leaf_struct_new_keeps_initExpr :
    (decodedLeaf.globals[0]?.map (·.initExpr.isEmpty)).getD true = false := by cbv

def leafStructConfig : Config Unit := initializedConfig decodedLeaf
def arithStructConfig : Config Unit := initializedConfig decodedArith

theorem leaf_struct_new_returns_100 :
    (runSteps 4 leafStructConfig).result.values? =
      some [.i32 100] := by cbv

theorem leaf_struct_new_terminates :
    TerminatesWith leafStructConfig
      (fun values _ => values = [.i32 100]) :=
  runSteps_values_terminates leaf_struct_new_returns_100

theorem leaf_struct_new_partial :
    PartiallyMeets leafStructConfig
      (fun values _ => values = [.i32 100]) :=
  leaf_struct_new_terminates.toPartiallyMeets

theorem arith_struct_new_returns_100 :
    (runSteps 4 arithStructConfig).result.values? =
      some [.i32 100] := by cbv

theorem arith_struct_new_terminates :
    TerminatesWith arithStructConfig
      (fun values _ => values = [.i32 100]) :=
  runSteps_values_terminates arith_struct_new_returns_100

theorem arith_struct_new_partial :
    PartiallyMeets arithStructConfig
      (fun values _ => values = [.i32 100]) :=
  arith_struct_new_terminates.toPartiallyMeets

end GlobalInitExpr
end Wasm
