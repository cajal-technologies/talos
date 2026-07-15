import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Examples.Harness

/-! ## Example: constant-expression global initializers in the WAT decoder

    A global initializer is a constant expression, not just a single
    `*.const`. The wasm 1.0 core spec permits `global.get` of an imported
    global, and the extended-const proposal adds `i32.add`/`i32.sub`/`i32.mul`
    (i64 ditto). Talos keeps such initializers as a program in `GlobalDecl.
    initExpr` and evaluates them at instantiation via `Module.runConstGlobals`
    rather than folding them to a literal at decode time.

    This module exercises a nested arithmetic initializer end-to-end so a
    regression — the initializer collapsing to its first operand, or the
    placeholder zero leaking through — fails the build. -/

namespace Wasm
open Wasm.Examples
namespace GlobalInitExpr

/-- A module whose only global is initialised with an extended-const
expression: `(20 * 3) - 18 = 42`. -/
def globalInitExprWat : String := "
(module
  (global $g i32 (i32.sub (i32.mul (i32.const 20) (i32.const 3)) (i32.const 18)))
  (func $getG (export \"getG\") (result i32)
    global.get $g))
"

private def decoded : Wasm.Module := decodeOrDefault globalInitExprWat

/-- The initializer is kept as a program rather than folded to a single
literal: the global's `initExpr` is non-empty. -/
theorem decoded_global_keeps_initExpr :
    (decoded.globals[0]?.map (·.initExpr.isEmpty)).getD true = false := by
  native_decide

/-- `runConstGlobals` evaluates the arithmetic initializer against the
fresh store and writes `42` into the global slot. -/
theorem runConstGlobals_evaluates_initExpr :
    (decoded.runConstGlobals 64 (decoded.initialStore (α := Unit)) {}).globals.globals[0]?
      = some (.i32 42) := by
  native_decide

private def runVals (idx : Nat) (st : Store Unit) (args : List Value) :
    List Value :=
  runValues 64 decoded idx st args

/-- End-to-end: running `getG` after initialising the globals returns `42`.
The old behaviour — placeholder `0` from `ValueType.zero`, or the first
operand `20` — would return `0` or `20` instead. -/
theorem getG_returns_42 :
    runVals 0 (decoded.runConstGlobals 64 (decoded.initialStore (α := Unit)) {}) []
      = [.i32 42] := by
  native_decide

/-! ### GC allocator initializers (issue #109)

    `struct.new` is a constant instruction, so a global may be initialised
    with a plain `(struct.new $s (i32.const 100))`. The decoder used to
    detect GC allocators only at the top level of the initializer sexpr, so
    the folded leaf form was rejected while the same allocation wrapped in
    extended-const arithmetic — caught by the (recursive) extended-const
    scan — was accepted. Both forms must decode and evaluate to the same
    module behaviour. -/

/-- Leaf form: the initializer is a folded `struct.new` with a plain
`i32.const` field value. -/
def structGlobalLeafWat : String := "
(module
  (type $s (struct (field i32)))
  (global $g (ref $s) (struct.new $s (i32.const 100)))
  (func $f (export \"f\") (result i32)
    (struct.get $s 0 (global.get $g))))
"

/-- Arithmetic form: the same allocation with the field value computed by an
extended-const expression. -/
def structGlobalArithWat : String := "
(module
  (type $s (struct (field i32)))
  (global $g (ref $s) (struct.new $s (i32.add (i32.const 50) (i32.const 50))))
  (func $f (export \"f\") (result i32)
    (struct.get $s 0 (global.get $g))))
"

private def decodedLeaf : Wasm.Module := decodeOrDefault structGlobalLeafWat
private def decodedArith : Wasm.Module := decodeOrDefault structGlobalArithWat

/-- The leaf `struct.new` initializer decodes (rather than erroring) and is
kept as a const-expr program for `runConstGlobals`. -/
theorem leaf_struct_new_keeps_initExpr :
    (decodedLeaf.globals[0]?.map (·.initExpr.isEmpty)).getD true = false := by
  native_decide

/-- End-to-end: reading the struct field of the leaf-initialised global
returns `100`. -/
theorem leaf_struct_new_returns_100 :
    runValues 64 decodedLeaf 0
      (decodedLeaf.runConstGlobals 64 (decodedLeaf.initialStore (α := Unit)) {}) []
      = [.i32 100] := by
  native_decide

/-- The arithmetic-wrapped form evaluates to the same result. -/
theorem arith_struct_new_returns_100 :
    runValues 64 decodedArith 0
      (decodedArith.runConstGlobals 64 (decodedArith.initialStore (α := Unit)) {}) []
      = [.i32 100] := by
  native_decide

end GlobalInitExpr
end Wasm
