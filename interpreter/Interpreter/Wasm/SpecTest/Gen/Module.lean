import Interpreter.Wasm.Syntax
import Interpreter.Wasm.SpecTest.Gen.Basic

/-!
# Constants read off a module

The module-derived family perturbs the numbers the program itself mentions:
every `i32.const`/`i64.const` immediate (including those nested in blocks,
loops and conditionals, and in global initialisers) and the declared memory
bounds, in pages and in bytes.
-/

namespace Wasm.SpecTest

mutual
  partial def instructionConstants : Instruction → List Nat
    | .const value => [value.toNat]
    | .constI64 value => [value.toNat]
    | .block _ _ body _ _ => programConstants body
    | .loop _ _ body _ _ => programConstants body
    | .iff _ _ thenBody elseBody _ _ => programConstants thenBody ++ programConstants elseBody
    | .tryTable _ _ _ body _ _ => programConstants body
    | .memOp _ inner => instructionConstants inner
    | _ => []

  partial def programConstants (program : List Instruction) : List Nat :=
    program.flatMap instructionConstants
end

/-- The distinct constants of a module, in increasing order. -/
def moduleConstants (m : Module) : List Nat :=
  let code := m.funcs.flatMap (fun f => programConstants f.body)
  let globalInits := m.globals.flatMap (fun g => programConstants g.initExpr)
  let memory := match m.memory with
    | some decl =>
      let pages := [decl.pagesMin.toNat] ++ (decl.pagesMax.map (·.toNat)).toList
      pages ++ pages.map (· * 65536)
    | none => []
  (dedup (code ++ globalInits ++ memory)).mergeSort (fun a b => decide (a ≤ b))

end Wasm.SpecTest
