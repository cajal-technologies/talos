import CodeLib
import Interpreter.Wasm.LeanSyntax
import Interpreter.Wasm.Decoder.Wat
import Lean.Elab.Term

/-!
# Support for generated Wasm modules

Generated `Program.lean` files import this module rather than depending on
interpreter internals directly. It re-exports CodeLib's proof surface together
with compact syntax that elaborates to ordinary Wasm AST literals.
-/

namespace Wasm

open Lean Elab Term

/- `watModule%` turns the decoded value into an ordinary kernel expression.
These instances are elaborator support only: generated definitions contain the
resulting constructors, not a decoder invocation or an `IO` action. -/
deriving instance Lean.ToExpr for Simd.Shape
deriving instance Lean.ToExpr for Simd.ICmp
deriving instance Lean.ToExpr for Simd.FCmp
deriving instance Lean.ToExpr for Simd.UnOp
deriving instance Lean.ToExpr for Simd.BinOp
deriving instance Lean.ToExpr for Simd.TestOp
deriving instance Lean.ToExpr for Simd.ShiftOp
deriving instance Lean.ToExpr for GcHeapType
deriving instance Lean.ToExpr for ValueType
deriving instance Lean.ToExpr for AnyRef
deriving instance Lean.ToExpr for StorageType
deriving instance Lean.ToExpr for FieldType
deriving instance Lean.ToExpr for Value
deriving instance Lean.ToExpr for CatchClause
deriving instance Lean.ToExpr for GcOp
deriving instance Lean.ToExpr for Instruction
deriving instance Lean.ToExpr for Function
deriving instance Lean.ToExpr for Export
deriving instance Lean.ToExpr for DataSegment
deriving instance Lean.ToExpr for MemDecl
deriving instance Lean.ToExpr for GlobalDecl
deriving instance Lean.ToExpr for FuncType
deriving instance Lean.ToExpr for CompositeType
deriving instance Lean.ToExpr for GcTypeDef
deriving instance Lean.ToExpr for TableDecl
deriving instance Lean.ToExpr for ImportDecl
deriving instance Lean.ToExpr for ElementSegment
deriving instance Lean.ToExpr for Module

/-- Decode a WAT file while elaborating and splice its complete Wasm AST into
the declaration as a literal expression. The source file therefore stays tiny,
while the resulting definition is just as reducible as a handwritten AST. -/
syntax (name := watModule) "watModule% " str : term

@[term_elab watModule] def elabWatModule : TermElab := fun stx _ => do
  let `(watModule% $pathSyntax:str) := stx | throwUnsupportedSyntax
  let path : System.FilePath := pathSyntax.getString
  let source ← IO.FS.readFile path
  let module ← match Decoder.Wat.decodeForVerification source with
    | .ok module => pure module
    | .error message => throwError "WAT decoder rejected {path}: {message}"
  pure (toExpr module)

/-- Quote all module metadata except function declarations. Generated files
provide those separately so each function body remains immediately transparent
to existing `wp_*` tactics, while data segments and other bulky metadata do not
occupy committed source text. -/
syntax (name := watModuleMetadata) "watModuleMetadata% " str : term

@[term_elab watModuleMetadata] def elabWatModuleMetadata : TermElab := fun stx _ => do
  let `(watModuleMetadata% $pathSyntax:str) := stx | throwUnsupportedSyntax
  let path : System.FilePath := pathSyntax.getString
  let source ← IO.FS.readFile path
  let module ← match Decoder.Wat.decodeForVerification source with
    | .ok module => pure module
    | .error message => throwError "WAT decoder rejected {path}: {message}"
  pure (toExpr { module with funcs := [] })

/-- Quote one function body directly. Unlike projecting it from a quoted
module list, this exposes the leading instruction to unification at reducible
transparency, which keeps the existing `wp_*` proof scripts working. -/
syntax (name := watFunctionBody) "watFunctionBody% " str num : term

@[term_elab watFunctionBody] def elabWatFunctionBody : TermElab := fun stx _ => do
  let `(watFunctionBody% $pathSyntax:str $indexSyntax:num) := stx
    | throwUnsupportedSyntax
  let path : System.FilePath := pathSyntax.getString
  let index := indexSyntax.getNat
  let source ← IO.FS.readFile path
  let module ← match Decoder.Wat.decodeForVerification source with
    | .ok module => pure module
    | .error message => throwError "WAT decoder rejected {path}: {message}"
  let some function := module.funcs[index]?
    | throwErrorAt indexSyntax
        "function index {index} is out of bounds for {path} ({module.funcs.length} functions)"
  pure (toExpr function.body)

/-- Decode the current WAT artifact and structurally compare the quoted kernel
expressions for its complete AST and the generated Lean module. This checks
every constructor, instruction, and immediate rather than merely pinning a
second copy of the WAT text inside `Program.lean`. -/
def checkWatFidelity (path : System.FilePath) (actual : Module) : IO Unit := do
  unless ← path.pathExists do
    throw (IO.userError s!"{path} is missing; cannot validate Program.lean provenance.")
  let source ← IO.FS.readFile path
  let expected ← match Decoder.Wat.decodeForVerification source with
    | .ok expected => pure expected
    | .error message => throw (IO.userError s!"{path} no longer decodes: {message}")
  unless toExpr actual == toExpr expected do
    throw (IO.userError
      s!"{path} decodes to a different Wasm module; re-run `lake exe verifier emit`.")

end Wasm
