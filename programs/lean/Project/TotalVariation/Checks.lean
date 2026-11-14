import Project.TotalVariation.Spec

/-! Regression executions through Talos's actual named-export initializer.
The fuel belongs only to these internal checks; the public theorem is fuel-free.
All equalities below are reduced by the Lean kernel. -/
namespace Project.TotalVariation.Checks
open Wasm Wasm.SmallStep Project.TotalVariation.Spec

private def runExport (input : Input) : Option (List Value) := do
  let config ← startExportConfig? (HostEnv.empty : HostEnv Unit) «module»
    "total_variation" (args input)
  (runSteps 100 config).result.values?

example : runExport ⟨0, 0, 0⟩ = some [.i64 0] := by rfl
example : runExport ⟨7, 7, 7⟩ = some [.i64 0] := by rfl
example : runExport ⟨1, 4, 9⟩ = some [.i64 8] := by rfl
example : runExport ⟨9, 4, 1⟩ = some [.i64 8] := by rfl
example : runExport ⟨2, 9, 3⟩ = some [.i64 13] := by rfl
example : runExport ⟨9, 2, 8⟩ = some [.i64 13] := by rfl

-- Immediately below overflow, the exact result is still representable.
example : runExport ⟨0, 9223372036854775808, 1⟩ =
    some [.i64 18446744073709551615] := by rfl
-- Equality with 2^64 overflows: a non-strict no-overflow condition is false.
example : runExport ⟨0, 9223372036854775808, 0⟩ = some [.i64 0] := by rfl
example : Arithmetic.mathematicalValue 0 9223372036854775808 0 = 2 ^ 64 := by decide
example : runExport ⟨0, 18446744073709551615, 0⟩ =
    some [.i64 18446744073709551614] := by rfl
example : runExport ⟨18446744073709551615, 0, 18446744073709551615⟩ =
    some [.i64 18446744073709551614] := by rfl

end Project.TotalVariation.Checks
