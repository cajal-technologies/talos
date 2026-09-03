import Project.Xor.Program
import Interpreter.Wasm.Host.Universal

/-!
# Specification for `xor`

The public contract supplies exactly two bytes through `stdio.read` and
requires the export to write their one-byte XOR through `stdio.write`.
-/

namespace Project.Xor.Spec

open Wasm

/-- The generated module imports standard I/O plus the allocator's terminal
OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by
  native_decide

/-- The universal host implements every operation required by the generated
module. -/
theorem universal_env_satisfies :
    (Universal.envFor «module»).Satisfies «module» (Universal.specFor «module») :=
  Universal.envFor_satisfies «module»

/-- The two semantic bytes supplied to `xor`. Their stream representation is
kept in `args`, outside the public proposition. -/
structure Input where
  first : UInt8
  second : UInt8

/-- The semantic byte returned by `xor`. -/
abbrev Output := UInt8

/-- Encode one semantic input as the export's initial host state. -/
def args (input : Input) : ExportCall Universal.State :=
  ExportCall.ofHost «module»
    (Universal.State.ofInput [input.first, input.second])

/-- Recognize the semantic output in the export's normal terminal state. -/
def result (output : Output) : ExportReturn Universal.State → Prop :=
  fun returned =>
    returned.values = [] ∧ returned.final.host.stdio.output = [output]

/-- Fuel-free execution of a named export in this compiled module. -/
abbrev Runs := Universal.RunsExport «module»

/-- For every semantic input there is an output produced by the compiled `xor`
export, and that output is exactly the bitwise XOR of the two input bytes. -/
@[spec_of "rust-exported" "xor::xor"]
def XorSpec : Prop :=
  ∀ input : Input,
    ∃ output : Output,
      Runs "xor" (args input) (result output) ∧
      output = input.first ^^^ input.second

end Project.Xor.Spec
