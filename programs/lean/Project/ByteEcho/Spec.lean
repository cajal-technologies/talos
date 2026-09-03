import Project.ByteEcho.Program
import Interpreter.Wasm.Host.Universal

/-!
# Specification for `byte_echo`

The public contract supplies exactly one byte through `stdio.read` and requires
the export to write that same byte through `stdio.write`.
-/

namespace Project.ByteEcho.Spec

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

/-- The one semantic byte supplied to `byte_echo`. The singleton stream
encoding belongs in `args`, not in the public proposition. -/
structure Input where
  byte : UInt8

/-- The semantic byte returned by `byte_echo`. -/
abbrev Output := UInt8

/-- Encode one semantic input as the export's initial host state. -/
def args (input : Input) : ExportCall Universal.State :=
  ExportCall.ofHost «module» (Universal.State.ofInput [input.byte])

/-- Recognize the semantic output in the export's normal terminal state. -/
def result (output : Output) : ExportReturn Universal.State → Prop :=
  fun returned =>
    returned.values = [] ∧ returned.final.host.stdio.output = [output]

/-- Fuel-free execution of a named export in this compiled module. -/
abbrev Runs := Universal.RunsExport «module»

/-- For every semantic input there is an output produced by the compiled
`byte_echo` export, and that output is exactly the input byte. -/
@[spec_of "rust-exported" "byte_echo::byte_echo"]
def ByteEchoSpec : Prop :=
  ∀ input : Input,
    ∃ output : Output,
      Runs "byte_echo" (args input) (result output) ∧
      output = input.byte

end Project.ByteEcho.Spec
