import Project.ByteEcho.Program
import Interpreter.Wasm.Host.StdIO

/-!
# Specification for `byte_echo`

The public contract supplies exactly one byte through `stdio.read` and requires
the export to write that same byte through `stdio.write`.
-/

namespace Project.ByteEcho.Spec

open Wasm

/-- The generated module is linked against Talos's canonical two-function
standard-I/O ABI. -/
theorem module_imports : «module».imports = StdIO.imports := by
  rfl

/-- Consequently the deterministic StdIO environment implements every host
operation required by the generated module. -/
theorem stdio_env_satisfies : StdIO.env.Satisfies «module» StdIO.spec :=
  StdIO.env_satisfies «module» module_imports

/-- Fuel-free relational execution of the exported byte-stream program. -/
def RunsBytes (input output : List UInt8) : Prop :=
  StdIO.Runs «module» "byte_echo" input output

/-- For every byte, running the program with that singleton input terminates
with exactly the same singleton output. -/
@[spec_of "rust-exported" "byte_echo::byte_echo"]
def ByteEchoSpec : Prop :=
  ∀ byte : UInt8, RunsBytes [byte] [byte]

end Project.ByteEcho.Spec
