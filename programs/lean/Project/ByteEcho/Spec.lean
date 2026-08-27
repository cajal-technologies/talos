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

/-- Fuel-free relational execution of the exported byte-stream program. -/
def RunsBytes (input output : List UInt8) : Prop :=
  Universal.RunsBytes «module» "byte_echo" input output

/-- For every byte, running the program with that singleton input terminates
with exactly the same singleton output. -/
@[spec_of "rust-exported" "byte_echo::byte_echo"]
def ByteEchoSpec : Prop :=
  ∀ byte : UInt8, RunsBytes [byte] [byte]

end Project.ByteEcho.Spec
