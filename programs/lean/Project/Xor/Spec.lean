import Project.Xor.Program
import Interpreter.Wasm.Host.StdIO

/-!
# Specification for `xor`

The public contract supplies exactly two bytes through `stdio.read` and
requires the export to write their one-byte XOR through `stdio.write`.
-/

namespace Project.Xor.Spec

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
  StdIO.Runs «module» "xor" input output

/-- For every pair of bytes, running the program with exactly those two input
bytes terminates with their XOR as the singleton output. -/
@[spec_of "rust-exported" "xor::xor"]
def XorSpec : Prop :=
  ∀ first second : UInt8, RunsBytes [first, second] [first ^^^ second]

end Project.Xor.Spec
