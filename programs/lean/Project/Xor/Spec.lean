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
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by native_decide

/-- Fuel-free relational execution of the exported byte-stream program. -/
def RunsBytes (input output : List UInt8) : Prop :=
  Universal.RunsBytes «module» "xor" input output

/-- For every pair of bytes, running the program with exactly those two input
bytes terminates with their XOR as the singleton output. -/
@[spec_of "rust-exported" "xor::xor"]
def XorSpec : Prop :=
  ∀ first second : UInt8, RunsBytes [first, second] [first ^^^ second]

end Project.Xor.Spec
