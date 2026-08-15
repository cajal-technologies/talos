import Project.Mergesort.FunctionSpecs
import Interpreter.Wasm.Host.StdIO

/-!
# Specification for the original generated `mergesort`

The unchanged Rust export reads one space-separated line of decimal `u64`
values and writes the sorted values in the same format. Fuel, the allocator,
linear memory, and the internal scratch vector are hidden at this boundary.
-/

namespace Project.Mergesort.Spec

open Wasm

theorem module_imports : «module».imports = StdIO.imports := by rfl

theorem stdio_env_satisfies : StdIO.env.Satisfies «module» StdIO.spec :=
  StdIO.env_satisfies «module» module_imports

def encodeValues (values : List UInt64) : List UInt8 :=
  Pure.encodeValues values

def RunsBytes (input output : List UInt8) : Prop :=
  StdIO.Runs «module» "mergesort" input output

def RunsValues (input output : List UInt64) : Prop :=
  RunsBytes (encodeValues input) (encodeValues output)

/-- A conservative explicit bound for the finite Wasm-memory proof. The
nonempty condition is semantic: `"".split(' ')` yields an empty token, whose
`u64` parse is unwrapped by the original Rust program. -/
def Fits (input : List UInt64) : Prop :=
  input ≠ [] ∧ input.length ≤ 4096

theorem Fits.nonempty {input : List UInt64} (h : Fits input) : input ≠ [] :=
  h.1

theorem Fits.length_le {input : List UInt64} (h : Fits input) :
    input.length ≤ 4096 :=
  h.2

def SortedPermutation (input output : List UInt64) : Prop :=
  Pure.SortedPermutation input output

@[spec_of "rust-exported" "mergesort::mergesort"]
def MergesortSpec : Prop :=
  ∀ input, Fits input → ∃ output,
    RunsValues input output ∧ SortedPermutation input output

end Project.Mergesort.Spec
