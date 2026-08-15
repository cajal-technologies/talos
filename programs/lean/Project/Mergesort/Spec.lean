import Project.Mergesort.CoreProof
import Project.Mergesort.StdIO

/-!
# Specification for `mergesort`

The exported Rust function reads packed little-endian `u64` values from
standard input and writes the sorted values in the same format.

The public specification deliberately hides fuel, linear memory, allocator
state, and the implementation's internal scratch array. `RunsValues` is the
boundary between those execution details and the mathematical contract.
-/

namespace Project.Mergesort.Spec

open Wasm

/-- The generated module is linked against Talos's canonical two-function
standard-I/O ABI. -/
theorem module_imports : «module».imports = StdIO.imports := by
  rfl

/-- Consequently the concrete deterministic StdIO environment satisfies the
relational host contract expected by the generated module. -/
theorem stdio_env_satisfies : StdIO.env.Satisfies «module» StdIO.spec :=
  StdIO.env_satisfies «module» module_imports

/-- The packed little-endian format consumed and produced by the entry point. -/
def encodeValues (values : List UInt64) : List UInt8 :=
  Pure.encodeValues values

/-- Fuel-free relational execution over byte streams through the exact three
generated calls that constitute the exported `mergesort` driver. -/
def RunsBytes (input output : List UInt8) : Prop :=
  Project.Mergesort.StdIO.RunsBytes input output

/-- The host-level execution relation exposed to clients of the specification. -/
def RunsValues (input output : List UInt64) : Prop :=
  RunsBytes (encodeValues input) (encodeValues output)

/-- Maximum number of values reserved by the verified Wasm entry point. -/
def maxValues : Nat := 4096

/-- Size of its packed input/output byte buffer. -/
def inputCapacity : Nat := 8 * maxValues

/-- The explicit finite-memory precondition of the exported Wasm program. -/
def Fits (input : List UInt64) : Prop :=
  input.length ≤ maxValues

theorem fits_bytes {input : List UInt64} (hfit : Fits input) :
    (encodeValues input).length ≤ inputCapacity := by
  simpa only [encodeValues, Pure.encodeValues_length, inputCapacity] using
    Nat.mul_le_mul_left 8 hfit

/-- `output` is sorted in nondecreasing order and contains exactly the input
values, including multiplicities. -/
def SortedPermutation (input output : List UInt64) : Prop :=
  Pure.SortedPermutation input output

/-- For every input fitting the module's fixed buffers, the exported Rust
function terminates with an output that is sorted in nondecreasing order and is
a permutation of that input.

This combines completeness (an execution and output exist) with functional
correctness (that output is a sorted permutation). -/
@[spec_of "rust-exported" "mergesort::mergesort"]
def MergesortSpec : Prop :=
  ∀ input, Fits input → ∃ output,
    RunsValues input output ∧ SortedPermutation input output

end Project.Mergesort.Spec
