import Project.Mergesort.Program
import Interpreter.Wasm.Host.StdIO

/-!
# Specification for `mergesort`

The exported Rust function reads a space-separated list of decimal `u64`
values from standard input and writes the sorted values in the same format.

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

/-- The exact textual format consumed and produced by the Rust entry point:
base-ten numbers separated by one ASCII space, with no trailing newline. -/
def encodeValues (values : List UInt64) : List UInt8 :=
  (String.intercalate " " (values.map toString)).toUTF8.toList

/-- Initial Wasm store with `input` attached to the deterministic StdIO host. -/
def initialStore (input : List UInt8) : Store StdIO.State :=
  { («module».initialStore (α := StdIO.State)) with
      host := StdIO.State.ofInput input }

/-- Initialize the generated module at its exported `mergesort` entry point. -/
def initialConfig? (input : List UInt8) : Option (SmallStep.Config StdIO.State) := do
  let entry ← «module».findExport "mergesort"
  (SmallStep.initConfig
    { module := «module», host := StdIO.env }
    entry (initialStore input) []).toOption

/-- Fuel-free relational execution over byte streams. -/
def RunsBytes (input output : List UInt8) : Prop :=
  ∃ initial,
    initialConfig? input = some initial ∧
    SmallStep.TerminatesWith initial (fun values final =>
      values = [] ∧ final.wasm.host.output = output)

/-- The host-level execution relation exposed to clients of the specification. -/
def RunsValues (input output : List UInt64) : Prop :=
  RunsBytes (encodeValues input) (encodeValues output)

/-- `output` is sorted in nondecreasing order and contains exactly the input
values, including multiplicities. -/
def SortedPermutation (input output : List UInt64) : Prop :=
  output.Pairwise (· ≤ ·) ∧ List.Perm input output

/-- For every input, the exported Rust function terminates with an output that
is sorted in nondecreasing order and is a permutation of that input.

This combines completeness (an execution and output exist) with functional
correctness (that output is a sorted permutation). -/
@[spec_of "rust-exported" "mergesort::mergesort"]
def MergesortSpec : Prop :=
  ∀ input, ∃ output,
    RunsValues input output ∧ SortedPermutation input output

end Project.Mergesort.Spec
