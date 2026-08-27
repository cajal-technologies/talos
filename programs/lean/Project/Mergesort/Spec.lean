import Project.Mergesort.Program
import Interpreter.Wasm.Host.Universal

/-!
# Specification for `mergesort`

The exported Rust function reads packed little-endian `UInt32` values from
standard input until exhaustion and writes the sorted values in the same
four-byte-per-value format.

The public specification deliberately hides fuel, linear memory, allocator
state, and the implementation's internal scratch array. Its two exhaustive
terminal outcomes are a correctly sorted output and the allocator's
distinguished `talos.oom` host trap.
-/

namespace Project.Mergesort.Spec

open Wasm

/-- The generated module imports standard I/O plus the allocator-private,
terminal OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by
  native_decide

/-- Every import of the generated module is implemented by the universal host. -/
theorem universal_host_covers : Universal.covers «module» = true := by
  native_decide

/-- The name-keyed universal environment satisfies the matching relational
host contract regardless of generated import indices. -/
theorem universal_env_satisfies :
    (Universal.envFor «module»).Satisfies «module» (Universal.specFor «module») :=
  Universal.envFor_satisfies «module»

/-- The four little-endian bytes of a 32-bit word. -/
def encodeWord (value : UInt32) : List UInt8 :=
  [ (value &&& 0xff).toUInt8
  , ((value >>> 8) &&& 0xff).toUInt8
  , ((value >>> 16) &&& 0xff).toUInt8
  , ((value >>> 24) &&& 0xff).toUInt8 ]

/-- The exact packed format consumed and produced by the Rust entry point. -/
def encodeValues (values : List UInt32) : List UInt8 :=
  values.flatMap encodeWord

/-- Fuel-free successful execution over byte streams through the composite host. -/
def RunsBytes (input output : List UInt8) : Prop :=
  Universal.RunsBytes «module» "mergesort" input output

/-- Fuel-free terminal resource exhaustion. The trap reason and the typed host
marker must both identify the allocator's `talos.oom` call, so an unrelated
host trap cannot satisfy this outcome. -/
def RunsOutOfMemoryBytes (input : List UInt8) : Prop :=
  TrapsWithHost (Universal.envFor «module») «module» "mergesort"
    (Universal.State.ofInput input) (.host OOM.trapMessage)
    (fun final => final.oom.raised = true)

/-- The host-level execution relation exposed to clients of the specification. -/
def RunsValues (input output : List UInt32) : Prop :=
  RunsBytes (encodeValues input) (encodeValues output)

/-- The value-level reading of the distinguished terminal OOM outcome. -/
def RunsOutOfMemory (input : List UInt32) : Prop :=
  RunsOutOfMemoryBytes (encodeValues input)

/-- `output` is sorted in nondecreasing order and contains exactly the input
values, including multiplicities. -/
def SortedPermutation (input output : List UInt32) : Prop :=
  output.Pairwise (· ≤ ·) ∧ List.Perm input output

/-- For every input, the exported Rust function has one of two finite terminal
outcomes: it returns a sorted permutation, or its private allocator calls the
distinguished OOM host function. Divergence and unrelated traps satisfy neither
branch. -/
@[spec_of "rust-exported" "mergesort::mergesort"]
def MergesortSpec : Prop :=
  ∀ input,
    (∃ output, RunsValues input output ∧ SortedPermutation input output) ∨
    RunsOutOfMemory input

end Project.Mergesort.Spec
