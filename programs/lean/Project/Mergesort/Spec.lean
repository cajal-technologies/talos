import Project.Mergesort.Program
import Interpreter.Wasm.Host.Universal
import CodeLib.UInt32
import CodeLib.WordCodec
import Std.Tactic.BVDecide

/-!
# Specification for `mergesort`

The exported Rust function reads packed little-endian `UInt32` values from
standard input until exhaustion and writes the sorted values in the same
four-byte-per-value format.

The public specification deliberately hides fuel, linear memory, allocator
state, and the implementation's internal scratch array. Every finite terminal
trace is classified as either a correctly sorted output or the allocator's
distinguished `talos.oom` host trap; termination itself is not claimed.
-/

namespace Project.Mergesort.Spec

open Wasm

/-- The generated module imports standard I/O plus the allocator-private,
terminal OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by decide +kernel

/-- Every import of the generated module is implemented by the universal host. -/
theorem universal_host_covers : Universal.covers «module» = true := by decide +kernel

/-- The four little-endian bytes of a 32-bit word. -/
def encodeWord (value : UInt32) : List UInt8 :=
  [ value.toUInt8
  , (value >>> 8).toUInt8
  , (value >>> 16).toUInt8
  , (value >>> 24).toUInt8 ]

/-- Decode one four-byte little-endian word.  The fallback is outside the
`WordCodec` interface: `deserialize` calls this only on a chunk of width four. -/
def decodeWord : List UInt8 → UInt32
  | b₀ :: b₁ :: b₂ :: b₃ :: _ =>
      b₀.toUInt32 ||| (b₁.toUInt32 <<< 8) |||
        (b₂.toUInt32 <<< 16) ||| (b₃.toUInt32 <<< 24)
  | _ => 0

/-- The one canonical codec used by streams and all memory-array views in the
merge-sort formalization. -/
def u32Codec : WordCodec UInt32 where
  width := 4
  encode := encodeWord
  decode := decodeWord
  width_pos := by decide
  encode_length := fun _ => rfl
  decode_encode := by
    intro value
    simp only [encodeWord, decodeWord]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft,
      UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
      UInt32.toNat_shiftRight]
    exact Nat.reassemble32_of_lt value.toNat (UInt32.toNat_lt value)

/-- The exact packed format consumed and produced by the Rust entry point. -/
def encodeValues (values : List UInt32) : List UInt8 :=
  u32Codec.serialize values

/-- `output` is sorted in nondecreasing order and contains exactly the input
values, including multiplicities. -/
def SortedPermutation (input output : List UInt32) : Prop :=
  output.Pairwise (· ≤ ·) ∧ List.Perm input output

/-- Everything publicly observable at the end of a finite execution. -/
structure RunOutcome where
  outcome : SmallStep.ObservableOutcome
  final : Universal.State

/-- The call returned normally and wrote `output` in the public stream format. -/
def ReturnsOutput (run : RunOutcome) (output : List UInt32) : Prop :=
  run.outcome = .done [] ∧
    run.final.stdio.output = encodeValues output

/-- The call terminated with the allocator's distinguished OOM outcome. -/
def RanOutOfMemory (run : RunOutcome) : Prop :=
  run.outcome = .trapped (.host OOM.trapMessage) ∧
    run.final.oom.raised = true

/-- Every finite terminal execution either satisfies `post` or terminates with
the allocator's distinguished OOM outcome.  This does not assert termination. -/
def PartiallyRuns (input : List UInt32) (post : RunOutcome → Prop) : Prop :=
  PartiallyRunsWithOutcome (Universal.envFor «module») «module» "mergesort"
    (Universal.State.ofInput (encodeValues input))
    (fun outcome final =>
      let run : RunOutcome := ⟨outcome, final⟩
      RanOutOfMemory run ∨ post run)

/-- A successful execution returns the encoding of a sorted permutation. -/
def Post (input : List UInt32) (run : RunOutcome) : Prop :=
  ∃ output : List UInt32,
    ReturnsOutput run output ∧ SortedPermutation input output

/-- Public partial-correctness contract for the exported call.  Every finite
terminal execution either reports OOM or satisfies `Post`. -/
@[spec_of "rust-exported-partial" "mergesort::mergesort"]
def PublicEntrySpecification : Prop :=
  ∀ input : List UInt32,
    PartiallyRuns input (Post input)

end Project.Mergesort.Spec
