import Project.Mergesort.Program
import Interpreter.Wasm.Host.Universal
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
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by native_decide

/-- Every import of the generated module is implemented by the universal host. -/
theorem universal_host_covers : Universal.covers «module» = true := by native_decide

/-- The name-keyed universal environment satisfies the matching relational
host contract regardless of generated import indices. -/
theorem universal_env_satisfies :
    (Universal.envFor «module»).Satisfies «module» (Universal.specFor «module») :=
  Universal.envFor_satisfies «module»

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

/-- Kernel-checked reconstruction of a 32-bit natural from its four bytes.
This avoids making the public codec, and therefore every theorem mentioning
its serialization, depend on the native bit-vector decision axiom. -/
private theorem reassemble32 (n : Nat) (h : n < 2 ^ 32) :
    n % 2 ^ 8 ||| (((n >>> 8) % 2 ^ 8) <<< 8) % 2 ^ 32 |||
      (((n >>> 16) % 2 ^ 8) <<< 16) % 2 ^ 32 |||
      (((n >>> 24) % 2 ^ 8) <<< 24) % 2 ^ 32 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hi8 : i < 8
  · simp [hi8, show i < 32 by omega, show ¬i ≥ 8 by omega,
      show ¬i ≥ 16 by omega, show ¬i ≥ 24 by omega]
  by_cases hi16 : i < 16
  · have h8le : i ≥ 8 := by omega
    have heq : 8 + (i - 8) = i := by omega
    simp [hi8, h8le, heq, show i < 32 by omega,
      show i - 8 < 8 by omega, show ¬i ≥ 16 by omega,
      show ¬i ≥ 24 by omega]
  by_cases hi24 : i < 24
  · have h16le : i ≥ 16 := by omega
    have heq : 16 + (i - 16) = i := by omega
    simp [hi8, h16le, heq, show i < 32 by omega,
      show ¬i - 8 < 8 by omega, show i - 16 < 8 by omega,
      show ¬i ≥ 24 by omega]
  by_cases hi32 : i < 32
  · have h24le : i ≥ 24 := by omega
    have heq : 24 + (i - 24) = i := by omega
    simp [hi8, hi32, h24le, heq, show ¬i - 8 < 8 by omega,
      show ¬i - 16 < 8 by omega, show i - 24 < 8 by omega]
  · have hibound : n.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le h
        (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hi8, hibound, show ¬i < 32 by omega,
      show ¬i - 8 < 8 by omega, show ¬i - 16 < 8 by omega,
      show ¬i - 24 < 8 by omega]

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
    exact reassemble32 value.toNat (UInt32.toNat_lt value)

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
