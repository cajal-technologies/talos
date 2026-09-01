import Project.RustVec.Program
import Interpreter.Wasm.Host.Universal
import CodeLib.RustStd.Vec.Codec

/-!
# Specification for `rust_vec`

Five exports, one `Vec` access pattern each.  Every export reads the whole
standard input into a `Vec<u8>` and writes at most one result to standard
output, so each contract is stated against the pure `List` model in
`CodeLib.RustStd.Vec.Basic` and the wire format in `CodeLib.RustStd.Vec.Codec`.

The contracts are partial, not total.  `read_all` allocates in proportion to
the input, so an allocation failure is a reachable terminal outcome for every
one of these exports; the `talos.oom` host trap is therefore admitted as an
alternative to a correct write, in the shape `Project.Mergesort.Spec` uses.
Fuel, linear memory, and allocator state stay hidden.
-/

namespace Project.RustVec.Spec

open Wasm Wasm.RustStd

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

/-! ## Run shape -/

/-- Everything publicly observable at the end of a finite execution. -/
structure RunOutcome where
  outcome : SmallStep.ObservableOutcome
  final : Universal.State

/-- The call returned normally and wrote exactly `output`. -/
def ReturnsOutput (run : RunOutcome) (output : List UInt8) : Prop :=
  run.outcome = .done [] ∧ run.final.stdio.output = output

/-- The call terminated with the allocator's distinguished OOM outcome. -/
def RanOutOfMemory (run : RunOutcome) : Prop :=
  run.outcome = .trapped (.host OOM.trapMessage) ∧ run.final.oom.raised = true

/-- Every finite terminal execution of the export `op` on `input` either
satisfies `post` or terminates with the allocator's distinguished OOM outcome.
This does not assert termination. -/
def PartiallyRuns (op : String) (input : List UInt8)
    (post : RunOutcome → Prop) : Prop :=
  PartiallyRunsWithOutcome (Universal.envFor «module») «module» op
    (Universal.State.ofInput input)
    (fun outcome final =>
      let run : RunOutcome := ⟨outcome, final⟩
      RanOutOfMemory run ∨ post run)

/-- The shared shape of all five contracts: a normal return writes exactly
`output`. -/
def WritesOrOOM (op : String) (input output : List UInt8) : Prop :=
  PartiallyRuns op input (fun run => ReturnsOutput run output)

/-! ## Expected output of each export -/

/-- `vec_len`: the element count as four little-endian bytes, truncated to 32
bits as the Rust `as u32` cast is. -/
def lenOutput (bytes : List UInt8) : List UInt8 :=
  WordCodec.encodeU32 (UInt32.ofNat (Vec.len bytes))

/-- `vec_pop`: the last element, nothing on empty input. -/
def popOutput (bytes : List UInt8) : List UInt8 :=
  (Vec.pop bytes).1.toList

/-- `vec_get`: byte 0 is an index into the remaining bytes; the element there,
nothing when the index is out of bounds or the input is empty. -/
def getOutput : List UInt8 → List UInt8
  | [] => []
  | index :: rest => (Vec.get rest index.toNat).toList

/-- `vec_contains`: byte 0 is the needle, the remaining bytes the haystack;
`1` when the needle occurs, `0` when it does not, nothing on empty input. -/
def containsOutput : List UInt8 → List UInt8
  | [] => []
  | needle :: rest => [if Vec.contains rest needle then 1 else 0]

/-- The wrapping 32-bit sum of a word list. -/
def sum32 (words : List UInt32) : UInt32 :=
  words.foldl (· + ·) 0

/-- `vec_sum32`: the wrapping sum of a length-prefixed word list, as four
little-endian bytes; nothing when the wire format rejects the input. -/
def sum32Output (bytes : List UInt8) : List UInt8 :=
  match Vec.deserialize WordCodec.u32le bytes with
  | none => []
  | some words => WordCodec.encodeU32 (sum32 words)

/-! ## Contracts -/

/-- `vec_len` writes the element count. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_len"]
def VecLenSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_len" bytes (lenOutput bytes)

/-- `vec_pop` writes the last element, and nothing on empty input. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_pop"]
def VecPopSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_pop" bytes (popOutput bytes)

/-- `vec_get` writes the element that byte 0 selects, and nothing when the
index is out of bounds.  The Rust source reads through `Vec::get`, so no index
panic is compiled into the module. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_get"]
def VecGetSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_get" bytes (getOutput bytes)

/-- `vec_contains` writes whether the needle in byte 0 occurs in the remaining
bytes, and nothing on empty input. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_contains"]
def VecContainsSpec : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "vec_contains" bytes (containsOutput bytes)

/-- `vec_sum32` writes the wrapping sum of a length-prefixed word list, and
nothing when the wire format rejects the input. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_sum32"]
def VecSum32Spec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_sum32" bytes (sum32Output bytes)

/-- `VecSum32Spec` read on well-formed input: a serialized word list is always
accepted, so the export writes the sum of exactly those words.  This is the
consumer of `Vec.deserialize_serialize`. -/
theorem sum32_on_serialized (words : List UInt32)
    (hbound : words.length < 2 ^ 32) :
    VecSum32Spec →
      WritesOrOOM "vec_sum32" (Vec.serialize WordCodec.u32le words)
        (WordCodec.encodeU32 (sum32 words)) := by
  intro h
  have hout : sum32Output (Vec.serialize WordCodec.u32le words)
      = WordCodec.encodeU32 (sum32 words) := by
    simp [sum32Output, Vec.deserialize_serialize WordCodec.u32le words hbound]
  have hrun := h (Vec.serialize WordCodec.u32le words)
  rwa [hout] at hrun

end Project.RustVec.Spec
