import Project.RustVec.Program
import Interpreter.Wasm.Host.Universal
import CodeLib.RustStd.Vec.Basic
import CodeLib.RustStd.Vec.Codec

/-!
# Specification for `rust_vec`

Five exports, one `Vec` access pattern each.  Every export reads the whole
standard input into a `Vec<u8>` and writes its result to standard output, so
each contract is stated against the pure `List` model in
`CodeLib.RustStd.Vec.Basic` and the wire format in `CodeLib.RustStd.Vec.Codec`.

The contracts are partial, not total.  `read_all` allocates in proportion to
the input, so an allocation failure is a reachable terminal outcome for every
one of these exports; the `talos.oom` host trap is therefore admitted as an
alternative to a correct write.  Fuel, linear memory, and allocator state stay
hidden.
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

/-- The shared shape of all five contracts: on `input`, every finite terminal
execution of `op` either returns no Wasm values after writing exactly `output`,
or reaches the allocator's `talos.oom` trap with the typed OOM marker set.
This states no termination claim. -/
def WritesOrOOM (op : String) (input output : List UInt8) : Prop :=
  PartiallyRunsWithOutcome (Universal.envFor «module») «module» op
    (Universal.State.ofInput input)
    (fun outcome final =>
      match outcome with
      | .done values => values = [] ∧ final.stdio.output = output
      | .trapped reason =>
          reason = .host OOM.trapMessage ∧ final.oom.raised = true)

/-- `vec_len` writes the element count as four little-endian bytes.  The count
is truncated to 32 bits, matching the Rust `as u32` cast. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_len"]
def LenSpecification : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "vec_len" bytes (Vec.encodeU32 (UInt32.ofNat (Vec.len bytes)))

/-- `vec_pop` writes the last element, and writes nothing on empty input. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_pop"]
def PopSpecification : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "vec_pop" bytes
      (match (Vec.pop bytes).1 with
        | none => []
        | some byte => [byte])

/-- `vec_get` reads an index from byte 0 and writes the element at that index
of the remaining bytes.  An out-of-bounds index writes nothing: the Rust code
goes through `get`, so no index panic, and therefore no trap, is reachable
from a bad index. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_get"]
def GetSpecification : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "vec_get" bytes
      (match bytes with
        | [] => []
        | index :: rest =>
            match Vec.get rest index.toNat with
            | none => []
            | some byte => [byte])

/-- `vec_contains` reads a needle from byte 0 and writes `1` when the needle
occurs in the remaining bytes, `0` when it does not. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_contains"]
def ContainsSpecification : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "vec_contains" bytes
      (match bytes with
        | [] => []
        | needle :: rest => [if Vec.contains rest needle then 1 else 0])

/-- The wrapping 32-bit sum of a word list. -/
def sum32 (words : List UInt32) : UInt32 :=
  words.foldl (· + ·) 0

/-- `vec_sum32` parses a length-prefixed list of little-endian words and writes
their wrapping sum.  Input that the wire format rejects writes nothing. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_sum32"]
def Sum32Specification : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "vec_sum32" bytes
      (match Vec.deserialize Vec.u32le bytes with
        | none => []
        | some words => Vec.encodeU32 (sum32 words))

/-- The reading of `Sum32Specification` on well-formed input: a serialized word
list is always accepted, so the export writes the sum of exactly those words.
This is the consumer of `Vec.deserialize_serialize`. -/
theorem sum32_on_serialized (words : List UInt32) (hbound : words.length < 2 ^ 32) :
    Sum32Specification →
      WritesOrOOM "vec_sum32" (Vec.serialize Vec.u32le words)
        (Vec.encodeU32 (sum32 words)) := by
  intro h
  have hrun := h (Vec.serialize Vec.u32le words)
  rwa [Vec.deserialize_serialize Vec.u32le words hbound] at hrun

/-- Distinct word lists start distinct runs, so `sum32_on_serialized` assigns
one sum to each starting state.  This is the consumer of `Vec.serialize_inj`. -/
theorem sum32_input_determined {words words' : List UInt32}
    (hbound : words.length < 2 ^ 32) (hbound' : words'.length < 2 ^ 32)
    (h : Universal.State.ofInput (Vec.serialize Vec.u32le words)
          = Universal.State.ofInput (Vec.serialize Vec.u32le words')) :
    words = words' :=
  Vec.serialize_inj Vec.u32le hbound hbound'
    (congrArg (fun state => state.stdio.input) h)

end Project.RustVec.Spec
