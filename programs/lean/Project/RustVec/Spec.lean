import Project.RustVec.Program
import Interpreter.Wasm.Host.Universal
import CodeLib.RustStd.Borsh

/-!
# Specification for `rust_vec`

Six exports, one `Vec` access pattern each.  The interface is functional:
every export reads one borsh value from standard input, applies one operation,
and writes one borsh value back.  An export that changes the vector writes the
changed vector, an export that also produces an element writes the element
beside the remaining vector, and an export that only observes writes the
observation alone.  Each contract is therefore stated against the pure `List`
model in `CodeLib.RustStd.Vec.Basic` and the layouts in
`CodeLib.RustStd.Borsh`.

`borsh::from_slice` rejects trailing bytes, so an input is accepted only when
it is exactly one encoded value.  Every rejection writes nothing.  A `None`
result writes its tag byte `[0]`, so a rejected input and a `None` result stay
distinguishable.  The encode step cannot fail: an allocation failure raises
`talos.oom` rather than an `Err`.

The contracts are partial, not total.  `read_all` and the decoder both
allocate in proportion to the input, so an allocation failure is a reachable
terminal outcome for every one of these exports; the `talos.oom` host trap is
therefore admitted as an alternative to a correct write, in the shape
`Project.Mergesort.Spec` uses.  Fuel, linear memory, and allocator state stay
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

/-- The shared shape of all six contracts: a normal return writes exactly
`output`. -/
def WritesOrOOM (op : String) (input output : List UInt8) : Prop :=
  PartiallyRuns op input (fun run => ReturnsOutput run output)

/-! ## Reading the input -/

/-- The vector the export decodes, or `none` when borsh rejects the bytes: a
header shorter than four bytes, a payload with a trailing partial word, or an
element count that disagrees with the header. -/
def vecOf (bytes : List UInt8) : Option (List UInt32) :=
  Borsh.vec? WordCodec.u32le bytes

/-- Input shaped `word ++ vec`, as `vec_push`, `vec_get` and `vec_contains`
read it.  A borsh tuple has no framing, so the word is simply the first four
bytes. -/
def wordAndVec (bytes : List UInt8) : Option (UInt32 × List UInt32) :=
  if bytes.length < 4 then none
  else (vecOf (bytes.drop 4)).map fun values =>
    (WordCodec.decodeU32 (bytes.take 4), values)

/-! ## Expected output of each export -/

/-- `vec_len`: the element count as a borsh `u32`; nothing when the input is
rejected.  The header already bounds the count below `2 ^ 32`, so the Rust
`as u32` cast is exact. -/
def lenOutput (bytes : List UInt8) : List UInt8 :=
  match vecOf bytes with
  | none => []
  | some values => Borsh.u32 (UInt32.ofNat (Vec.len values))

/-- `vec_push`: the vector with the leading word appended. -/
def pushOutput (bytes : List UInt8) : List UInt8 :=
  match wordAndVec bytes with
  | none => []
  | some (value, values) =>
      Borsh.vec WordCodec.u32le (Vec.push values value)

/-- `vec_pop`: the removed element beside the remaining vector, as a borsh
tuple.  On an empty vector the element is `None`, so the output is the `None`
tag followed by the empty vector, not nothing at all. -/
def popOutput (bytes : List UInt8) : List UInt8 :=
  match vecOf bytes with
  | none => []
  | some values =>
      let (element, rest) := Vec.pop values
      Borsh.option Borsh.u32 element ++ Borsh.vec WordCodec.u32le rest

/-- `vec_get`: the element under the leading index, as a borsh `Option`. -/
def getOutput (bytes : List UInt8) : List UInt8 :=
  match wordAndVec bytes with
  | none => []
  | some (index, values) =>
      Borsh.option Borsh.u32 (Vec.get values index.toNat)

/-- `vec_contains`: whether the leading word occurs, as a borsh `bool`. -/
def containsOutput (bytes : List UInt8) : List UInt8 :=
  match wordAndVec bytes with
  | none => []
  | some (needle, values) => Borsh.bool (Vec.contains values needle)

/-- The wrapping 32-bit sum of a word list. -/
def sum32 (words : List UInt32) : UInt32 :=
  words.foldl (· + ·) 0

/-- `vec_sum32`: the wrapping sum of every element, as a borsh `u32`. -/
def sum32Output (bytes : List UInt8) : List UInt8 :=
  match vecOf bytes with
  | none => []
  | some words => Borsh.u32 (sum32 words)

/-! ## Contracts -/

/-- `vec_len` writes the element count. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_len"]
def VecLenSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_len" bytes (lenOutput bytes)

/-- `vec_push` writes the vector with the leading word appended. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_push"]
def VecPushSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_push" bytes (pushOutput bytes)

/-- `vec_pop` writes the removed element beside the remaining vector. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_pop"]
def VecPopSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_pop" bytes (popOutput bytes)

/-- `vec_get` writes the element that the leading index selects, and `None`
when the index is out of bounds.  The Rust source reads through `Vec::get`, so
no index panic is compiled into the module. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_get"]
def VecGetSpec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_get" bytes (getOutput bytes)

/-- `vec_contains` writes whether the leading word occurs in the vector. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_contains"]
def VecContainsSpec : Prop :=
  ∀ bytes : List UInt8,
    WritesOrOOM "vec_contains" bytes (containsOutput bytes)

/-- `vec_sum32` writes the wrapping sum of every element. -/
@[spec_of "rust-exported-partial" "rust_vec::vec_sum32"]
def VecSum32Spec : Prop :=
  ∀ bytes : List UInt8, WritesOrOOM "vec_sum32" bytes (sum32Output bytes)

/-- Every name the contracts mention starts a call on the generated module.
A misspelt name would make its contract false, not vacuous:
`PartiallyRunsWithOutcome` needs a start configuration. -/
theorem contract_names_start :
    ["vec_len", "vec_push", "vec_pop", "vec_get", "vec_contains", "vec_sum32"].all
      (fun op =>
        (startCallConfig? (Universal.envFor «module») «module» op
          (Universal.State.ofInput [])).isSome) = true := by
  native_decide

/-! ## Reading the contracts

Each contract quantifies over raw bytes.  The theorems below read them on
well-formed input, where `Borsh.vec?_vec` turns the byte-level statement into
one about the `List` model.  Together they exercise both readers (`vecOf` and
`wordAndVec`), the decode direction of `Borsh.u32`, both `Option` tags, and
the `Vec` operations `push`, `get` and `pop`. -/

/-- `VecSum32Spec` read on well-formed input: an encoded word list is always
accepted, so the export writes the sum of exactly those words. -/
theorem sum32_on_serialized (words : List UInt32)
    (hbound : words.length < 2 ^ 32) :
    VecSum32Spec →
      WritesOrOOM "vec_sum32" (Borsh.vec WordCodec.u32le words)
        (Borsh.u32 (sum32 words)) := by
  intro h
  have hout : sum32Output (Borsh.vec WordCodec.u32le words)
      = Borsh.u32 (sum32 words) := by
    simp [sum32Output, vecOf, Borsh.vec?_vec WordCodec.u32le words hbound]
  have hrun := h (Borsh.vec WordCodec.u32le words)
  rwa [hout] at hrun

/-- `VecPushSpec` read on well-formed input: a word in front of an encoded
vector is accepted as the tuple `(u32, Vec<u32>)`, and the export writes the
vector with that word appended.  This is the theorem that goes through
`wordAndVec`, the one hand-written reader. -/
theorem push_on_serialized (value : UInt32) (values : List UInt32)
    (hbound : values.length < 2 ^ 32) :
    VecPushSpec →
      WritesOrOOM "vec_push" (Borsh.u32 value ++ Borsh.vec WordCodec.u32le values)
        (Borsh.vec WordCodec.u32le (Vec.push values value)) := by
  intro h
  have hlen : (Borsh.u32 value).length = 4 := WordCodec.u32le_encode_length value
  have hnot : ¬ (Borsh.u32 value ++ Borsh.vec WordCodec.u32le values).length < 4 := by
    rw [List.length_append, hlen]
    omega
  have htake : (Borsh.u32 value ++ Borsh.vec WordCodec.u32le values).take 4
      = Borsh.u32 value :=
    List.take_left' hlen
  have hdrop : (Borsh.u32 value ++ Borsh.vec WordCodec.u32le values).drop 4
      = Borsh.vec WordCodec.u32le values :=
    List.drop_left' hlen
  have hword : WordCodec.decodeU32 (Borsh.u32 value) = value :=
    WordCodec.u32le.decode_encode value
  have hout : pushOutput (Borsh.u32 value ++ Borsh.vec WordCodec.u32le values)
      = Borsh.vec WordCodec.u32le (Vec.push values value) := by
    unfold pushOutput wordAndVec
    rw [if_neg hnot, hdrop, htake, hword, vecOf,
      Borsh.vec?_vec WordCodec.u32le values hbound]
    simp
  have hrun := h (Borsh.u32 value ++ Borsh.vec WordCodec.u32le values)
  rwa [hout] at hrun

/-- `VecGetSpec` read on well-formed input: an index in front of an encoded
vector is accepted as the tuple `(u32, Vec<u32>)`, and the export writes the
element under that index as a borsh `Option`, `None` when the index is out of
bounds.  The Rust `index as usize` is exact on wasm32, which is why the model
reads `index.toNat`. -/
theorem get_on_serialized (index : UInt32) (values : List UInt32)
    (hbound : values.length < 2 ^ 32) :
    VecGetSpec →
      WritesOrOOM "vec_get" (Borsh.u32 index ++ Borsh.vec WordCodec.u32le values)
        (Borsh.option Borsh.u32 (Vec.get values index.toNat)) := by
  intro h
  have hlen : (Borsh.u32 index).length = 4 := WordCodec.u32le_encode_length index
  have hnot : ¬ (Borsh.u32 index ++ Borsh.vec WordCodec.u32le values).length < 4 := by
    rw [List.length_append, hlen]
    omega
  have htake : (Borsh.u32 index ++ Borsh.vec WordCodec.u32le values).take 4
      = Borsh.u32 index :=
    List.take_left' hlen
  have hdrop : (Borsh.u32 index ++ Borsh.vec WordCodec.u32le values).drop 4
      = Borsh.vec WordCodec.u32le values :=
    List.drop_left' hlen
  have hword : WordCodec.decodeU32 (Borsh.u32 index) = index :=
    WordCodec.u32le.decode_encode index
  have hout : getOutput (Borsh.u32 index ++ Borsh.vec WordCodec.u32le values)
      = Borsh.option Borsh.u32 (Vec.get values index.toNat) := by
    unfold getOutput wordAndVec
    rw [if_neg hnot, hdrop, htake, hword, vecOf,
      Borsh.vec?_vec WordCodec.u32le values hbound]
    simp
  have hrun := h (Borsh.u32 index ++ Borsh.vec WordCodec.u32le values)
  rwa [hout] at hrun

/-- `VecPopSpec` read on well-formed input.  On a non-empty vector the export
writes the `Some` tag, the last element, and the vector without it; the two
halves of that output are what makes the contract functional rather than a
bare element. -/
theorem pop_on_serialized (values : List UInt32) (last : UInt32)
    (hbound : values.length + 1 < 2 ^ 32) :
    VecPopSpec →
      WritesOrOOM "vec_pop" (Borsh.vec WordCodec.u32le (values ++ [last]))
        (Borsh.option Borsh.u32 (some last) ++ Borsh.vec WordCodec.u32le values) := by
  intro h
  have hout : popOutput (Borsh.vec WordCodec.u32le (values ++ [last]))
      = Borsh.option Borsh.u32 (some last) ++ Borsh.vec WordCodec.u32le values := by
    simp [popOutput, vecOf,
      Borsh.vec?_vec WordCodec.u32le (values ++ [last]) (by simpa using hbound),
      Vec.pop]
  have hrun := h (Borsh.vec WordCodec.u32le (values ++ [last]))
  rwa [hout] at hrun

/-- `VecPopSpec` read on the empty vector: the export writes the `None` tag
and then the empty vector, so an empty result is still an output and not a
rejection. -/
theorem pop_on_empty :
    VecPopSpec →
      WritesOrOOM "vec_pop" (Borsh.vec WordCodec.u32le [])
        (Borsh.option Borsh.u32 none ++ Borsh.vec WordCodec.u32le []) := by
  intro h
  have hout : popOutput (Borsh.vec WordCodec.u32le [])
      = Borsh.option Borsh.u32 none ++ Borsh.vec WordCodec.u32le [] := by
    simp [popOutput, vecOf, Borsh.vec?_vec WordCodec.u32le [] (by simp),
      Vec.pop]
  have hrun := h (Borsh.vec WordCodec.u32le [])
  rwa [hout] at hrun

end Project.RustVec.Spec
