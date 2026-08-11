import CodeLib.Examples.MergeSort.TotalProof
import Interpreter.Wasm.Host.StdIO

/-!
# Merge sort as a `StdIO` program

This layer turns the memory-oriented merge-sort implementation into a small
byte-stream program.  Its input and output format is a packed sequence of
little-endian `UInt32` values.  The entry point reads the input into the first
half of its one-page memory, uses the second half as scratch space, sorts the
words, and writes the sorted first half to the append-only output stream.
-/

namespace Wasm.Examples.MergeSort.StdIO

open Wasm SmallStep

/-- Each of the source and scratch arrays owns half of the 64-KiB page. -/
def bufferBytes : Nat := 32768

def source : UInt32 := 0
def scratch : UInt32 := UInt32.ofNat bufferBytes

/-- The four little-endian bytes of a 32-bit word. -/
def encodeWord (value : UInt32) : List UInt8 :=
  [ (value &&& 0xff).toUInt8
  , ((value >>> 8) &&& 0xff).toUInt8
  , ((value >>> 16) &&& 0xff).toUInt8
  , ((value >>> 24) &&& 0xff).toUInt8 ]

/-- Reassemble a 32-bit word from its four little-endian bytes. -/
def decodeWord (b₀ b₁ b₂ b₃ : UInt8) : UInt32 :=
  b₀.toUInt32 ||| (b₁.toUInt32 <<< 8) |||
    (b₂.toUInt32 <<< 16) ||| (b₃.toUInt32 <<< 24)

/-- Packed little-endian serialization of a list of 32-bit words. -/
def serialize (values : List UInt32) : List UInt8 :=
  values.flatMap encodeWord

/-- Decode a packed little-endian byte sequence. A trailing partial word is
rejected rather than silently ignored. -/
def deserialize : List UInt8 → Option (List UInt32)
  | [] => some []
  | b₀ :: b₁ :: b₂ :: b₃ :: rest =>
      (deserialize rest).map (decodeWord b₀ b₁ b₂ b₃ :: ·)
  | _ => none

@[simp] theorem decode_encode (value : UInt32) :
    decodeWord
      (value &&& 0xff).toUInt8
      (((value >>> 8) &&& 0xff).toUInt8)
      (((value >>> 16) &&& 0xff).toUInt8)
      (((value >>> 24) &&& 0xff).toUInt8) = value := by
  simp only [decodeWord]
  bv_decide

@[simp] theorem deserialize_serialize (values : List UInt32) :
    deserialize (serialize values) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [serialize, List.flatMap_cons, encodeWord, List.cons_append,
        List.nil_append, deserialize, decode_encode]
      change (deserialize (serialize values)).map (value :: ·) = some (value :: values)
      rw [ih]
      rfl

@[simp] theorem serialize_length (values : List UInt32) :
    (serialize values).length = 4 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change (List.flatMap encodeWord values).length = 4 * values.length at ih
      simp only [serialize, List.flatMap_cons, encodeWord, List.cons_append,
        List.nil_append, List.length_cons, Nat.mul_add]
      omega

/-- The stream-facing wrapper.  Local `0` remembers the byte count returned
by `read`; dividing it by four gives the number of words passed to merge sort.

Unified function indices are: `0 = read`, `1 = write`, `2 = mergeSort`,
`3 = merge`, and `4 = main`. -/
def mainBody : Program :=
  [ .const (UInt32.ofNat bufferBytes), .const source, .call 0, .localSet 0
  , .const source, .const scratch, .localGet 0, .const 4, .divU, .call 2
  , .localGet 0, .const source, .call 1
  , .ret ]

def mainFunction : Function :=
  { locals := [.i32]
    body := mainBody }

/-- Merge sort linked against the two-function `StdIO` ABI. -/
def module : Module :=
  { imports := Wasm.StdIO.imports
    funcs := [mergeSortFunction 3, mergeFunction, mainFunction]
    memory := some { pagesMin := 1, pagesMax := some 1 } }

def initialStore (input : List UInt8) : Store Wasm.StdIO.State :=
  { (module.initialStore (α := Wasm.StdIO.State)) with
      host := Wasm.StdIO.State.ofInput input }

def config (input : List UInt8) : Config Wasm.StdIO.State :=
  match SmallStep.initConfig
      { module, host := Wasm.StdIO.env } 4 (initialStore input) [] with
  | .ok result => result
  | .error _ =>
      -- Definitionally unreachable: local function index 4 is `mainFunction`.
      { expr := .trapped (.host "invalid StdIO merge-sort entry")
        store :=
          { runtime := { module, host := Wasm.StdIO.env }
            wasm := initialStore input } }

/-- Execute the authoritative small-step machine and project the host output. -/
def run (fuel : Nat) (input : List UInt8) : Option (List UInt8) :=
  match (SmallStep.runSteps fuel (config input)).result with
  | .success _ store => some store.wasm.host.output
  | _ => none

/-- A clean, host-level execution predicate.  Fuel is hidden existentially
and neither linear memory nor Wasm machine state appears in client specs. -/
def Runs (input output : List UInt8) : Prop :=
  ∃ fuel, run fuel input = some output

/-- Serialize the input, run the byte-stream program, and deserialize its
output.  This is the convenient executable surface for clients. -/
def runValues (fuel : Nat) (input : List UInt32) : Option (List UInt32) :=
  (run fuel (serialize input)).bind deserialize

/-- Fuel-free execution phrased entirely in terms of lists of words. -/
def RunsValues (input output : List UInt32) : Prop :=
  ∃ fuel, runValues fuel input = some output

/-- Pure input-side condition imposed by the fixed one-page Wasm32 layout. -/
def Fits (values : List UInt32) : Prop :=
  (serialize values).length ≤ bufferBytes

/-- Every value-level result successfully produced by the program is a sorted
permutation of its input.  This safety statement is independent of Wasm's
finite-memory resource limit. -/
def Correct : Prop :=
  ∀ input output,
    RunsValues input output → SortedPermutation input output

/-- Every input that fits the current fixed layout successfully produces an
output.  Keeping resource-bounded termination separate leaves `Correct` clean. -/
def Complete : Prop :=
  ∀ input, Fits input →
    ∃ output, RunsValues input output

theorem exec_empty : run 100 (serialize []) = some (serialize []) := by
  native_decide

theorem exec_five :
    run 12000 (serialize [5, 1, 4, 2, 3]) =
      some (serialize [1, 2, 3, 4, 5]) := by
  native_decide

theorem exec_duplicates :
    run 15000 (serialize [4, 1, 4, 2, 1, 3]) =
      some (serialize [1, 1, 2, 3, 4, 4]) := by
  native_decide

theorem exec_values_five :
    runValues 12000 [5, 1, 4, 2, 3] = some [1, 2, 3, 4, 5] := by
  native_decide

end Wasm.Examples.MergeSort.StdIO
