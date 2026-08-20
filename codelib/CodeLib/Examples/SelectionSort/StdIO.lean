import CodeLib.Examples.SelectionSort.TotalProof
import CodeLib.RustStd.MemArray
import Interpreter.Wasm.Host.StdIO
import Mathlib.Data.List.Sort

/-!
# Selection sort as a `StdIO` program

This is the stream-facing layer of the selection-sort tutorial. Input is a
packed sequence of little-endian unsigned 64-bit integers. The program calls
`stdio.read`, sorts the words in its one-page memory, and passes the same byte
region to `stdio.write`.

Both the recursive and loop implementations satisfy the same public contract:
for every input representable by the fixed page, there exists an output
returned by the program, and that output is a sorted permutation of the input.
The recursive proof will use induction; the loop proof will use invariants.
-/

namespace Wasm.Examples.SelectionSort.StdIO

open Wasm SepLogic SmallStep
open Iris Iris.Std

def bufferBytes : Nat := 65536
def array : UInt32 := 0

/-! ## Little-endian `UInt64` streams -/

/-- The eight little-endian bytes of an unsigned 64-bit word. -/
def encodeWord (value : UInt64) : List UInt8 :=
  [ (value &&& 0xff).toUInt8
  , ((value >>> 8) &&& 0xff).toUInt8
  , ((value >>> 16) &&& 0xff).toUInt8
  , ((value >>> 24) &&& 0xff).toUInt8
  , ((value >>> 32) &&& 0xff).toUInt8
  , ((value >>> 40) &&& 0xff).toUInt8
  , ((value >>> 48) &&& 0xff).toUInt8
  , ((value >>> 56) &&& 0xff).toUInt8 ]

/-- Reassemble an unsigned 64-bit word from its little-endian bytes. -/
def decodeWord (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : UInt8) : UInt64 :=
  b₀.toUInt64 ||| (b₁.toUInt64 <<< 8) |||
    (b₂.toUInt64 <<< 16) ||| (b₃.toUInt64 <<< 24) |||
    (b₄.toUInt64 <<< 32) ||| (b₅.toUInt64 <<< 40) |||
    (b₆.toUInt64 <<< 48) ||| (b₇.toUInt64 <<< 56)

def serialize (values : List UInt64) : List UInt8 :=
  values.flatMap encodeWord

/-- Reject a trailing partial word instead of silently ignoring it. -/
def deserialize : List UInt8 → Option (List UInt64)
  | [] => some []
  | b₀ :: b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: b₆ :: b₇ :: rest =>
      (deserialize rest).map (decodeWord b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ :: ·)
  | _ => none

@[simp] theorem decode_encode (value : UInt64) :
    decodeWord
      (value &&& 0xff).toUInt8
      (((value >>> 8) &&& 0xff).toUInt8)
      (((value >>> 16) &&& 0xff).toUInt8)
      (((value >>> 24) &&& 0xff).toUInt8)
      (((value >>> 32) &&& 0xff).toUInt8)
      (((value >>> 40) &&& 0xff).toUInt8)
      (((value >>> 48) &&& 0xff).toUInt8)
      (((value >>> 56) &&& 0xff).toUInt8) = value := by
  simp only [decodeWord]
  bv_decide

@[simp] theorem deserialize_serialize (values : List UInt64) :
    deserialize (serialize values) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [serialize, List.flatMap_cons, encodeWord, List.cons_append,
        List.nil_append, deserialize, decode_encode]
      change (deserialize (serialize values)).map (value :: ·) =
        some (value :: values)
      rw [ih]
      rfl

@[simp] theorem serialize_length (values : List UInt64) :
    (serialize values).length = 8 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change (List.flatMap encodeWord values).length = 8 * values.length at ih
      simp only [serialize, List.flatMap_cons, encodeWord, List.cons_append,
        List.nil_append, List.length_cons, Nat.mul_add]
      omega

/-! ## Link each sort against the `StdIO` ABI -/

/-- Read one page, require EOF, sort `byteLength / 8` words, and write them.
The unified indices are `0 = read`, `1 = write`, followed by the supplied sort
functions and finally `main`. -/
def mainBody (sortIndex : Nat) : Program :=
  [ .const (UInt32.ofNat bufferBytes), .const array, .call 0, .localSet 0
  , .const 1, .const (UInt32.ofNat bufferBytes), .call 0, .localSet 1
  , .const array, .localGet 0, .const 8, .divU, .call sortIndex
  , .localGet 0, .const array, .call 1
  , .ret ]

def mainFunction (sortIndex : Nat) : Function :=
  { locals := [.i32, .i32]
    body := mainBody sortIndex }

structure Executable where
  module : Module
  entry : Nat
  sortEntry : Nat
  imports_eq : module.imports = Wasm.StdIO.imports
  memory_pages :
    (module.initialStore (α := Wasm.StdIO.State)).mem.pages = 1
  extraMemories_empty : module.extraMemories = []

def recursive : Executable :=
  { module :=
      { imports := Wasm.StdIO.imports
        funcs :=
          [ findMinRecursiveFunction 2
          , recursiveSelectionSortFunction 2 3
          , mainFunction 3 ]
        memory := some { pagesMin := 1, pagesMax := some 1 } }
    entry := 4
    sortEntry := 3
    imports_eq := rfl
    memory_pages := rfl
    extraMemories_empty := rfl }

def loop : Executable :=
  { module :=
      { imports := Wasm.StdIO.imports
        funcs := [loopSelectionSortFunction, mainFunction 2]
        memory := some { pagesMin := 1, pagesMax := some 1 } }
    entry := 3
    sortEntry := 2
    imports_eq := rfl
    memory_pages := rfl
    extraMemories_empty := rfl }

def initialStore (program : Executable) (input : List UInt8) :
    Store Wasm.StdIO.State :=
  { (program.module.initialStore (α := Wasm.StdIO.State)) with
      host := Wasm.StdIO.State.ofInput input }

def execute (program : Executable) (fuel entry : Nat)
    (store : Store Wasm.StdIO.State) (args : List Value) :
    Option (List Value × Store Wasm.StdIO.State) :=
  match SmallStep.initConfig
      { module := program.module, host := Wasm.StdIO.env } entry store args with
  | .error _ => none
  | .ok phase =>
      match (SmallStep.runSteps fuel phase).result with
      | .success values finalStore => some (values, finalStore.wasm)
      | _ => none

def replaceHost (store : Store α) (host : β) : Store β :=
  { store with host := host }

/-- The host-independent call configuration shared by the executable runner
and the Iris proof. Keeping the explicit `.call` exposes exactly the public
function contract proved in `TotalProof`. -/
def sortConfig (program : Executable) (store : Store Wasm.StdIO.State)
    (args : List Value) : Config Unit :=
  { expr := .running
      ⟨⟨[], [], args⟩, [.call program.sortEntry], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := program.module, host := ({} : HostEnv Unit) }], entry := ⟨0⟩ }
        wasm := replaceHost store () } }

/-- The sort functions cannot call an import. Running them with an inert host
makes that independence explicit, after which the unchanged StdIO buffers are
reattached. -/
def executeSort (program : Executable) (fuel : Nat)
    (store : Store Wasm.StdIO.State) (args : List Value) :
    Option (List Value × Store Wasm.StdIO.State) :=
  match (SmallStep.runSteps fuel (sortConfig program store args)).result with
  | .success values finalStore =>
      some (values, replaceHost finalStore.wasm store.host)
  | _ => none

def writtenStore (store : Store Wasm.StdIO.State) (length : UInt32) :
    Store Wasm.StdIO.State :=
  { store with
    host :=
      { input := store.host.input
        output := store.host.output ++
          store.mem.readBytes array.toNat length.toNat } }

def runAfterRead (program : Executable) (fuel : Nat)
    (byteLength : UInt32) (afterRead : Store Wasm.StdIO.State) :
    Option (List UInt8) := do
  let (probeValues, afterProbe) ← execute program 2 0 afterRead
    [.i32 (UInt32.ofNat 65536), .i32 1]
  guard (probeValues = [.i32 0])
  let (_, afterSort) ← executeSort program fuel afterProbe
    [.i32 (UInt32.ofNat (byteLength.toNat / 8)), .i32 array]
  let (_, afterWrite) ← execute program 2 1 afterSort
    [.i32 array, .i32 byteLength]
  pure afterWrite.host.output

/-- Execute `read`, an EOF probe, the selected sort, and `write` as explicit
small-step phases. This is the same style as the merge-sort StdIO tutorial and
keeps the host-independent sort proof reusable. -/
def run (program : Executable) (fuel : Nat)
    (input : List UInt8) : Option (List UInt8) := do
  let (readValues, afterRead) ← execute program 2 0
    (initialStore program input)
    [.i32 array, .i32 (UInt32.ofNat bufferBytes)]
  let byteLength ← match readValues with
    | [.i32 length] => some length
    | _ => none
  runAfterRead program fuel byteLength afterRead

def runValues (program : Executable) (fuel : Nat)
    (input : List UInt64) : Option (List UInt64) :=
  (run program fuel (serialize input)).bind deserialize

/-! ## Shared public correctness statement -/

def Sorted (values : List UInt64) : Prop :=
  values.Pairwise (· ≤ ·)

def Fits (input : List UInt64) : Prop :=
  (serialize input).length ≤ bufferBytes

def RunsValues (program : Executable)
    (input output : List UInt64) : Prop :=
  ∃ fuel, runValues program fuel input = some output

/-- For every representable input there exists an output returned by the
program, and the output is exactly a sorted permutation of the input. -/
def Correct (program : Executable) : Prop :=
  ∀ input, Fits input →
    ∃ output,
      RunsValues program input output ∧
      List.Perm input output ∧
      Sorted output

/-- Correctness theorem proved by induction in `StdIOProof`. -/
def RecursiveCorrect : Prop := Correct recursive

/-- Correctness theorem proved with loop invariants in `StdIOProof`. -/
def LoopCorrect : Prop := Correct loop

/-! ## Executable smoke checks

These checks exercise the complete `read → sort → write` path. They are not
the tutorial's correctness proofs. The value above `UInt32.size` ensures the
program is genuinely sorting unsigned 64-bit words rather than 32-bit ones.
-/

theorem recursive_exec_u64 :
    runValues recursive 5000 [5, 1, 0x100000000, 2, 3] =
      some [1, 2, 3, 5, 0x100000000] := by
  native_decide

theorem loop_exec_u64 :
    runValues loop 5000 [5, 1, 0x100000000, 2, 3] =
      some [1, 2, 3, 5, 0x100000000] := by
  native_decide

end Wasm.Examples.SelectionSort.StdIO
