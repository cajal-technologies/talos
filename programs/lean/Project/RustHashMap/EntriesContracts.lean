import Project.RustHashMap.SortContracts
import Project.RustHashMap.GrowContract
import CodeLib.RustStd.HashMap.ProbeWasm
import CodeLib.RustStd.HashMap.OptionOut
import CodeLib.RustStd.HashMap.Codec
import CodeLib.RustStd.Borsh

/-!
# The contracts of `sorted_entries` and the reply writer

The three map drivers that answer with a whole map end the same way.
They call absolute `func 7`, `sorted_entries`, which reads the table and
builds a `Vec<(u32, u32)>` in key order, and then absolute `func 8`, the
reply writer, which serializes an `Option<u32>` and that vector and
writes the bytes to the output stream.

This module states one contract for each.  Nothing is proved here.

## The pair vector

`sorted_entries` answers with the three words of a `Vec` header: the
capacity, the buffer pointer and the entry count.  `PairVecAt` is the
ownership of the buffer that the header names.  An empty vector allocates
nothing; `RawVec::NEW` reports the capacity 0 and the dangling pointer 4,
which WAT 1290 to 1294 writes as the single `i64` constant
17179869184.

## The stack constants

Absolute `func 7` commits a 16-byte frame at WAT 1024 to 1027 and calls
absolute `func 14`, the sort, absolute `func 13`, the grow, and absolute
`func 58`, the allocator.  The sort is the deepest of the three, so
`sortedEntriesDepth` is the frame plus `SortContracts.sortDepth`.

`serializeDepth` is the largest value that `sortedEntriesDepth` takes.  A
table holds at most `2 ^ 27` buckets, so the sort limit is at most 54 and
the sort takes at most 55 quicksort frames.

Absolute `func 8` commits a 16-byte frame at WAT 1302 to 1305 and calls
absolute `func 13`, the grow, absolute `func 64`, the write shim, and
absolute `func 58`, the allocator.  The write shim holds no
`global.get 0` and forwards to import 1, so `writeDepth` is zero and the
grow is the deepest call.

## The dead arms

X-F7-CAP of `Analysis/scope-and-exclusions.md` is the `call 99` and
`unreachable` at WAT 1285 behind the two capacity guards at WAT 1084 to
1091.  `t.buckets <= 2 ^ 27` kills it, because the capacity is at most
`max t.items 4` and `t.items` is below the bucket count.

X-F7-GROW is the `call 13` at WAT 1215 behind the guard at WAT 1203 to
1207, which compares the loop index with the capacity.  The capacity is
`max t.items 4`, which is never below the number of entries the loop
writes, so the guard is false at every step and the grow never runs.

X-F8-NULL is the `call 99` and `unreachable` at WAT 1473 behind the guard
at WAT 1316 to 1320.  `Func55Spec` returns a nonzero pointer, so the
guard is false.
-/

namespace Project.RustHashMap.EntriesContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.PairGrow
open Project.RustHashMap.SortContracts
open Project.RustHashMap.GrowContract
open scoped Wasm.SmallStep.Outcome

/-! ## The pair vector -/

/-- The buffer that a `Vec<(u32, u32)>` header names.  The capacity 0 is
the vector that allocated nothing: `RawVec::NEW` holds the dangling
pointer 4 and no entry.  A positive capacity is one live block of
`pairBlock cap`, whose first `8 * pairs.length` bytes are the entries and
whose rest is spare. -/
def PairVecAt [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId capacity : Nat) (ptr : UInt32)
    (pairs : List (UInt32 × UInt32)) : HeapIProp :=
  if capacity = 0 then iprop(⌜ptr = 4 ∧ pairs = []⌝)
  else iprop(∃ pad : List UInt8,
    ⌜(HashMap.Table.pairBytes pairs ++ pad).length = 8 * capacity⌝ ∗
    LiveBlock heapId allocationId ptr (pairBlock capacity)
      (HashMap.Table.pairBytes pairs ++ pad))

/-! ## The stack constants -/

/-- The stack that absolute `func 7` takes below its caller: its own
16-byte frame and the sort of `items` entries. -/
def sortedEntriesDepth (items : Nat) : Nat := 16 + sortDepth items

/-- The largest stack that absolute `func 7` takes.  A table holds at
most `2 ^ 27` buckets, so the sort takes at most 55 quicksort frames of
256 bytes each. -/
def serializeDepth : Nat := 14096

theorem serializeDepth_eq : serializeDepth = 16 + 256 * 55 := rfl

theorem sortedEntriesDepth_le_serialize {items : Nat}
    (hitems : items ≤ 2 ^ 27) : sortedEntriesDepth items ≤ serializeDepth := by
  have hsort := sortDepth_le hitems
  unfold sortedEntriesDepth serializeDepth
  omega

/-- The stack that the write shim, absolute `func 64`, takes below its
caller.  The shim holds no `global.get 0` and forwards to import 1, so
the answer is zero.  `Project.RustHashMap.Contracts.Func61Spec` takes no
stack resource for the same reason. -/
def writeDepth : Nat := 0

/-- The stack that absolute `func 8` takes below its caller: its own
16-byte frame and the deepest of the grow and the write. -/
def replyDepth : Nat := 16 + max growDepth writeDepth

theorem replyDepth_eq : replyDepth = 32 := rfl

/-! ## `sorted_entries`, absolute `func 7` -/

/-- Absolute `func 7`, local `func4`, WAT 1022 to 1299.  The two
arguments in source order are the 12-byte output slot and the map value,
so local 0 is the slot and local 1 is the map.

The body walks the control bytes of the table, copies each live bucket
into a fresh buffer, and sorts the buffer by key with `call 14` when it
holds 21 entries or more and with `call 15` otherwise.  The answer is the
three-word header of that buffer.

The capacity is `max items 4` for a table with entries and 0 for an empty
one, which WAT 1073 to 1080 computes and which the continuation reports.

The body writes no stream.  It reads the map and gives it back unchanged.
The final cursor, frontier and history stay existential, because the
empty arm allocates nothing while the other arm allocates one block. -/
def Func4Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out map : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 7 [.i32 map, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp (sortedEntriesDepth t.items) below ∗
        Slices.ByteSlice 0 out outBefore ∗
        HashMap.Table.HashMapAt 0 map k0 k1 t ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 12 ∧
          HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t ∧
          t.buckets ≤ 2 ^ 27 ∧
          out.toNat + 12 < UInt32.size ∧
          map.toNat + 32 < UInt32.size ∧
          sortedEntriesDepth t.items ≤ sp.toNat⌝ ∗
        (-- the normal arm
         (∀ capacity : UInt32, ∀ ptr : UInt32, ∀ allocationId : Nat,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp (sortedEntriesDepth t.items) below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize
                [capacity, ptr, UInt32.ofNat t.items]) -∗
            HashMap.Table.HashMapAt 0 map k0 k1 t -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            PairVecAt heapId allocationId capacity.toNat ptr
              (HashMap.sortByKey (HashMap.Table.toList t)) -∗
            Streams input output raised -∗
            ⌜capacity.toNat =
              if t.items = 0 then 0 else max t.items 4⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## The reply writer, absolute `func 8` -/

/-- Absolute `func 8`, local `func5`, WAT 1300 to 1491.  The one argument
is a 20-byte record: the `Option<u32>` answer at offset 0, and the three
words of the pair vector header at offsets 8, 12 and 16.  The body never
reads the capacity word at offset 8; it reads the pointer at offset 12
and the count at offset 16.

The body allocates a 1024-byte buffer with `call 58`, writes the borsh
form of the option, then the entry count, then each entry as the key word
and the value word, and grows the buffer with `call 13` whenever fewer
than four bytes are free.  It ends with `call 64`, the write shim, and
frees the buffer with `call 60`, whose body is empty.

The pair buffer stays with the caller.  The body reads it and writes
nothing into it.  The final cursor, frontier and history stay
existential, because the number of grows depends on the entry count. -/
def Func5Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp arg capacity ptr : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 8 [.i32 arg]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp replyDepth below ∗
        HashMap.Table.optionU32At 0 arg o ∗
        Slices.ByteSlice 0 (arg + 8)
          (WordCodec.u32le.serialize
            [capacity, ptr, UInt32.ofNat pairs.length]) ∗
        Slices.ByteSlice 0 ptr (HashMap.Table.pairBytes pairs) ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜pairs.length ≤ 2 ^ 27 ∧ replyDepth ≤ sp.toNat ∧
          arg.toNat + 20 < UInt32.size ∧
          ptr.toNat + 8 * pairs.length < UInt32.size⌝ ∗
        (-- the normal arm
         (∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp replyDepth below' -∗
            HashMap.Table.optionU32At 0 arg o -∗
            Slices.ByteSlice 0 (arg + 8)
              (WordCodec.u32le.serialize
                [capacity, ptr, UInt32.ofNat pairs.length]) -∗
            Slices.ByteSlice 0 ptr (HashMap.Table.pairBytes pairs) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input
              (output ++ Borsh.option Borsh.u32 o ++
                HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
                  pairs) raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

end Project.RustHashMap.EntriesContracts
