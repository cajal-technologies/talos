import Project.RustHashMap.BodyContracts
import Project.RustHashMap.CollectBodyContracts
import CodeLib.RustStd.HashMap.ProbeWasm
import CodeLib.RustStd.HashMap.OptionOut
import CodeLib.RustStd.HashMap.TableRefinement

/-!
# The contracts of the two map operations and of the two bodies below them

`map_insert` and `map_remove` each end with one call that changes the
table.  `map_insert` calls absolute `func 6`, a shim that forwards to
`HashMap::insert`, absolute `func 18`.  `map_remove` calls absolute
`func 11`, which is `HashMap::remove` itself.

This module states four contracts:

| Absolute | Local | Rust | WAT | Contract |
| --- | --- | --- | --- | --- |
| 6 | 3 | the `insert` shim | 975-1021 | `Func3Spec` |
| 11 | 8 | `HashMap::remove` | 1925-2285 | `Func8Spec` |
| 17 | 14 | `reserve_rehash_inner` | 3019-4130 | `Func14ResizeSpec` |
| 18 | 15 | `HashMap::insert` | 4131-4546 | `Func15InsertSpec` |

Nothing is proved here; a contract is an interface.

## Why absolute 17 and 18 need a second contract

`Project.RustHashMap.CollectBodyContracts` already states a contract for
each of these two bodies.  Both are specialized to the one call site that
`collect_entries` has: `func 17` serves the static empty singleton only,
and `func 15` carries `1 <= t.growthLeft`, which makes its own `call 17`
dead and lets it allocate nothing.

`map_insert` reaches neither of those.  It inserts into a table that a
driver decoded, whose `growthLeft` may be zero, so `func 18` takes the
resize edge X-F18-RESIZE of `Analysis/scope-and-exclusions.md`, the
`call 17` at WAT 4314 behind the guard at WAT 4302 to 4304.  That edge is
live here.  `Func15InsertSpec` and `Func14ResizeSpec` are therefore the
general contracts of the same two bodies: they take the stream and the
bump heap, they carry an out-of-memory arm, and `Func14ResizeSpec` takes
a general table rather than the singleton.

The two contracts stay in this module and nothing imports them from the
`collect` lane, so the two windows do not collide.

## Absolute `func 11` has no dead arm and no frame

The body holds no `global.get 0` and calls nothing.  It reads the map,
erases one bucket in place, and copies the whole 32-byte map value into
the answer.  Its contract therefore takes `RuntimeContext` and the map
alone, in the shape of
`Project.RustHashMap.LookupContracts.Func17Spec`.

## The stack constants

`resizeDepth` is the 32-byte frame of absolute `func 17`, at WAT 3021 to
3023, plus the 96 of the dead panic subtree below `call 97`.  This module
reads it from `Project.RustHashMap.CollectBodyContracts`, which is the one
home of that constant.  `insertFullDepth` is the 16-byte frame of absolute
`func 18`, at WAT 4133 to 4135, plus `resizeDepth`.  `insertWrapDepth` is
the 16-byte frame of absolute `func 6`, at WAT 977 to 979, plus
`insertFullDepth`.  `maxTableCapacity` is in
`Project.RustHashMap.EntryContracts`, which both lanes read.
-/

namespace Project.RustHashMap.MapOpContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectBodyContracts
open scoped Wasm.SmallStep.Outcome

/-! ## Constants -/

/-- The stack that `HashMap::insert`, absolute `func 18`, takes below its
caller on the general path: its own 16-byte frame and `resizeDepth`, for
the resize edge that a general table may take. -/
def insertFullDepth : Nat := 16 + resizeDepth

theorem insertFullDepth_eq : insertFullDepth = 144 := rfl

/-- The stack that the shim, absolute `func 6`, takes below its caller:
its own 16-byte frame and `insertFullDepth`. -/
def insertWrapDepth : Nat := 16 + insertFullDepth

theorem insertWrapDepth_eq : insertWrapDepth = 160 := rfl

/-! ## `HashMap::remove`, absolute `func 11` -/

/-- Absolute `func 11`, local `func8`, WAT 1925 to 2285.  The three
arguments in source order are the 40-byte output slot, the map value and
the key, so local 0 is the slot, local 1 the map and local 2 the key.

The body inlines SipHash-1-3 over the key, probes, erases the bucket it
finds, and then copies the whole 32-byte map value into the answer at
offsets 8 to 40, at WAT 2270 to 2284.  The answer is therefore the
`Option<u32>` at `out` and a fresh map value at `out + 8`.  The map that
the caller lent keeps its 32 bytes, but their content is the content of
the table before the copy, which no caller reads again, so the contract
gives them back as raw bytes.

The body allocates nothing, touches no stream and commits no frame.
There is no dead arm and no ledger row. -/
def Func8Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (out map key : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (outBefore : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 11 [.i32 key, .i32 map, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Slices.ByteSlice 0 out outBefore ∗
        HashMap.Table.HashMapAt 0 map k0 k1 t ∗
        ⌜outBefore.length = 40 ∧
          HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t ∧
          HashMap.Table.Clean t ∧
          out.toNat + 40 < UInt32.size ∧
          map.toNat + 32 < UInt32.size⌝ ∗
        (∀ mapBytes : List UInt8,
          RuntimeContext -∗
          HashMap.Table.optionU32At 0 out
            (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1) t key).1 -∗
          HashMap.Table.HashMapAt 0 (out + 8) k0 k1
            (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1) t key).2 -∗
          Slices.ByteSlice 0 map mapBytes -∗
          ⌜mapBytes.length = 32⌝ -∗
          ResumeWP [] callerLocals stack code arity remainder controls
            calls s E Φ))

/-! ## The `insert` shim, absolute `func 6` -/

/-- Absolute `func 6`, local `func3`, WAT 975 to 1021.  The four
arguments in source order are the 40-byte output slot, the map value, the
key and the value, so local 0 is the slot, local 1 the map, local 2 the
key and local 3 the value.

The body commits a 16-byte frame, calls absolute `func 18` with an
8-byte slot at `frame + 8`, and then copies the map value into the answer
at offsets 8 to 40 and the `Option<u32>` into offsets 0 to 8.  It is the
same answer shape as absolute `func 11`.

`t.items < maxTableCapacity` is what the resize edge needs: absolute
`func 18` may call `call 17` with the addition 1, and
`Func14ResizeSpec` rejects a capacity above `maxTableCapacity`. -/
def Func3Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out map key value : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 6 [.i32 value, .i32 key, .i32 map, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp insertWrapDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        HashMap.Table.HashMapAt 0 map k0 k1 t ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 40 ∧
          HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t ∧
          HashMap.Table.Clean t ∧
          t.items < maxTableCapacity ∧
          t.buckets ≤ 2 ^ 27 ∧
          t.growthLeft < UInt32.size ∧
          insertWrapDepth ≤ sp.toNat ∧
          out.toNat + 40 < UInt32.size ∧
          map.toNat + 32 < UInt32.size⌝ ∗
        (-- the normal arm
         (∀ mapBytes : List UInt8, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp insertWrapDepth below' -∗
            HashMap.Table.optionU32At 0 out
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                t key value).1 -∗
            HashMap.Table.HashMapAt 0 (out + 8) k0 k1
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                t key value).2 -∗
            Slices.ByteSlice 0 map mapBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜mapBytes.length = 32⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## `HashMap::insert`, absolute `func 18`, both arms -/

/-- Absolute `func 18`, local `func15`, WAT 4131 to 4546, on the general
path.

The four arguments in source order are the 8-byte `Option<u32>` slot, the
32-byte map value, the key and the value.

This is `Project.RustHashMap.CollectBodyContracts.Func15Spec` without
`1 <= t.growthLeft`.  Dropping that hypothesis opens the resize edge
X-F18-RESIZE, the `call 17` at WAT 4314, so the contract gains the bump
heap, the stream, an out-of-memory arm, and the capacity bound that
`Func14ResizeSpec` asks for.  The final cursor, frontier and history stay
existential, because the resize runs only when `growthLeft` is zero.

`t.growthLeft < UInt32.size` stays.  The guard at WAT 4302 to 4304 reads
the header word, not the model counter, and `Table.Layout` puts no bound
on `growthLeft`, so a multiple of `UInt32.size` would store as the word
0 and take the resize edge against the model.

The result is the model pair `Table.insert`, which starts with
`Table.reserve hash t 1`.  On this path that reserve is the resize that
`call 17` runs. -/
def Func15InsertSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out mapBase key value : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 18 [.i32 value, .i32 key, .i32 mapBase, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp insertFullDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        HashMap.Table.HashMapAt 0 mapBase k0 k1 t ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 8 ∧ insertFullDepth ≤ sp.toNat ∧
          out.toNat + 8 < UInt32.size ∧
          mapBase.toNat + 32 < UInt32.size ∧
          HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t ∧
          HashMap.Table.Clean t ∧
          t.items < maxTableCapacity ∧
          t.buckets ≤ 2 ^ 27 ∧
          t.growthLeft < UInt32.size⌝ ∗
        (-- the normal arm
         (∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp insertFullDepth below' -∗
            HashMap.Table.optionU32At 0 out
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                t key value).1 -∗
            HashMap.Table.HashMapAt 0 mapBase k0 k1
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                t key value).2 -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## `reserve_rehash_inner`, absolute `func 17`, the resize path -/

/-- Absolute `func 17`, local `func14`, WAT 3019 to 4130, on the path
that absolute `func 18` takes.

The five arguments in source order are the 8-byte `Result` slot, the
`RawTableInner` pointer, the extra item count, the `RandomState` pointer
and the fallibility flag.  Absolute `func 18` passes the addition 1 and
the flag 1 as literals at WAT 4305 to 4313, so the operand list carries
both as constants.

This is `Project.RustHashMap.CollectBodyContracts.Func14Spec` with a
general table instead of the static empty singleton, and with the
addition fixed to 1.  A general table has items, so the rehash-in-place
region and the resize loop are both live here, and the answer is
`Table.reserve` rather than `Table.withCapacity`.

`t.growthLeft = 0` is the guard that absolute `func 18` already tested,
so the reserve is never the identity.  `t.items + 1 <= maxTableCapacity`
kills the capacity-overflow exit X-F17-CAP, which is `call 97` and not an
arm.

The `Result` slot takes the `Ok` tag `okTag` in word 0.  Word 1 is
untouched on that path, so the contract leaves it existential.  The
allocation at WAT 3685 can raise `talos.oom`, so the second arm stays. -/
def Func14ResizeSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out table hasher : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 17
      [.i32 1, .i32 hasher, .i32 1, .i32 table, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp resizeDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        HashMap.Table.TableAt 0 table t ∗
        pointsTo_u64 0 hasher k0 ∗
        pointsTo_u64 0 (hasher + 8) k1 ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 8 ∧ resizeDepth ≤ sp.toNat ∧
          out.toNat + 8 < UInt32.size ∧ table.toNat + 16 < UInt32.size ∧
          hasher.toNat + 16 < UInt32.size ∧
          HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t ∧
          HashMap.Table.Clean t ∧
          t.growthLeft = 0 ∧
          t.items + 1 ≤ maxTableCapacity⌝ ∗
        (-- the normal arm
         (∀ word1 : UInt32, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp resizeDepth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [okTag, word1]) -∗
            HashMap.Table.TableAt 0 table
              (HashMap.Table.reserve (HashMap.SipHash.hashU32 k0 k1)
                t 1) -∗
            pointsTo_u64 0 hasher k0 -∗
            pointsTo_u64 0 (hasher + 8) k1 -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

end Project.RustHashMap.MapOpContracts
