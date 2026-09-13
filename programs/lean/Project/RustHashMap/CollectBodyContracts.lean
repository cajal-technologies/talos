import Project.RustHashMap.CollectContract
import CodeLib.RustStd.HashMap.OptionOut

/-!
# Call contracts of the five functions that `collect_entries` calls

`Project.RustHashMap.CollectContract` states `Func2Spec`, the contract of
absolute `func 5`.  Its body calls five further functions.  This module
states a contract for each one that a body proof reaches, and records why
the other two need none.

| Absolute | Local | Rust | WAT | Contract |
| --- | --- | --- | --- | --- |
| 16 | 13 | the `RandomState` thread-local | 2953-3018 | `Func13Spec` |
| 83 | 80 | the seed source | 10611-10651 | `Func80Spec` |
| 17 | 14 | `RawTableInner::reserve_rehash_inner` | 3019-4130 | `Func14Spec` |
| 18 | 15 | `HashMap::insert` | 4131-4546 | `Func15Spec` |
| 97, 98 | 94, 95 | the two error builders | 11125-11156 | none, see below |

## What the call sites fix

Every contract below is specialized to the one call site that
`collect_entries` has.  A general contract would cover code that no run of
`map_len` reaches.

`func 5` calls `func 16` with the literal argument 0 at WAT 873 to 874.
The branch at WAT 2965 to 2982, which reads a cached seed pair through a
non-null pointer, is dead.  So is the panic at WAT 2993 to 3004, which
needs the state byte to be 2 while the module only ever stores 0 and 1.

`func 5` calls `func 17` once, at WAT 908 to 919, with the arguments
`(frame+8, frame+16, len, frame+32, 1)`.  The table at frame+16 is the
static empty `RawTableInner` that WAT 883 to 890 copies from 1048584, so
`items` is 0 and `bucket_mask` is 0.  Three regions of `func 17` are then
unreachable:

* rehash in place, WAT 3116 to 3640, because `full_cap` is 0 and
  `new_items` is `len`, which is at least 1;
* phase D, the resize loop with the second inlined SipHash, WAT 3746 to
  4084, because the guard at WAT 3747 tests `items == 0`;
* phase F, the free, WAT 4098 to 4117, because the guard at WAT 4099
  tests `old_mask == 0` and the static singleton is never freed.

So `Func14Spec` covers phase A, phase B, phase C, phase E and the
epilogue, about 130 of the 1112 lines.

`func 18` guards its own `call 17` at WAT 4314 on `growth_left == 0`, at
WAT 4302 to 4304.  After the single `reserve(len)` the table has
`growth_left = bucketMaskToCapacity (buckets - 1)`, which is at least
`len`, and insert `k` sees at least `len - k`, so the guard is false at
every insert.  `Func15Spec` therefore allocates nothing and has one arm.

## Why funcs 97 and 98 get no contract

`func 5` passes fallibility 1, so both builders take their nonzero arm.
`func 97` calls `func 104` and `func 98` calls `func 102`, and `func 102`
is `call 80` then `unreachable`.  Neither reaches `call 2`, the
`talos.oom` import, so a capacity-overflow exit is a plain Wasm trap and
is neither arm of `Func2Spec`.  A contract would only name an outcome that
the proof must show unreachable.  `Func14Spec` takes the bound instead.

CAUTION.  `Func2Spec` does not carry that bound today.  Its precondition
bounds `8 * cap` by `UInt32.size` through the byte slice of the pair
buffer, which allows `cap` up to 536870911, and `BumpHeap` owns the cursor
and the frontier ghost, not the bytes above the frontier, so no
disjointness argument recovers a tighter bound.  `Func2Spec` is therefore
not provable as stated.  The repair is the one commit 44bf4f3 made for the
decoder: strengthen the accepting arm of `Func1Spec` with a heap tie on
`capacity`, then pass it down.  Do that edit in one window, because both
contracts are imported by `DriverProof` and `DriverTailProof`.

`Func2Spec` misses a second conjunct for the same reason.  `Func13Spec`
needs `keysBefore[16]? != some 2`, because the guard at WAT 2993 to 2997
panics when the thread-local state byte is 2.  `Func2Spec` lends
`keysBefore` with a length equation only, and the guard at WAT 867 to 872
in `func 5` gives just "not 1", so the fact has to come from the entry.
It holds there: the one data segment runs from 1048576 to 1049496 and the
state byte is at 1049528, so it starts at 0.  Add both conjuncts in the
same window.

## The stack constants

`collectDepth` is 192 and the audit that measured it gives the path
`f5(+48) f18(+16) f17(+32) f97(+0) f104(+32) f79(+16) f72(+0) f73(+16)
f75(+32)`.  Each constant below is the sum along the worst path from the
entry of that function, so each includes the frame of the function itself.
The frames are read from the `global.get 0` prologue of each body.

```
panic subtree   f104(32) f79(16) f72(0) f73(16) f75(32)          = 96
alloc subtree   f102(0) f80(0) f81(16) f70(0) f71(0) f76(0)      = 16
f83             16 + max(0, 16)                                  = 32
f16             16 + max(32, 96)                                 = 112
f17             32 + max(0, 96, 16)                              = 128
f18             16 + 128                                         = 144
f5              48 + max(112, 144, 128, 0)                       = 192
```

The last line is `collectDepth`, so the constants agree with the audit
with no slack at the top.  The two indirect calls that `func 71` and
`func 75` make resolve to leaves; the argument is in the
`Project.RustHashMap.BodyContracts` docstring and it is what makes the
call graph acyclic.
-/

namespace Project.RustHashMap.CollectBodyContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open scoped Wasm.SmallStep.Outcome

/-! ## Constants -/

/-- The stack that the seed source takes below its caller: its own 16-byte
frame, and 16 more for the dead allocation-error chain below `func 102`. -/
def seedSourceDepth : Nat := 32

/-- The stack that the `RandomState` thread-local takes below its caller:
its own 16-byte frame, and 96 for the dead panic subtree, which is deeper
than the 32 of the seed source. -/
def randomStateDepth : Nat := 112

/-- The stack that `reserve_rehash_inner` takes below its caller: its own
32-byte frame and 96 for the dead panic subtree below `func 97`. -/
def resizeDepth : Nat := 128

/-- The stack that `insert` takes below its caller: its own 16-byte frame
and the 128 of `reserve_rehash_inner`, whose call is dead on this path but
which the constant still covers. -/
def insertDepth : Nat := 144

/-- The largest capacity that `reserve_rehash_inner` serves without taking
the capacity-overflow exit.

The tightest of the four guards is the one at WAT 3679, which rejects a
total allocation above 2147483640 bytes.  The total is `9 * buckets + 8`
and `buckets` is a power of two, so the guard needs `buckets` at most
`2 ^ 27`, and `Table.capacityToBuckets` reaches `2 ^ 27` exactly when the
capacity is at most `bucketMaskToCapacity (2 ^ 27 - 1)`, which is
`2 ^ 27 / 8 * 7`.

The guard at WAT 3094 is looser: it allows `buckets` up to `2 ^ 28`, so a
capacity up to 234881024.  The guards at WAT 3039 and 3080 are looser
still. -/
def maxTableCapacity : Nat := 117440512

theorem maxTableCapacity_eq :
    maxTableCapacity = HashMap.Table.bucketMaskToCapacity (2 ^ 27 - 1) := by
  decide

/-! ## `RandomState` seeds -/

/-- Absolute `func 83`, local `func80`.  The one argument is a 16-byte
output slot.

The body writes two `u64` words into the slot and returns.  Neither word
is random.  WAT 10633 to 10638 stores the address of the byte at
`frame + 15`, and WAT 10639 to 10642 stores the pointer that
`call 58(1, 1)` returned at WAT 10625, which WAT 10646 frees again with
`call 60`, whose body is empty.  Both are addresses of the run, so the
contract returns them existentially.

`call 58` can raise the terminal `talos.oom` host trap, so the contract
has the usual second arm.  The null-pointer arm at WAT 10628 to 10631 is
dead, because `func 58` traps instead of returning 0. -/
def Func80Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out : UInt32) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 83 [.i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp seedSourceDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 16 ∧ seedSourceDepth ≤ sp.toNat ∧
          out.toNat + 16 < UInt32.size⌝ ∗
        (-- the normal arm
         (∀ k0 : UInt64, ∀ k1 : UInt64, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp seedSourceDepth below' -∗
            pointsTo_u64 0 out k0 -∗
            pointsTo_u64 0 (out + 8) k1 -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-- Absolute `func 16`, local `func13`.  The one argument is the pointer to
a cached seed pair, and `collect_entries` passes the literal 0.

With the argument 0 the body calls `func 83` for a fresh pair, checks the
state byte at 1049528 against 2, stores 1 there, and stores the pair at
1049512 and 1049520.  The contract takes the thread-local region as raw
bytes and gives it back as the two seed words plus the eight trailing
bytes, because that is the shape every caller reads.

The state byte is in the trailing bytes and the contract says it is 1.  No
caller of `func 16` reads it again inside one run of `map_len`, but the
guard at WAT 867 to 872 in `func 5` reads it before the call, so a second
call would see 1 and skip.

CAUTION.  The precondition needs `keysBefore[16]? != some 2`, because the
guard at WAT 2993 to 2997 panics when the state byte is 2, through
`call 104` and then `unreachable`, which is neither arm.  The guard in
`func 5` gives only "not 1", so the fact comes from the entry: the one
data segment ends at 1049496 and the state byte is at 1049528, so it
starts at 0 and the module only ever stores 1 there.  `Func2Spec` does not
carry that conjunct today; see the module docstring. -/
def Func13Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp : UInt32) (keysBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 16 [.i32 0]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp randomStateDepth below ∗
        Slices.ByteSlice 0 randomStateCell keysBefore ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜keysBefore.length = randomStateSize ∧
          randomStateDepth ≤ sp.toNat ∧
          keysBefore[16]? ≠ some 2⌝ ∗
        (-- the normal arm
         (∀ k0 : UInt64, ∀ k1 : UInt64, ∀ tail : List UInt8,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp randomStateDepth below' -∗
            pointsTo_u64 0 randomStateCell k0 -∗
            pointsTo_u64 0 (randomStateCell + 8) k1 -∗
            Slices.ByteSlice 0 (randomStateCell + 16) tail -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜tail.length = randomStateSize - 16 ∧ tail.head? = some 1⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## `reserve_rehash_inner` -/

/-- Absolute `func 17`, local `func14`: `RawTableInner::reserve_rehash_inner`.

The five arguments in source order are the 8-byte `Result` slot, the
`RawTableInner` pointer, the extra item count, the `RandomState` pointer
and the fallibility flag.  `collect_entries` passes 1 for the flag, which
is `Infallible`, so both error builders panic rather than return.

This contract covers the one reachable call: the table is the static empty
singleton, so `items` is 0, `buckets` is 1 and `growthLeft` is 0.  The
model calls that `Table.empty`, and `Table.reserve` on it with a positive
`additional` reduces to `Table.withCapacity additional`, because the fold
of `Table.resize` runs over an empty `fullIndices`.

The `additional` bound kills every capacity-overflow guard.  Without it
the body reaches `func 97` and traps, which is neither arm.

The `Result` slot takes the `Ok` tag `0x80000001` in word 0.  Word 1 is
untouched on that path, so the contract leaves it existential.  The
allocation at WAT 3685 can raise `talos.oom`, so the second arm stays. -/
def Func14Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out table additional hasher : UInt32)
    (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 17
      [.i32 1, .i32 hasher, .i32 additional, .i32 table, .i32 out]
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
          t = HashMap.Table.empty ∧
          1 ≤ additional.toNat ∧ additional.toNat ≤ maxTableCapacity⌝ ∗
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
              (HashMap.Table.withCapacity additional.toNat) -∗
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

/-! ## `insert` -/

/-- Absolute `func 18`, local `func15`: `HashMap::insert`.

The four arguments in source order are the 8-byte `Option<u32>` slot, the
32-byte map value, the key and the value.  The map value holds the
`RawTableInner` in its first 16 bytes and the two seeds at offsets 16 and
24, which is what `Table.HashMapAt` says.

The body inlines SipHash-1-3 over the key at WAT 4138 to 4300, with the
same length byte folded into the start constant `8098989879002948979` at
WAT 4145 that `func 17` uses.  Then it probes and writes.

`growthLeft` at least 1 makes the `call 17` at WAT 4314 dead, so this
contract allocates nothing, touches no stream and has one arm.  It still
takes the stack, because the compiled body commits a frame at WAT 4133 to
4137.

The result is the model pair `Table.insert`: the old value when the key
was present, and the new table.  `Table.insert` starts with
`Table.reserve hash t 1`, which returns `t` unchanged under the same
`growthLeft` hypothesis. -/
def Func15Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out mapBase key value : UInt32)
    (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (outBefore below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 18 [.i32 value, .i32 key, .i32 mapBase, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp insertDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        HashMap.Table.HashMapAt 0 mapBase k0 k1 t ∗
        ⌜outBefore.length = 8 ∧ insertDepth ≤ sp.toNat ∧
          out.toNat + 8 < UInt32.size ∧ mapBase.toNat + 32 < UInt32.size ∧
          HashMap.Table.Layout (HashMap.SipHash.hashU32 k0 k1) t ∧
          1 ≤ t.growthLeft⌝ ∗
        (∀ below' : List UInt8,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp insertDepth below' -∗
            HashMap.Table.optionU32At 0 out
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                t key value).1 -∗
            HashMap.Table.HashMapAt 0 mapBase k0 k1
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                t key value).2 -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ))

end Project.RustHashMap.CollectBodyContracts
