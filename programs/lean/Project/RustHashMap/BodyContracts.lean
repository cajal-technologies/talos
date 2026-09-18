import Project.RustHashMap.VecGrow
import Project.RustHashMap.DeallocNoop

/-!
# Call contracts of the bodies that the `map_len` driver calls

The tail of the `map_len` driver calls three functions:

* absolute `func 4`, the borsh decoder of `Vec<(u32, u32)>`;
* absolute `func 5`, `collect_entries`, which builds the hash table;
* absolute `func 55`, `borsh::io::Error::new`.

This module states their contracts.  The driver proof takes them as
hypotheses, so the driver is proved before the bodies are.  Each contract
follows the shape of `Func98Spec` in `Project.RustHashMap.VecGrow`: a
`CallContract`, an `iprop` precondition, and a continuation with a normal
arm and an out-of-memory arm.

## The stack below the caller

`Func98Spec` gives `grow_one` the fixed sixteen bytes of `StackReserve`.
These three functions take much more, because each one calls further.
`StackBelow sp depth bytes` is the general form.  The depth of each
function is a named constant, measured from the WAT.  A body proof that
needs more stack than its constant gives must raise the constant, and only
the driver proof has to follow.

CAUTION. Do not let a body proof use more stack than its constant gives.
Each of the three constants is exactly the maximum that the WAT call graph
allows, so there is no slack.  A new local, or a new version of rustc,
borsh or hashbrown, can break all three at once.

The three constants are sound only because every reachable
`call_indirect` resolves to one concrete leaf.  The module has one table of
17 entries, filled from index 1 by the element segment.  Three resolutions
carry the result:

* `func 71` loads the panic hook from 1049536 and selects 1 when the hook
  is zero, so the target is `table[1]`, which is `func 76`, a leaf.
* the two indirect calls in `func 75` at WAT lines 10459 and 10481 sit
  behind a guard that loads 1049544, so both are dead.
* the indirect call in `func 75` at WAT line 10488 reads a vtable word,
  and `func 73` is its only caller and passes 1049204 or 1049232, which
  select `table[9]` and `table[14]`, both leaves.

Each of 1049536 and 1049544 lies above the data segment, which ends at
1049496, so Wasm zero-initializes it.  No instruction in the module stores
to either address.  Without these three resolutions the call graph has
cycles through `core::fmt` and the depth is unbounded.

## Why the error tag is never the success tag

The driver reads word 0 of the decoder output slot and compares it with
`0x80000001`.  On the error path that word is the capacity of the message
`String`.  The bump allocator refuses any allocation whose end passes
`isize::MAX`, so a capacity is at most `0x7fffffff` and can never equal
`0x80000001`.  Both contracts below state that inequality, because without
it the driver cannot show that the error branch is taken.
-/

namespace Project.RustHashMap.BodyContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open scoped Wasm.SmallStep.Outcome

/-! ## The stack region below a call -/

/-- The `depth` bytes below the stack pointer `sp`.  A callee owns them for
the length of the call and gives them back with the contents changed. -/
def StackBelow [WasmHeapGS Universal.State]
    (sp : UInt32) (depth : Nat) (bytes : List UInt8) : HeapIProp :=
  iprop(⌜bytes.length = depth⌝ ∗
    Slices.ByteSlice 0 (sp - UInt32.ofNat depth) bytes)

/-- The tag that the decoder writes in word 0 of its output slot for `Ok`.
It is `0x80000001`, which the WAT writes as `i32.const -2147483647`. -/
def okTag : UInt32 := 2147483649

/-- The stack that `borsh::io::Error::new` takes below the caller.  Its own
frame is 16 bytes; the rest is the format and allocate chain 42, 43, 57,
51, 48, 50, 44 and 58.

The worst path uses exactly 160 bytes:

```
f55(+16) f42(+0) f43(+16) f57(+16) f51(+16) f48(+48) f50(+16) f44(+32)
```

The path returns normally, so 160 is the true maximum for a run that does
not trap.  There is no slack.

`func 48` picks between `f49` and `f50` on bit 0 of its third argument at
WAT line 9426, and `func 51` passes the folded constant `0 & 1` there at
WAT lines 9593 to 9596, so `f49` is dead and `f50` is the live arm.  Both
frames are 16 bytes.

The other branch of `func 55` is `f55(+16) f56(+32)`, which is 48 bytes.
`func 56` does not commit the stack pointer; it writes a red zone below
the value it inherits.  The leaves `func 33` and `func 58` take no frame
at all, so the chain ends at `f44`. -/
def errorNewDepth : Nat := 160

/-! ## `borsh::io::Error::new` -/

/-- Absolute `func 55`, local `func52`.  The arguments in source order are
the 16-byte output slot, the `ErrorKind` byte, and a static message with
its length.  The function allocates the message as a `String` and packs
`{capacity, pointer, length, kind}` into the slot.

The contract keeps the four words abstract.  The driver only needs to know
that word 0 is not the success tag, and that it may hand word 0 and word 1
to the deallocator afterwards.  It needs no ownership of the message,
because it frees it through `DeallocNoop.Func57NoopSpec`.

## Why the length bound is necessary

The precondition bounds `msgLen` by `isize::MAX`.  Without that bound the
contract is false, not merely unprovable.  The chain reaches `func 48`,
which tests `size <= 0x80000000 - alignment` at WAT lines 9362 to 9369.
The alignment is 1 here, so the test is `msgLen <= 0x7fffffff`.  A larger
length takes the capacity-overflow arm, which sets the error tag, and
`func 51` then runs `call 99` and `unreachable` at WAT lines 9611 and
9612.  That is a bare trap.  It is not a return, and it is not the
`talos.oom` trap that the second arm covers, so neither arm of the
continuation applies.

The bound also gives the driver the inequality it needs.  Word 0 of the
error slot is the capacity of the message `String`, and `func 48` returns
either 0, for an empty message, or `msgLen`.  Both are at most
`0x7fffffff`, and `okTag` is `0x80000001`, so word 0 is never the success
tag.

The driver passes the literal length 18, so the bound closes by `decide`.

## Why the message bytes are a resource

The chain reaches `func 57`, which runs `memory.copy` from the message
pointer into the fresh `String` buffer at WAT line 9874.  A separation
logic proof of that step needs the source bytes.  The contract takes
`msgBytes` and gives it back unchanged, because the copy only reads it and
no step of the chain writes it.

The contract does not fix the content of `msgBytes`.  The driver passes
the pointer 1049107 and the length 18, which is the text
`Not all bytes read` in the data segment, but no arm of the continuation
reads the message again.  Both error paths write nothing to the output
stream.

The bytes come from the data segment at [1048576, 1049496).
`Project.RustHashMap.Adequacy.entryHeap` owns that region as its fourth
`insertFreshBytes` layer, `EntrySpec` carries it, and
`Project.RustHashMap.DriverTail.DriverTailSpec` cuts the eighteen-byte
window out of it. -/
def Func52Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out kind msgPtr msgLen : UInt32)
    (heapId : GName) (outBefore below msgBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 55 [.i32 msgLen, .i32 msgPtr, .i32 kind, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp errorNewDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 msgPtr msgBytes ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 16 ∧ errorNewDepth ≤ sp.toNat ∧
          out.toNat + 16 < UInt32.size ∧
          0 < msgLen.toNat ∧ msgLen.toNat ≤ 2147483647 ∧
          msgBytes.length = msgLen.toNat⌝ ∗
        ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
            ∀ word3 : UInt32, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp errorNewDepth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
            Slices.ByteSlice 0 msgPtr msgBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜word0 ≠ okTag⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## The borsh decoder -/

/-- The entry count that the first four bytes of the input announce. -/
def headerWord (bytes : List UInt8) : UInt32 :=
  WordCodec.decodeU32 (bytes.take 4)

/-- The decoder accepts exactly when it has a four-byte header and the
payload holds every pair that the header announces.  It does not reject
trailing bytes; it reports them through the slice header instead, and the
driver is what rejects them. -/
def DecodeAccepts (bytes : List UInt8) : Prop :=
  4 ≤ bytes.length ∧ 4 + 8 * (headerWord bytes).toNat ≤ bytes.length

/-- The stack that the decoder takes below the caller.  Its own frame is 64
bytes; the rest is the error chain through 52 and 55.

The worst path uses exactly 240 bytes:

```
f4(+64) f52(+16) f55(+16) f42(+0) f43(+16) f57(+16) f51(+16) f48(+48)
f50(+16) f44(+32)
```

`func 48` calls `f50` and not `f49`, because `func 51` passes the zeroed
flag 0 at WAT line 9594.  The two frames are both 16 bytes, so the total
is the same either way.

The path returns normally, so 240 is the true maximum for a run that does
not trap.  There is no slack. -/
def decoderDepth : Nat := 240

/-- Absolute `func 4`, local `func1`: `Vec<(u32, u32)>::deserialize`.

The arguments in source order are the 16-byte output slot and the slice
header.  The slice header holds the pointer at offset 0 and the remaining
length at offset 4.  The decoder reads the input through that pointer,
advances the header past everything it consumed, and writes a
`Result<Vec<(u32, u32)>, io::Error>` into the output slot.

On success the output slot holds the tag `okTag`, then the capacity, the
buffer pointer and the entry count.  The buffer holds the payload bytes
unchanged, because the compiled loop stores each key at `buffer + 8 i` and
each value at `buffer + 8 i + 4`, which is the wire order.  An empty vector
allocates nothing and reports capacity 0 with the dangling pointer 4.
The buffer pointer has a four-byte alignment, because the pair block
asks for that alignment.

On failure the output slot holds a 16-byte `io::Error`, and word 0 is a
`String` capacity, so it is never `okTag`.  The failure arm leaves the
slice header advanced by an unspecified amount, which is sound because the
driver does not read it again.

The caller keeps the input bytes throughout.  The decoder never writes
them.

## Why this contract needs no length bound

`Func52Spec` above needed one, because its `msgLen` is a free parameter
that nothing bounds.  The decoder reaches the same `RawVec` code and needs
no bound, because the quantity that can overflow there is tied to the
input length through the bump heap.

`func 4` reaches `func 99` at three sites, and both arms of `func 99` end
in `unreachable`.  The subtree behind it never calls the OOM import: one
arm runs 102, 80, 81 and 70, the other runs 103, 104 and 79, and each ends
in a bare trap.  The only call of the OOM import in the module is in
`func 59`, and `func 99` does not reach it.  Neither arm of the
continuation below covers a trap, so all three sites must be dead.

* WAT line 818 pushes the literal 4 as the first argument.  A non-zero
  first argument selects the allocation-failure arm.  That arm is dead,
  because `func 58` and `func 61` never return null.  The bump allocator
  either succeeds or raises `talos.oom`.
* WAT line 8848 sits in `func 26`, the amortized grow of the pair buffer.
  `func 27` writes the flag word 1 on both of its failure arms.  The
  allocation-failure arm writes the alignment 4 beside the flag, so it
  selects the same dead arm as the first site.  The capacity-overflow arm
  writes 0 beside the flag, so it selects the panic arm, and that one is
  live code.
* WAT line 9611 sits in `func 51`, the `RawVec` allocate of the error
  chain.  `Project.RustHashMap.Func48Proof` proves that body and shows the
  arm is dead, so this site needs no work in the decoder proof.

The overflow guard is at WAT lines 8868 to 8898.  With the element size 8
and the alignment 4 that `func 26` passes, the guard sends control to the
panic arm exactly when `8 * newCap > 2147483644`, and `newCap` is
`max(4, 2 * oldCap)`.

The body proof must carry two facts.  Write them as loop invariants.

* `heapBase + 16 * oldCap <= frontier + 4096` kills the capacity-overflow
  arm.  The first allocation is `8 * min(count, 512)` bytes, so the fact
  holds when the loop starts.  A grow allocates `16 * oldCap` more bytes,
  and `func 61` is a bump allocator that never hands the same byte out
  twice, so the fact holds again after the grow.

  `BumpHeap` bounds the frontier by 2147483648, so the fact bounds
  `16 * oldCap` by 2146438175.  The panic arm needs
  `8 * newCap > 2147483644` with `newCap = max(4, 2 * oldCap)`, and that
  needs `16 * oldCap` to be 2147483645 or more.  The margin is 1045470
  bytes.  `Project.RustHashMap.Decoder.grow_no_overflow` is the argument
  in Lean.

  The fact is about the allocator alone.  The contract lends the input as
  a plain byte slice and never says that the input lies in the heap.

* `4 + 8 * index <= bytes.length` says that the input holds every pair that
  the loop read.  The accepting arm needs it.  `func 26` runs only when the
  length word equals the capacity word, at WAT lines 764 to 772, so the
  buffer is full at a grow, and each pair consumed eight input bytes at WAT
  lines 745 to 754, after the four-byte header.

  The eight bytes hold for every pair, because the two arms that append a
  pair after a short read are dead.  Those arms are at WAT lines 718 and
  743, and both need word 0 of the error that `func 55` or `func 52`
  builds to be `okTag`.  That word is a `String` capacity, 27 at WAT line
  626 and 26 at WAT line 9689, so it is never `okTag`.

`Project.RustHashMap.Decoder.LoopInv` carries both facts.

## Why the data segment is a resource

The error arm builds a message with `func 55` at WAT lines 487 to 493, and
the loop builds the same one at WAT lines 621 to 627.  The message is 27
bytes at 1049080, which is `entryStackTop + 504`.  `Func52Spec` above takes
the message bytes as a resource, because the chain copies them.  The arm
then calls `func 52`, whose own error arm builds a second message of 26
bytes at 1049137.  Both sit in the data segment at [1048576, 1049496).

So this contract lends the whole data segment and gives it back unchanged.
The contract must lend the segment, because the body reads it.
`Project.RustHashMap.DriverTail.DriverTailSpec` carries the segment
already, so the caller pays nothing new.

## The subtree below the decoder

The error arm calls absolute `func 52`, which turns the `io::Error` into
the error that the output slot takes.  That call opens a subtree of 14
bodies and 325 WAT lines: 34 to 41, 45 to 47, 52, 53 and 54.  Each one is
small, and the largest is 63 lines.  The accepting arm of the decoder
reaches none of them.  `Project.RustHashMap.DecodeErrorContract` states the
call as `Func49Spec`, and `Project.RustHashMap.Func49Proof` proves it. -/
def Func1Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out hdr ptr len : UInt32)
    (heapId : GName) (bytes outBefore below dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 4 [.i32 hdr, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp decoderDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        pointsTo_u32 0 hdr ptr ∗
        pointsTo_u32 0 (hdr + 4) len ∗
        Slices.ByteSlice 0 ptr bytes ∗
        Slices.ByteSlice 0 entryStackTop dataBytes ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 16 ∧ bytes.length = len.toNat ∧
          decoderDepth ≤ sp.toNat ∧ out.toNat + 16 < UInt32.size ∧
          hdr.toNat + 8 < UInt32.size ∧
          dataBytes.length = dataSegmentSize⌝ ∗
        (-- the accepting arm
         (∀ capacity : UInt32, ∀ buffer : UInt32, ∀ payload : List UInt8,
            ∀ spare : List UInt8, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            ⌜DecodeAccepts bytes⌝ -∗
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp decoderDepth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize
                [okTag, capacity, buffer, headerWord bytes]) -∗
            pointsTo_u32 0 hdr
              (ptr + 4 + 8 * headerWord bytes) -∗
            pointsTo_u32 0 (hdr + 4)
              (len - 4 - 8 * headerWord bytes) -∗
            Slices.ByteSlice 0 ptr bytes -∗
            Slices.ByteSlice 0 entryStackTop dataBytes -∗
            Slices.ByteSlice 0 buffer (payload ++ spare) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜payload = (bytes.drop 4).take (8 * (headerWord bytes).toNat) ∧
              (headerWord bytes).toNat ≤ capacity.toNat ∧
              spare.length = 8 * (capacity.toNat - (headerWord bytes).toNat) ∧
              ((headerWord bytes).toNat = 0 → capacity = 0) ∧
              buffer.toNat % 4 = 0⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the rejecting arm
         ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
            ∀ word3 : UInt32, ∀ ptr' : UInt32, ∀ len' : UInt32,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            ⌜¬ DecodeAccepts bytes⌝ -∗
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp decoderDepth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
            pointsTo_u32 0 hdr ptr' -∗
            pointsTo_u32 0 (hdr + 4) len' -∗
            Slices.ByteSlice 0 ptr bytes -∗
            Slices.ByteSlice 0 entryStackTop dataBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜word0 ≠ okTag⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage))))))

end Project.RustHashMap.BodyContracts
