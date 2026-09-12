import Project.RustHashMap.VecGrow
import Project.RustHashMap.DeallocNoop

/-!
# Call contracts of the bodies that the `map_len` driver calls

The tail of the `map_len` driver calls three functions whose bodies are not
proved yet:

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
An audit of the WAT call graph on 2026-09-11 measured the true maximum of
all three constants.  Each constant is large enough, and each one is
exactly equal to the true maximum.  There is no slack.  A new local, or a
new version of rustc, borsh or hashbrown, can break all three at once.

The audit is sound only because every reachable `call_indirect` resolves
to one concrete leaf.  The module has one table of 17 entries, filled from
index 1 by the element segment.  Three resolutions carry the result:

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
51, 48, 49, 44 and 58.

The audit measured the worst path and it uses exactly 160 bytes:

```
f55(+16) f42(+0) f43(+16) f57(+16) f51(+16) f48(+48) f49(+16) f44(+32)
```

The path returns normally, so 160 is the true maximum for a run that does
not trap.  There is no slack. -/
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

The static message bytes are not a resource here.  They live in the data
segment at [1048576, 1049496), and
`Project.RustHashMap.Adequacy.entryHeap` holds only the stack, the
allocator cursor and the thread-local cells, so no caller owns them.

CAUTION. Read this before you start the body proof.  The contract can
leave the message bytes out, because the driver only passes the pointer
on.  The body cannot.  The chain reaches `func 57`, which runs
`memory.copy` from the message pointer into the fresh `String` buffer
(WAT line 9874).  A separation logic proof of that step needs the source
bytes as a resource.  The driver calls this function with the pointer
1049107 and the length 18, which is the text `Not all bytes read` inside
the data segment.

Adding the data segment to `entryHeap` is the fix, as a fourth
`insertFreshBytes` layer between the stack and the allocator cursor.  The
existing layers give the pattern to copy.  The cost reaches `EntrySpec`,
the driver proof and this contract, so do it before the body, not during
it. -/
def Func52Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out kind msgPtr msgLen : UInt32)
    (heapId : GName) (outBefore below : List UInt8)
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
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 16 ∧ errorNewDepth ≤ sp.toNat ∧
          out.toNat + 16 < UInt32.size ∧
          msgLen.toNat ≤ 2147483647⌝ ∗
        ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
            ∀ word3 : UInt32, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp errorNewDepth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
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

The audit measured the worst path and it uses exactly 240 bytes:

```
f4(+64) f52(+16) f55(+16) f42(+0) f43(+16) f57(+16) f51(+16) f48(+48)
f49(+16) f44(+32)
```

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

On failure the output slot holds a 16-byte `io::Error`, and word 0 is a
`String` capacity, so it is never `okTag`.  The failure arm leaves the
slice header advanced by an unspecified amount, which is sound because the
driver does not read it again.

The caller keeps the input bytes throughout.  The decoder never writes
them.

CAUTION. Test this contract for the capacity-overflow trap before you
start the body.  `Func52Spec` above needed a length bound, because the
`RawVec` path traps with a bare `unreachable` when the requested byte
count passes `isize::MAX`.  The decoder can reach the same code.  Two
facts are measured:

* `func 4` holds exactly one `call 99`, at WAT line 818, and it pushes the
  alignment 4 as the first argument.  A non-zero first argument selects
  the allocation-failure arm of `func 99`, not the capacity-overflow arm.
  That arm is dead, because the bump allocator never returns null.  It
  either succeeds or traps with `talos.oom`.
* `func 4` also reaches `func 99` through `func 26`, at WAT line 8848.
  That site pushes two loaded words, so it can select either arm.

The second site is not yet analysed.  If it can overflow, this contract
needs a bound near `8 * (headerWord bytes).toNat <= 2147483644`.  The
driver can supply such a bound the way `AfterRead_length_lt` supplies the
present one, because `VecStorage` holds a block that the bump allocator
returned, and `classifyBump` only succeeds below `isize::MAX`. -/
def Func1Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out hdr ptr len : UInt32)
    (heapId : GName) (bytes outBefore below : List UInt8)
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
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 16 ∧ bytes.length = len.toNat ∧
          decoderDepth ≤ sp.toNat ∧ out.toNat + 16 < UInt32.size ∧
          hdr.toNat + 8 < UInt32.size⌝ ∗
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
            Slices.ByteSlice 0 buffer (payload ++ spare) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜payload = (bytes.drop 4).take (8 * (headerWord bytes).toNat) ∧
              (headerWord bytes).toNat ≤ capacity.toNat ∧
              spare.length = 8 * (capacity.toNat - (headerWord bytes).toNat) ∧
              ((headerWord bytes).toNat = 0 → capacity = 0)⌝ -∗
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
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜word0 ≠ okTag⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage))))))

end Project.RustHashMap.BodyContracts
