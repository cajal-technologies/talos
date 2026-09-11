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
51, 48, 49, 44 and 58. -/
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

The static message bytes are not a resource here.  They live in a data
segment above the stack, and `Project.RustHashMap.Adequacy.entryHeap` holds
only the stack and the allocator cursor, so no caller owns them. -/
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
          out.toNat + 16 < UInt32.size⌝ ∗
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
bytes; the rest is the error chain through 55 and 52.  This number is
measured from the WAT and is not proved.  A body proof that needs more must
raise it here. -/
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
them. -/
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
