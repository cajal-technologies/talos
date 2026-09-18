import Project.RustHashMap.DecodeErrorContract

/-!
# The contract of the key-and-map decoder

`map_contains_key` and `map_get` read an input shaped `key ++ map`.
Absolute `func 10`, local `func7`, is the borsh reader of that pair.  It is
WAT lines 1741 to 1924.  `Project.RustHashMap.Spec.keyAndMap` is the model
of the same shape.

This module states the contract.  The proof of each driver takes it as a
hypothesis, in the same way that
`Project.RustHashMap.DriverTailProof.twp_driver_tail` takes `Func1Spec`.

## What the body does

The arguments in source order are the 20-byte output slot, the input
pointer and the input length.  The body keeps a 96-byte frame and holds
the slice header in it, at frame + 8 for the pointer and at frame + 12 for
the remaining length.

* The input is four bytes or longer.  The body reads the key from the
  first four bytes, advances the header past them, and calls absolute
  `func 4` on the rest.  WAT lines 1759 to 1776.
* The input is shorter than four bytes.  The body builds an `io::Error`
  with absolute `func 55`, from the 27-byte message at 1049080, and turns
  it into the decode error with absolute `func 52`.  WAT lines 1778 to
  1831.

The map decoder returns, and the body takes one of three exits.

* The decoder rejected the rest.  The body copies the 16-byte error into
  words 1 to 4 of the output slot and writes the tag 1.  WAT lines 1888 to
  1900.
* The decoder accepted the rest and left bytes behind.  The body builds a
  second `io::Error`, from the 18-byte message at 1049107, writes it the
  same way, and frees the pair buffer with absolute `func 60`.  WAT lines
  1859 to 1886.
* The decoder accepted the rest and consumed all of it.  The body writes
  the tag 0, the key, the capacity, the buffer pointer and the pair count.
  WAT lines 1902 to 1918.
  The buffer pointer has a four-byte alignment, because the map decoder
  promises it.

So word 0 of the output slot is the tag: 0 on success and 1 on failure.
The four words behind it are the answer on success and the decode error on
failure.

## The two dead arms

The body tests word 0 of each error against `okTag` and leaves the block
when the two are equal, at WAT lines 1798 to 1800 and 1822 to 1824.  Both
tests fail.  `Func52Spec` and `Func49Spec` each promise that word 0 of
what they build is not `okTag`, so neither arm is live.

## The stack depth

The body lowers the stack pointer by 96 and then calls absolute `func 4`,
absolute `func 52`, absolute `func 55` and absolute `func 60`.  The
decoder is the deepest of the four, so the body needs
`96 + decoderDepth` bytes.  There is no slack.

## What the failure arm keeps

The failure arm gives back the input bytes and the data segment, and it
gives back no pair buffer.  The trailing-bytes exit frees the buffer, and
the other two exits never allocate one.  The caller of a failing run
therefore holds exactly what it lent, less the buffer that it never
had. -/

namespace Project.RustHashMap.KeyDecoderContract

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.DecodeErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- The frame of absolute `func 10` is 96 bytes, and the deepest of its
four calls is the borsh decoder. -/
def keyDecoderDepth : Nat := 96 + decoderDepth

/-- The key of an input shaped `key ++ map`.  A borsh tuple has no framing
of its own, so the key is the first four bytes. -/
def leadingKey (bytes : List UInt8) : UInt32 :=
  WordCodec.decodeU32 (bytes.take 4)

/-- The bytes that the map decoder reads. -/
def mapBytes (bytes : List UInt8) : List UInt8 := bytes.drop 4

/-- The pair count that the map header names. -/
def pairCount (bytes : List UInt8) : UInt32 := headerWord (mapBytes bytes)

/-- The pair bytes that the map decoder copies into its buffer. -/
def keyPayload (bytes : List UInt8) : List UInt8 :=
  ((mapBytes bytes).drop 4).take (8 * (pairCount bytes).toNat)

/-- The body accepts the input when a key fits in front, the map decoder
accepts the rest, and the map decoder consumes the rest exactly.  The last
conjunct is the trailing-bytes test at WAT lines 1855 to 1858. -/
def KeyDecodeAccepts (bytes : List UInt8) : Prop :=
  4 ≤ bytes.length ∧ DecodeAccepts (mapBytes bytes) ∧
    4 + 8 * (pairCount bytes).toNat = (mapBytes bytes).length

/-- Absolute `func 10`, local `func7`: the borsh reader of `key ++ map`. -/
def Func7Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out ptr len : UInt32)
    (heapId : GName) (bytes outBefore below dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 10 [.i32 len, .i32 ptr, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp keyDecoderDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 ptr bytes ∗
        Slices.ByteSlice 0 entryStackTop dataBytes ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 20 ∧ bytes.length = len.toNat ∧
          keyDecoderDepth ≤ sp.toNat ∧ out.toNat + 20 < UInt32.size ∧
          dataBytes.length = dataSegmentSize⌝ ∗
        (-- the accepting arm
         (∀ capacity : UInt32, ∀ buffer : UInt32, ∀ spare : List UInt8,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            ⌜KeyDecodeAccepts bytes⌝ -∗
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp keyDecoderDepth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize
                [0, leadingKey bytes, capacity, buffer, pairCount bytes]) -∗
            Slices.ByteSlice 0 ptr bytes -∗
            Slices.ByteSlice 0 entryStackTop dataBytes -∗
            Slices.ByteSlice 0 buffer (keyPayload bytes ++ spare) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜(pairCount bytes).toNat ≤ capacity.toNat ∧
              spare.length =
                8 * (capacity.toNat - (pairCount bytes).toNat) ∧
              ((pairCount bytes).toNat = 0 → capacity = 0) ∧
              buffer.toNat % 4 = 0⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the rejecting arm
         ((∀ word1 : UInt32, ∀ word2 : UInt32, ∀ word3 : UInt32,
            ∀ word4 : UInt32, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            ⌜¬ KeyDecodeAccepts bytes⌝ -∗
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp keyDecoderDepth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [1, word1, word2, word3, word4]) -∗
            Slices.ByteSlice 0 ptr bytes -∗
            Slices.ByteSlice 0 entryStackTop dataBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜word1 ≠ okTag⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage))))))

end Project.RustHashMap.KeyDecoderContract
