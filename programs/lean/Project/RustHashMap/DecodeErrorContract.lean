import Project.RustHashMap.DecoderLoop

/-!
# The contract of the decode-error conversion

The error arm of the borsh decoder builds an `io::Error` with absolute
`func 55` and then turns it into the error that the output slot of the
decoder takes.  Absolute `func 52`, local `func49`, is that second step.
The decoder calls it at WAT lines 525, 659 and 736.

This module states its contract.  The proof of the decoder takes the
contract as a hypothesis, in the same way that
`Project.RustHashMap.DriverTailProof.twp_driver_tail` takes `Func1Spec`.

## What the body does

The body keeps a 16-byte frame.  It reads the `ErrorKind` tag of the error
with `func 53`, compares the tag with the static byte at 1049136 with
`func 54`, and then takes one of two arms.  `br_if` leaves the inner block
when the comparison returns a non-zero value, which is when the two bytes
are equal.

* The tags are equal.  The body builds a second `io::Error` into the output
  slot with `func 55`, from the 26-byte message at 1049137, and then drops
  the first error with `func 38`.  WAT lines 9686 to 9700.
* The tags differ.  The body copies the sixteen bytes of the error into the
  output slot and leaves the error alone.  WAT lines 9673 to 9684.

Word 0 of the output is never `okTag`.  On the copy arm it is word 0 of the
input, which the caller promises is not `okTag`.  On the other arm it is
the capacity of a 26-byte `String`, and `Func52Spec` promises that the
capacity is not `okTag`.

## The stack

`func49Depth` is `16 + errorNewDepth`, because the deepest call of the body
is the one to `func 55`.  The audit of 2026-09-11 measured the worst path
of the decoder as

```
f4(+64) f52(+16) f55(+16) f42(+0) f43(+16) f57(+16) f51(+16) f48(+48)
f50(+16) f44(+32)
```

and `f52` there is absolute `func 52`.  So `decoderDepth` is
`64 + func49Depth`, and there is no slack.

## What is proved

`Project.RustHashMap.Func49Proof.func49_correct` proves the contract.  The
thirteen bodies below it, absolute 34 to 41, 45 to 47, 53 and 54, are
proved too.  `Project.RustHashMap.DropErrorContracts` states their
contracts.
-/

namespace Project.RustHashMap.DecodeErrorContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open scoped Wasm.SmallStep.Outcome

/-- The stack that the decode-error conversion takes below its caller.  Its
own frame is 16 bytes, and the rest is the `io::Error::new` chain. -/
def func49Depth : Nat := 16 + errorNewDepth

/-- The decoder takes its own 64-byte frame and then calls the conversion.
-/
theorem decoderDepth_conversion : decoderDepth = 64 + func49Depth := by rfl

/-- Absolute `func 52`, local `func49`.  The arguments in source order are
the 16-byte output slot and the 16-byte `io::Error`.

The body gives the storage of the error back with its content unspecified,
because the second arm drops the error through `func 38`.  The caller of
the conversion holds that storage in its own frame, so it needs the bytes
back but not their content. -/
def Func49Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out errPtr : UInt32)
    (errWord0 errWord1 errWord2 errWord3 : UInt32)
    (heapId : GName) (outBefore below dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 52 [.i32 errPtr, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func49Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 errPtr
          (WordCodec.u32le.serialize
            [errWord0, errWord1, errWord2, errWord3]) ∗
        Slices.ByteSlice 0 entryStackTop dataBytes ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 16 ∧ func49Depth ≤ sp.toNat ∧
          out.toNat + 16 < UInt32.size ∧ errPtr.toNat + 16 < UInt32.size ∧
          errWord0 ≠ okTag ∧ dataBytes.length = dataSegmentSize⌝ ∗
        ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
            ∀ word3 : UInt32, ∀ errAfter : List UInt8,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func49Depth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
            Slices.ByteSlice 0 errPtr errAfter -∗
            Slices.ByteSlice 0 entryStackTop dataBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜word0 ≠ okTag ∧ errAfter.length = 16⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

end Project.RustHashMap.DecodeErrorContracts
