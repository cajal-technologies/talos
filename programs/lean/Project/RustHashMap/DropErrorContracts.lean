import Project.RustHashMap.DecodeErrorContract

/-!
# Call contracts of the subtree below the decode-error conversion

`Project.RustHashMap.DecodeErrorContracts.Func49Spec` states the contract
of absolute `func 52`, the conversion that the error arm of the borsh
decoder calls at WAT lines 525, 659 and 736.  That body is the head of a
subtree of fourteen bodies.  This module states the contracts of the
thirteen bodies below it.

## The shape of the subtree

Absolute `func 52` calls four bodies.  One of them, absolute `func 55`, is
`borsh::io::Error::new` and is proved already.  The other three open a
tree that is almost a line:

```
52 -> 53
52 -> 54
52 -> 38 -> 36 -> 37 -> 34 -> 35 -> 39
                                 -> 40 -> 41 -> 45 -> 46
                                                   -> 47 -> 60
```

Absolute `func 60` is the deallocator.  Its compiled body is empty, and
`Project.RustHashMap.DeallocNoop.Func57NoopSpec` states that weaker
contract, so the subtree rests on proved ground and adds no new leaf.

## What the bodies do

* `func 54` compares one byte with one byte.  It keeps no frame.
* `func 53` reads the `ErrorKind` byte of the error.  The byte sits at
  offset 4 when word 0 is `0x80000000`, and at offset 12 otherwise.
* `func 38` down to `func 47` are the drop glue of the error.  `func 36`
  returns at once when word 0 is `0x80000000`.  Otherwise `func 39` walks
  the elements of the message buffer and does nothing to each of them, and
  `func 40` frees the buffer through `func 45`, `func 46` and `func 47`.

The drop reads the first twelve bytes of the error and writes none of
them, so every contract of the drop glue gives the three words back
unchanged.

## Why the drop needs no heap

`func 47` frees the buffer with absolute `func 60`, whose body is empty.
The subtree therefore holds no `LiveBlock` and no `BumpHeap`, and
`Func44Spec` below asks for nothing but the runtime context.  This is the
only sound reading of the code: `Func52Spec` hands the four words of the
error back without a block token, so a caller of the conversion cannot own
the buffer that the drop frees.

## Why the kind byte is abstract

`Func52Spec` leaves word 3 of the error abstract, because `func 56` reads
three bytes of its own uncommitted frame into the top of that word.  The
kind byte that `func 53` returns is the low byte of word 3 on the live
path, so it is abstract too, and both arms of `func 52` are live in the
proof.

## The stack

Two depths cover the subtree.  `redZoneDepth` is the sixteen-byte red zone
that `func 39`, `func 46` and `func 53` use below the stack pointer that
they inherit; none of the three commits a pointer of its own.  `dropDepth`
is the thirty-two bytes that the drop glue takes, which is the sixteen-byte
frame of `func 45` and the red zone of `func 46` below it.

Both fit inside the sixteen-byte frame of `func 52` and its budget of
`func49Depth`, with room to spare.  The worst path of `func 52` is the one
through `func 55`, not the one through the drop.
-/

namespace Project.RustHashMap.DropErrorContracts

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

/-! ## Stack depths -/

/-- The red zone of a body that reads and writes the sixteen bytes below
the stack pointer without committing one of its own.  Absolute `func 39`
at WAT lines 9019 to 9022, absolute `func 46` at WAT lines 9266 to 9269
and absolute `func 53` at WAT lines 9710 to 9713 all do this. -/
def redZoneDepth : Nat := 16

/-- The drop glue.  Only absolute `func 45` commits a pointer, at WAT line
9216, and only absolute `func 46` uses a red zone below it. -/
def dropDepth : Nat := 32

/-- The frame of the conversion and the drop below it stay inside the
budget of the conversion. -/
theorem dropDepth_fits : 16 + dropDepth ≤ func49Depth := by decide

/-- The frame of the conversion and the red zone of `func 53` below it
stay inside the same budget. -/
theorem redZoneDepth_fits : 16 + redZoneDepth ≤ func49Depth := by decide

/-! ## Absolute `func 54`, local `func51` -/

/-- The byte comparison.  The arguments in source order are two pointers
to one byte each.  The body loads one byte from each, masks both with 255,
and returns 1 when the bytes are equal and 0 when they differ.  It keeps no
frame and it calls nothing. -/
def Func51Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (ptrA ptrB : UInt32) (byteA byteB : UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 54 [.i32 ptrB, .i32 ptrA]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Slices.ByteSlice 0 ptrA [byteA] ∗
        Slices.ByteSlice 0 ptrB [byteB] ∗
        (RuntimeContext -∗
          Slices.ByteSlice 0 ptrA [byteA] -∗
          Slices.ByteSlice 0 ptrB [byteB] -∗
          ResumeWP [.i32 (if byteA = byteB then 1 else 0)] callerLocals stack
            code arity remainder controls calls s E Φ))

/-! ## Absolute `func 47`, local `func44` -/

/-- The free.  The arguments in source order are an unused pointer, the
buffer pointer, the alignment and the size.  The body returns at once when
the size is zero, and otherwise calls absolute `func 60`, whose body is
empty.  Either way nothing changes. -/
def Func44Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (unused ptr alignment size : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 47 [.i32 size, .i32 alignment, .i32 ptr, .i32 unused]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        (RuntimeContext -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 46`, local `func43` -/

/-- The layout of the buffer.  The arguments in source order are a
twelve-byte output slot, the buffer record, the alignment and the element
count.  The only caller fixes both the alignment and the count at 1, at WAT
lines 9059 to 9063.

The body reads the capacity at `[record]` and the pointer at `[record + 4]`
and writes three words to the slot, through the red zone at WAT lines 9288
to 9305.  The zero-count arm at WAT line 9273 is dead, because the count is
1.  The zero-capacity arm at WAT lines 9276 to 9279 is live.

The content of the slot is left abstract.  The caller reads it back and
passes it to `func 47`, which needs nothing. -/
def Func43Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out record capacity ptr : UInt32) (outBefore below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 46 [.i32 1, .i32 1, .i32 record, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp redZoneDepth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr]) ∗
        ⌜outBefore.length = 12 ∧ redZoneDepth ≤ sp.toNat ∧
          out.toNat + 12 < UInt32.size ∧ record.toNat + 8 < UInt32.size⌝ ∗
        (∀ outAfter : List UInt8, ∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp redZoneDepth below' -∗
          Slices.ByteSlice 0 out outAfter -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr]) -∗
          ⌜outAfter.length = 12⌝ -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 45`, local `func42` -/

/-- The free of the buffer.  The arguments in source order are the buffer
record, the alignment and the element size, and the only caller fixes both
of the last two at 1.

The body takes a sixteen-byte frame at WAT lines 9211 to 9216, asks
`func 46` for the layout into the top twelve bytes of that frame, and then
calls `func 47` when the middle word of the layout is not zero.  Both arms
leave the caller with what it had. -/
def Func42Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 45 [.i32 1, .i32 1, .i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 8 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 41`, local `func38` -/

/-- A forwarder that fixes the alignment and the element size at 1, at WAT
lines 9059 to 9064. -/
def Func38Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 41 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 8 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 40`, local `func37` -/

/-- A bare forwarder to `func 41`, at WAT lines 9053 to 9055. -/
def Func37Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 40 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 8 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 39`, local `func36` -/

/-- The walk over the elements of the buffer.  The argument is the buffer
record.  The body reads the pointer at `[record + 4]` and drops it, reads
the length at `[record + 8]`, and then counts from 0 up to the length in
the red zone at WAT lines 9032 to 9049.  The loop body does nothing else,
because the element type has no drop glue.

The loop is the only loop of the subtree.  It ends after `length` turns,
so the measure is `length` minus the counter. -/
def Func36Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr length : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 39 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp redZoneDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr, length]) ∗
        ⌜redZoneDepth ≤ sp.toNat ∧ record.toNat + 12 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp redZoneDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr, length]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 35`, local `func32` -/

/-- The drop of the buffer: the walk and then the free, at WAT lines 8980
to 8983. -/
def Func32Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr length : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 35 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr, length]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 12 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr, length]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 34`, local `func31` -/

/-- A bare forwarder to `func 35`, at WAT lines 8975 to 8977. -/
def Func31Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr length : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 34 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr, length]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 12 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr, length]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 37`, local `func34` -/

/-- A bare forwarder to `func 34`, at WAT lines 9008 to 9010. -/
def Func34Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr length : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 37 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr, length]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 12 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr, length]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 36`, local `func33` -/

/-- The test of the representation.  The body calls `func 37` only when
word 0 of the error is not `0x80000000`, at WAT lines 8988 to 9003.  A
simple error owns no buffer, so the other arm returns at once. -/
def Func33Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr length : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 36 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr, length]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 12 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr, length]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 38`, local `func35` -/

/-- The head of the drop glue, at WAT lines 9013 to 9015.  This is the
body that absolute `func 52` calls. -/
def Func35Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp record capacity ptr length : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 38 [.i32 record]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp dropDepth below ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [capacity, ptr, length]) ∗
        ⌜dropDepth ≤ sp.toNat ∧ record.toNat + 12 < UInt32.size⌝ ∗
        (∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp dropDepth below' -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [capacity, ptr, length]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Absolute `func 53`, local `func50` -/

/-- The read of the `ErrorKind` byte.  The argument is the sixteen-byte
error.  The body reads word 0, takes the byte at offset 4 when that word
is `0x80000000` and the byte at offset 12 otherwise, and returns it
through the red zone at WAT lines 9731 to 9743.

The returned byte is abstract, because `Func52Spec` leaves word 3 of the
error abstract. -/
def Func50Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp errPtr word0 word1 word2 word3 : UInt32) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 53 [.i32 errPtr]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp redZoneDepth below ∗
        Slices.ByteSlice 0 errPtr
          (WordCodec.u32le.serialize [word0, word1, word2, word3]) ∗
        ⌜redZoneDepth ≤ sp.toNat ∧ errPtr.toNat + 16 < UInt32.size⌝ ∗
        (∀ kindByte : UInt8, ∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp redZoneDepth below' -∗
          Slices.ByteSlice 0 errPtr
            (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
          ResumeWP [.i32 kindByte.toUInt32] callerLocals stack code arity
            remainder controls calls s E Φ))

end Project.RustHashMap.DropErrorContracts
