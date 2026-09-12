import Project.RustHashMap.BodyContracts

/-!
# Call contracts of the `borsh::io::Error::new` chain

`Project.RustHashMap.BodyContracts.Func52Spec` states the contract of
absolute `func 55`, which is `borsh::io::Error::new`.  That function is
the head of a chain of nine bodies.  This module states the contracts of
the eight bodies below it.

## The shape of the chain

Every body of the chain has exactly one live caller, so the chain is a
line:

```
55 -> 42 -> 43 -> 57 -> 51 -> 48 -> 50 -> 44 -> { 33, 58 }
55 -> 56
```

The two leaves are proved already.  Absolute `func 33` is a bare `return`
at WAT line 8972, and `Project.RustHashMap.Func30Proof` proves it.
Absolute `func 58` is the bump allocator, and
`Project.RustHashMap.Func55Proof` proves it against
`Project.RustHashMap.AllocatorContracts.Func55Spec`.  The chain therefore
rests on proved ground and adds no new leaf.

## Two dead arms

`func 48` picks between `func 49` and `func 50` on bit 0 of its third
argument at WAT line 9426.  Its only caller, `func 51`, passes the folded
constant `0 and 1` at WAT lines 9593 to 9596.  So `func 49` is dead, and
the subtree below it is dead with it.

`func 44` picks between absolute `func 58` and absolute `func 62` on its
fourth argument at WAT line 9120.  Its only live caller, `func 50`,
passes the constant 0 at WAT lines 9559 and 9560.  So the `func 62` arm
is dead and the chain never reaches the zeroed allocator.

The contracts below fix both constants instead of taking them as
parameters.  A parameter that no caller varies buys nothing and costs a
case split in the body proof.

## Two more dead arms

`func 48` reads eight data-segment bytes at 1049128 on its capacity
overflow arm at WAT lines 9396 to 9401, and `func 44` reads the same
eight bytes on its null-pointer arm at WAT lines 9157 to 9162.  Both arms
are dead.  The overflow arm needs `msgLen > 2147483647`, which
`Func52Spec` excludes, and the null arm needs a null result from
absolute `func 58`, which `Allocator.LiveBlock` excludes because it
carries `ptr != 0`.

This matters for ownership.  The window [1049128, 1049136) is disjoint
from the eighteen message bytes at [1049107, 1049125) that
`Project.RustHashMap.DriverTail.DriverTailSpec` lends, so no contract in
this file asks for more of the data segment than the message itself.

## Why the length is positive

`Func52Spec` requires `0 < msgLen`.  Three bodies carry a zero-length arm
that the bound kills at once:

* `func 48` at WAT line 9393 returns without calling `func 50`;
* `func 44` at WAT lines 9124 to 9130 returns the alignment as a
  dangling pointer;
* `func 57` at WAT lines 9852 to 9857 skips the `memory.copy`.

## What the chain computes

`func 57` allocates `msgLen` bytes at alignment 1 and copies the message
into them.  Its twelve-byte record is `(capacity, pointer, length)`.  The
capacity is the requested length itself, not a rounded one, because
`func 48` returns its own `count` argument at WAT line 9501.  `func 43`
and `func 42` pass the record up without change.

`func 56` packs the record and the `ErrorKind` byte into the sixteen-byte
slot.  Word 3 is not the kind alone.  `func 56` writes the kind with
`i32.store8` at WAT line 9795 and reads the whole word back with
`i64.load offset=24` at WAT line 9806, so the top three bytes of word 3
are the bytes at `frame + 29` to `frame + 31`.  `func 56` does not commit
the stack pointer, so its frame covers the retired frame of `func 43`,
and those three bytes are the top three bytes of the length.  `Func53Spec`
therefore leaves word 3 abstract.  `Func52Spec` quantifies word 3 as
well, so nothing above the chain needs the value.
-/

namespace Project.RustHashMap.ErrorNewContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open scoped Wasm.SmallStep.Outcome

/-! ## Stack depths

Each depth is the frame of the body plus the depth of its deepest live
callee.  The leaves `func 33` and `func 58` take no frame, so the chain
ends at `func 44`. -/

/-- Absolute `func 44`.  Own frame 32 bytes, at WAT lines 9104 to 9109. -/
def func41Depth : Nat := 32

/-- Absolute `func 50`.  Own frame 16 bytes, above `func 44`. -/
def func47Depth : Nat := 48

/-- Absolute `func 48`.  Own frame 48 bytes, above `func 50`. -/
def func45Depth : Nat := 96

/-- Absolute `func 51`.  Own frame 16 bytes, above `func 48`. -/
def func48Depth : Nat := 112

/-- Absolute `func 57`.  Own frame 16 bytes, above `func 51`. -/
def func54Depth : Nat := 128

/-- Absolute `func 43`.  Own frame 16 bytes, above `func 57`. -/
def func40Depth : Nat := 144

/-- Absolute `func 42`.  It keeps no frame and forwards to `func 43`. -/
def func39Depth : Nat := 144

/-- Absolute `func 56`.  A 32-byte red zone below the stack pointer that
it inherits.  It commits no stack pointer of its own. -/
def func53Depth : Nat := 32

/-- The allocate branch of `func 55` uses its whole budget.  `func 55`
takes 16 bytes and calls `func 42`. -/
theorem errorNewDepth_allocate : errorNewDepth = 16 + func39Depth := by decide

/-- The pack branch of `func 55` stays inside the same budget. -/
theorem errorNewDepth_pack : 16 + func53Depth ≤ errorNewDepth := by decide

/-! ## The message buffer -/

/-- The layout of the message buffer: `msgLen` bytes at alignment 1.
`func 51` passes the alignment 1 and the element size 1 at WAT lines 9597
and 9598, so the chain allocates at no other alignment and at no other
element size. -/
def messageLayout (msgLen : UInt32) : AllocLayout :=
  { size := msgLen.toNat, alignment := 1 }

/-- The layout that the chain builds is valid for the allocator whenever
the length is positive and within `isize::MAX`. -/
theorem messageLayout_valid (msgLen : UInt32)
    (hpos : 0 < msgLen.toNat) (hle : msgLen.toNat ≤ 2147483647) :
    (messageLayout msgLen).Valid := by
  simp only [AllocLayout.Valid, messageLayout]
  refine ⟨hpos, by decide, ⟨0, by decide⟩, by decide, by omega, ?_, by decide⟩
  simp only [UInt32.size]
  omega

/-! ## Absolute `func 44`, local `func41` -/

/-- The allocate leaf of the chain.  The arguments in source order are
the eight-byte output slot, the alignment, the size, and a zero-fill
flag.  The chain fixes the alignment at 1 and the flag at 0.

The body calls absolute `func 33`, which is empty, and then absolute
`func 58` at WAT line 9136.  It writes the returned pointer to `[out]`
and the size to `[out + 4]` at WAT lines 9187 to 9202.  The null check at
WAT line 9150 is dead, because `LiveBlock` carries `ptr != 0`. -/
def Func41Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out size : UInt32)
    (heapId : GName) (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 44 [.i32 0, .i32 size, .i32 1, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func41Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 8 ∧ func41Depth ≤ sp.toNat ∧
          out.toNat + 8 < UInt32.size ∧
          0 < size.toNat ∧ size.toNat ≤ 2147483647⌝ ∗
        ((∀ ptr : UInt32, ∀ blockId : Nat, ∀ contents : List UInt8,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func41Depth below' -∗
            Slices.ByteSlice 0 out (WordCodec.u32le.serialize [ptr, size]) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            LiveBlock heapId blockId ptr (messageLayout size) contents -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## Absolute `func 50`, local `func47` -/

/-- A forwarder to `func 44`.  The arguments in source order are the
eight-byte output slot, an unused pointer, the alignment, and the size.
The body drops the second argument, calls `func 44` at WAT line 9567, and
copies the two result words at WAT lines 9568 to 9577.  The result is the
result of `func 44`. -/
def Func47Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out unused size : UInt32)
    (heapId : GName) (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 50 [.i32 size, .i32 1, .i32 unused, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func47Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 8 ∧ func47Depth ≤ sp.toNat ∧
          out.toNat + 8 < UInt32.size ∧
          0 < size.toNat ∧ size.toNat ≤ 2147483647⌝ ∗
        ((∀ ptr : UInt32, ∀ blockId : Nat, ∀ contents : List UInt8,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func47Depth below' -∗
            Slices.ByteSlice 0 out (WordCodec.u32le.serialize [ptr, size]) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            LiveBlock heapId blockId ptr (messageLayout size) contents -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## Absolute `func 48`, local `func45` -/

/-- The layout and overflow check.  The arguments in source order are the
twelve-byte output slot, the element count, a zero-fill flag, the
alignment, and the element size.  The chain fixes the flag at 0 and both
the alignment and the element size at 1.

The body multiplies the count by the element size in 64 bits at WAT lines
9334 to 9349, rejects a product that does not fit, and rejects a size
above `0x80000000` minus the alignment.  With an element size of 1 and an
alignment of 1 the surviving test is `count <= 0x7fffffff`, which the
precondition gives.  The success arm writes the flag 0, the count, and
the pointer at WAT lines 9497 to 9508. -/
def Func45Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out count : UInt32)
    (heapId : GName) (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 48 [.i32 1, .i32 1, .i32 0, .i32 count, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func45Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 12 ∧ func45Depth ≤ sp.toNat ∧
          out.toNat + 12 < UInt32.size ∧
          0 < count.toNat ∧ count.toNat ≤ 2147483647⌝ ∗
        ((∀ ptr : UInt32, ∀ blockId : Nat, ∀ contents : List UInt8,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func45Depth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [0, count, ptr]) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            LiveBlock heapId blockId ptr (messageLayout count) contents -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## Absolute `func 51`, local `func48` -/

/-- The `RawVec` allocate.  The arguments in source order are the
eight-byte output slot, the element count, the alignment, and the element
size.  The chain fixes both the alignment and the element size at 1.

The body calls `func 48` at WAT line 9599 and tests bit 0 of the result
flag at WAT lines 9601 to 9606.  The error arm runs `call 99` and
`unreachable` at WAT lines 9611 and 9612, which is a bare trap and not
the `talos.oom` trap.  The precondition makes that arm dead.  The success
arm writes the count and the pointer at WAT lines 9633 to 9638.

The store of -1 at WAT lines 9624 to 9626 lands at `frame + 12`, which no
instruction reads again. -/
def Func48Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out count : UInt32)
    (heapId : GName) (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 51 [.i32 1, .i32 1, .i32 count, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func48Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 8 ∧ func48Depth ≤ sp.toNat ∧
          out.toNat + 8 < UInt32.size ∧
          0 < count.toNat ∧ count.toNat ≤ 2147483647⌝ ∗
        ((∀ ptr : UInt32, ∀ blockId : Nat, ∀ contents : List UInt8,
            ∀ below' : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func48Depth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [count, ptr]) -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            LiveBlock heapId blockId ptr (messageLayout count) contents -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## Absolute `func 57`, local `func54` -/

/-- The body that builds the `String`.  The arguments in source order are
the twelve-byte output slot, the message pointer, and the message length.

The body calls `func 51` at WAT line 9838, writes the capacity, the
pointer, and the length 0 at WAT lines 9839 to 9851, and then copies the
message with `memory.copy` at WAT line 9874 and overwrites the length at
WAT lines 9876 to 9878.  The copy reads the message, so the contract
takes those bytes and gives them back unchanged.

The record that the body leaves is `(capacity, pointer, length)` with the
capacity and the length both equal to `msgLen`.  The block now holds the
message, so the contract returns a `LiveBlock` over `msgBytes` and not
over abstract contents. -/
def Func54Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out msgPtr msgLen : UInt32)
    (heapId : GName) (outBefore below msgBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 57 [.i32 msgLen, .i32 msgPtr, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func54Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 msgPtr msgBytes ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 12 ∧ func54Depth ≤ sp.toNat ∧
          out.toNat + 12 < UInt32.size ∧
          0 < msgLen.toNat ∧ msgLen.toNat ≤ 2147483647 ∧
          msgBytes.length = msgLen.toNat⌝ ∗
        ((∀ ptr : UInt32, ∀ blockId : Nat, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func54Depth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [msgLen, ptr, msgLen]) -∗
            Slices.ByteSlice 0 msgPtr msgBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            LiveBlock heapId blockId ptr (messageLayout msgLen) msgBytes -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## Absolute `func 43`, local `func40` -/

/-- A forwarder to `func 57`.  The arguments in source order are the
twelve-byte output slot, the message pointer, and the message length.
The body calls `func 57` at WAT line 9087 and copies the twelve result
bytes at WAT lines 9088 to 9098.  The result is the result of
`func 57`. -/
def Func40Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out msgPtr msgLen : UInt32)
    (heapId : GName) (outBefore below msgBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 43 [.i32 msgLen, .i32 msgPtr, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func40Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 msgPtr msgBytes ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 12 ∧ func40Depth ≤ sp.toNat ∧
          out.toNat + 12 < UInt32.size ∧
          0 < msgLen.toNat ∧ msgLen.toNat ≤ 2147483647 ∧
          msgBytes.length = msgLen.toNat⌝ ∗
        ((∀ ptr : UInt32, ∀ blockId : Nat, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func40Depth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [msgLen, ptr, msgLen]) -∗
            Slices.ByteSlice 0 msgPtr msgBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            LiveBlock heapId blockId ptr (messageLayout msgLen) msgBytes -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## Absolute `func 42`, local `func39` -/

/-- A forwarder to `func 43` that keeps no frame.  The arguments in
source order are the twelve-byte output slot, the message pointer, the
message length, and a fourth argument that the body drops: it pushes only
arguments 0, 1 and 2 before `call 43` at WAT lines 9068 to 9071.

The dropped argument is the static pointer 1049164 at every call site.
The contract keeps it free, because the body reads no part of it.  No
data-segment ownership is needed for it. -/
def Func39Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out msgPtr msgLen unused : UInt32)
    (heapId : GName) (outBefore below msgBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 42 [.i32 unused, .i32 msgLen, .i32 msgPtr, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func39Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 msgPtr msgBytes ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜outBefore.length = 12 ∧ func39Depth ≤ sp.toNat ∧
          out.toNat + 12 < UInt32.size ∧
          0 < msgLen.toNat ∧ msgLen.toNat ≤ 2147483647 ∧
          msgBytes.length = msgLen.toNat⌝ ∗
        ((∀ ptr : UInt32, ∀ blockId : Nat, ∀ below' : List UInt8,
            ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
            ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp func39Depth below' -∗
            Slices.ByteSlice 0 out
              (WordCodec.u32le.serialize [msgLen, ptr, msgLen]) -∗
            Slices.ByteSlice 0 msgPtr msgBytes -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            LiveBlock heapId blockId ptr (messageLayout msgLen) msgBytes -∗
            Streams input output raised -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
          (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

/-! ## Absolute `func 56`, local `func53` -/

/-- The pack.  The arguments in source order are the sixteen-byte output
slot, the `ErrorKind` byte, and the twelve-byte record.

The body calls nothing, so the contract has one arm and touches neither
the bump heap nor the streams.  It takes a 32-byte red zone below the
stack pointer that it inherits, because it computes its frame at WAT
lines 9789 to 9792 and never commits it.

Word 3 stays abstract.  The body writes the kind into the low byte with
`i32.store8` at WAT line 9795 and reads the whole word back at WAT line
9806, so the top three bytes come from the red zone and depend on the
caller.  No caller of `func 55` reads word 3. -/
def Func53Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp out kind record : UInt32)
    (word0 word1 word2 : UInt32) (outBefore below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 56 [.i32 record, .i32 kind, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp func53Depth below ∗
        Slices.ByteSlice 0 out outBefore ∗
        Slices.ByteSlice 0 record
          (WordCodec.u32le.serialize [word0, word1, word2]) ∗
        ⌜outBefore.length = 16 ∧ func53Depth ≤ sp.toNat ∧
          out.toNat + 16 < UInt32.size ∧
          record.toNat + 12 < UInt32.size⌝ ∗
        (∀ word3 : UInt32, ∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp func53Depth below' -∗
          Slices.ByteSlice 0 out
            (WordCodec.u32le.serialize [word0, word1, word2, word3]) -∗
          Slices.ByteSlice 0 record
            (WordCodec.u32le.serialize [word0, word1, word2]) -∗
          ResumeWP [] callerLocals stack code arity remainder controls
            calls s E Φ))

end Project.RustHashMap.ErrorNewContracts
