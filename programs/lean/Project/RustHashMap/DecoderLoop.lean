import Project.RustHashMap.DecoderDefs

/-!
# The borsh decoder: the state of the pair loop

The decoder loop is `Project.RustHashMap.Decoder.pairLoopBody`, WAT lines
612 to 801.  One step reads eight input bytes, grows the pair buffer when
the buffer is full, and appends the pair.  This file gives the state of one
step, the locals at the loop head, the measure, and the loop invariant.

`Project.RustHashMap.ReadAll` states its read loop the same way, and
`ReadAllLoop.twp_loop_iteration` shows how a body proof consumes an
invariant of this shape.

## What the loop keeps

The frame is 64 bytes.  Offsets 4, 8 and 12 hold the three words of the
pair buffer: the capacity, the pointer and the number of pairs.  Offsets 0
to 4 and 16 to 64 are the scratch of the error arms, and the accepting path
of the loop never writes them, so they are parameters here and not fields
of the state.

The number of pairs is the index of the step.  The payload of the buffer is
a function of the input and the index, so it is not a field either.

## Why the capacity cannot overflow

`func 26` doubles the capacity, and `func 27` panics when
`8 * newCap > 2147483644`.  `Project.RustHashMap.BodyContracts.Func1Spec`
needs that arm to be dead.  One fact gives it:

```
heapBase + 16 * capacity <= frontier + 4096
```

The fact holds at the loop head, because the first allocation is
`8 * min(count, 512)` bytes and `min(count, 512) <= 512`.  It survives a
grow, because the bump allocator hands out a new block of `16 * capacity`
bytes and never gives a block back.  `BumpHeap` bounds the frontier by
2147483648, so the fact bounds `16 * capacity` by 2146438175, and the panic
needs 2147483645.  The margin is 1045469 bytes.

The fact is about the allocator alone.  It says nothing about the input, so
the decoder needs no bound on the input length.  `grow_no_overflow` below
is the whole argument.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The capacity bound -/

/-- The allocator fact that the loop carries.  See the module docstring. -/
def CapacityFits (capacity : UInt32) (frontier : Nat) : Prop :=
  heapBase.toNat + 16 * capacity.toNat ≤ frontier + 4096

/-- The panic arm of `func 27` is dead under the capacity fact.  The
argument that `func 27` tests is `8 * max 4 (2 * capacity)`, and it panics
when that is more than 2147483644. -/
theorem grow_no_overflow {capacity : UInt32} {frontier : Nat}
    (hcapacity : CapacityFits capacity frontier)
    (hfrontier : frontier < 2147483648) :
    8 * max 4 (2 * capacity.toNat) ≤ 2147483644 := by
  unfold CapacityFits at hcapacity
  have hbase : heapBase.toNat = 1049568 := rfl
  rcases Nat.le_total (2 * capacity.toNat) 4 with h | h
  · rw [Nat.max_eq_left h]; omega
  · rw [Nat.max_eq_right h]; omega

/-- A capacity that fits is small enough that doubling it does not wrap a
32-bit word. -/
theorem capacity_lt {capacity : UInt32} {frontier : Nat}
    (hcapacity : CapacityFits capacity frontier)
    (hfrontier : frontier < 2147483648) :
    capacity.toNat < 134217728 := by
  unfold CapacityFits at hcapacity
  have hbase : heapBase.toNat = 1049568 := rfl
  omega

/-- The capacity fact survives one grow.  The new block takes
`16 * capacity` bytes of the heap, and the allocator never hands the same
byte out twice. -/
theorem CapacityFits.grow {capacity newCapacity : UInt32}
    {frontier newFrontier : Nat}
    (hcapacity : CapacityFits capacity frontier)
    (hnew : newCapacity.toNat = 2 * capacity.toNat)
    (hfrontier : frontier + 8 * newCapacity.toNat ≤ newFrontier) :
    CapacityFits newCapacity newFrontier := by
  unfold CapacityFits at hcapacity ⊢
  omega

/-! ## The state of one step -/

/-- The state at the head of one loop step.  `index` is the number of pairs
that the loop wrote, and it is the length word at frame offset 12. -/
structure LoopState where
  /-- The number of pairs written.  It is the word at frame offset 12. -/
  index : Nat
  /-- The capacity word at frame offset 4. -/
  capacity : UInt32
  /-- The buffer pointer at frame offset 8. -/
  buffer : UInt32
  /-- The bytes of the buffer above the pairs that the loop wrote. -/
  spare : List UInt8
  /-- The allocator cursor. -/
  storedCursor : UInt32
  /-- The allocator frontier. -/
  frontier : Nat
  /-- The allocation history. -/
  history : AllocationHistory
  /-- Local 10, the key of the step before. -/
  aux10 : UInt32
  /-- Local 11, the scratch word of the step before. -/
  aux11 : UInt32
  /-- Local 12, the value of the step before. -/
  aux12 : UInt32

/-- The bytes that the loop wrote into the buffer.  Each step writes the
key at `buffer + 8 i` and the value at `buffer + 8 i + 4`, which is the
wire order, so the payload is the input after the header. -/
def payload (bytes : List UInt8) (index : Nat) : List UInt8 :=
  (bytes.drop 4).take (8 * index)

/-- The locals at the head of one step.  Local 2 is the frame base, local 4
the tail of the `io::Error` slot, local 5 the number of unread input bytes,
local 6 the input cursor, local 7 the declared pair count, and local 9 the
byte offset of the next value. -/
def loopLocals (out hdr frame ptr len count : UInt32) (st : LoopState) :
    Locals :=
  ⟨[.i32 out, .i32 hdr],
    [.i32 frame, .i32 (UInt32.ofNat st.index), .i32 (frame + 52),
      .i32 (len - 4 - UInt32.ofNat (8 * st.index)),
      .i32 (ptr + 4 + UInt32.ofNat (8 * st.index)), .i32 count,
      .i32 st.buffer, .i32 (UInt32.ofNat (8 * st.index + 4)),
      .i32 st.aux10, .i32 st.aux11, .i32 st.aux12], []⟩

/-- The measure of the loop.  Each step writes one pair, so the number of
pairs that are left goes down. -/
def loopMeasure (count : Nat) (st : LoopState) : Nat :=
  count - st.index

/-! ## The continuation -/

/-- The continuation of the decoder at the loop head.  It is the pair of
arms of `Project.RustHashMap.BodyContracts.Func1Spec`, in the same order
and with the same binders.  The loop leaves through the first arm when the
count runs out, and through the second when a step runs out of input. -/
def DecoderPost [WasmSmallStepGS hlc Universal.State]
    (sp out hdr ptr len : UInt32) (heapId : GName)
    (bytes dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ capacity : UInt32, ∀ buffer : UInt32, ∀ payloadOut : List UInt8,
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
      pointsTo_u32 0 hdr (ptr + 4 + 8 * headerWord bytes) -∗
      pointsTo_u32 0 (hdr + 4) (len - 4 - 8 * headerWord bytes) -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      Slices.ByteSlice 0 buffer (payloadOut ++ spare) -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜payloadOut = (bytes.drop 4).take (8 * (headerWord bytes).toNat) ∧
        (headerWord bytes).toNat ≤ capacity.toNat ∧
        spare.length = 8 * (capacity.toNat - (headerWord bytes).toNat) ∧
        ((headerWord bytes).toNat = 0 → capacity = 0)⌝ -∗
      ResumeWP [] callerLocals stack code arity remainder controls
        calls s E Φ) ∧
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
        Φ (.trapped (.host OOM.trapMessage)))))

/-! ## The invariant -/

/-- The invariant at the head of one loop step.

`pad` is the four frame bytes below the vector words, and `scratch` is the
48 frame bytes above them.  The accepting path of a step writes neither, so
both are parameters.

The facts are, in order: the buffer holds the pairs and the spare bytes;
the index is below the declared count; the index is at most the capacity;
the input holds every byte that the loop read; the capacity fits the heap;
and the data segment has its full length.

The loop holds the data segment, because the short-input arm of a step
builds its message from it. -/
def LoopInv [WasmSmallStepGS hlc Universal.State]
    (sp out hdr ptr len frame : UInt32) (heapId : GName)
    (bytes outBefore below pad scratch dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (st : LoopState) : HeapIProp := iprop(
  RuntimeContext ∗
  StackPointer frame ∗
  StackBelow frame (decoderDepth - 64) below ∗
  Slices.ByteSlice 0 frame
    (pad ++
      WordCodec.u32le.serialize
        [st.capacity, st.buffer, UInt32.ofNat st.index] ++
      scratch) ∗
  Slices.ByteSlice 0 out outBefore ∗
  pointsTo_u32 0 hdr (ptr + 4 + UInt32.ofNat (8 * st.index)) ∗
  pointsTo_u32 0 (hdr + 4) (len - 4 - UInt32.ofNat (8 * st.index)) ∗
  Slices.ByteSlice 0 ptr bytes ∗
  Slices.ByteSlice 0 entryStackTop dataBytes ∗
  Slices.ByteSlice 0 st.buffer (payload bytes st.index ++ st.spare) ∗
  BumpHeap heapId st.storedCursor st.frontier st.history ∗
  Streams input output raised ∗
  ⌜st.spare.length = 8 * (st.capacity.toNat - st.index) ∧
    st.index < (headerWord bytes).toNat ∧
    st.index ≤ st.capacity.toNat ∧
    4 + 8 * st.index ≤ bytes.length ∧
    CapacityFits st.capacity st.frontier ∧
    dataBytes.length = dataSegmentSize⌝ ∗
  DecoderPost sp out hdr ptr len heapId bytes dataBytes input output raised
    callerLocals stack code arity remainder controls calls s E Φ)

end Project.RustHashMap.Decoder
