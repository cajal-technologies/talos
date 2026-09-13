import Project.RustHashMap.DecoderDefs
import Project.RustHashMap.PairGrow
import Project.RustHashMap.FrameCells

/-!
# The borsh decoder: the state of the pair loop

The decoder loop is `Project.RustHashMap.Decoder.pairLoopBody`, WAT lines
612 to 801.  One step reads eight input bytes, grows the pair buffer when
the buffer is full, and appends the pair.  This file gives the state of one
step, the locals at the loop head, the measure, the two exits of the loop,
and the loop invariant.

`Project.RustHashMap.ReadAll` states its read loop the same way, and
`ReadAllLoop.twp_loop_iteration` shows how a body proof consumes an
invariant of this shape.

## What the loop keeps

The frame is 64 bytes.  Offsets 4, 8 and 12 hold the three words of the
pair buffer: the capacity, the pointer and the number of pairs.  The loop
keeps each of the three as one owned word, because the grow writes the
first two and the append writes the third.  Offsets 0 to 4 and 16 to 64 are
the scratch of the error arms, and the accepting path of the loop never
writes them, so they are parameters here and not fields of the state.

The pair buffer is one live block of the allocator, because the grow asks
for a live block and gives a new one back.

The number of pairs is the index of the step.  The payload of the buffer is
a function of the input and the index, so it is not a field either.

## The two exits

`LoopCont` below holds the three arms that a step can take.  The first is
the fall-through: every pair is written, the loop frame goes away, and the
machine is at `okReturn`.  The second is the branch out of the error arms
of one step, which lands at the continuation of the allocation block.  The
third is the out-of-memory trap of the grow.

Neither arm says what the two programs do.  The loop proof forwards to
them, and the proof of `allocStage` fills them in.

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
open Project.RustHashMap.FrameCells
open Project.RustHashMap.VecGrow
open Project.RustHashMap.PairGrow
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

/-! ## The frame and the stack region -/

/-- The sixteen bytes at the top of the region below the frame are the
reserve that `grow_one` takes. -/
theorem StackBelow_as_reserve [WasmHeapGS Universal.State]
    (frame : UInt32) (bytes : List UInt8) :
    StackBelow frame 16 bytes ⊣⊢ StackReserve (frame - 16) bytes := .rfl

/-- The three words of the pair buffer, as the three cells that a step
writes and as the slice that the accepting return reads. -/
theorem vector_words [WasmHeapGS Universal.State]
    (frame capacity buffer length : UInt32)
    (hnowrap : frame.toNat + 16 < UInt32.size) :
    iprop(pointsTo_u32 0 (frame + 4) capacity ∗
        pointsTo_u32 0 (frame + 8) buffer ∗
        pointsTo_u32 0 (frame + 12) length) ⊣⊢
      Slices.ByteSlice 0 (frame + 4)
        (WordCodec.u32le.serialize [capacity, buffer, length]) := by
  have h8 : frame + 4 + 4 = frame + 8 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  have h12 : frame + 8 + 4 = frame + 12 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  have hb4 : (frame + 4).toNat = frame.toNat + 4 :=
    Slices.byteOffset_toNat frame 4 (by omega)
  constructor
  · iintro ⟨Hcapacity, Hbuffer, Hlength⟩
    iapply ByteSlice_of_cells (frame + 4) [capacity, buffer, length]
      (by simp only [List.length_cons, List.length_nil]; omega)
    isimp only [arrayAt, h8, h12]
    iframe Hcapacity Hbuffer Hlength
  · iintro Hslice
    ihave Harray := cells_of_ByteSlice (frame + 4) [capacity, buffer, length]
      $$ Hslice
    isimp only [arrayAt, h8, h12] at Harray
    icases Harray with ⟨Hcapacity, Hbuffer, Hlength, _Hemp⟩
    iframe Hcapacity Hbuffer
    iexact Hlength

/-! ## The addresses of one step -/

/-- A byte offset eight bytes above another. -/
private theorem addr_step8 (ptr : UInt32) (pos : Nat) :
    ptr + UInt32.ofNat (pos + 8) = ptr + UInt32.ofNat pos + 8 := by
  rw [UInt32.ofNat_add, ← UInt32.add_assoc]
  rfl

/-- The input cursor of the next step. -/
theorem loop_cursor_step (ptr : UInt32) (index : Nat) :
    ptr + UInt32.ofNat (4 + 8 * index) + 8
      = ptr + UInt32.ofNat (4 + 8 * (index + 1)) := by
  rw [show 4 + 8 * (index + 1) = 4 + 8 * index + 8 from by omega]
  exact (addr_step8 ptr (4 + 8 * index)).symm

/-- The number of unread input bytes of the next step. -/
theorem loop_remaining_step (len : UInt32) (index : Nat) :
    len - UInt32.ofNat (4 + 8 * index) - 8
      = len - UInt32.ofNat (4 + 8 * (index + 1)) := by
  have h8 : (8 : UInt32) = UInt32.ofNat 8 := rfl
  rw [h8, sub_sub_ofNat,
    show 4 + 8 * index + 8 = 4 + 8 * (index + 1) from by omega]

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
  /-- The allocation that holds the pair buffer. -/
  allocationId : Nat
  /-- Every byte of the pair buffer, written and spare. -/
  blockBytes : List UInt8
  /-- The stack region below the frame.  The grow writes its top sixteen
  bytes. -/
  below : List UInt8
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
      .i32 (len - UInt32.ofNat (4 + 8 * st.index)),
      .i32 (ptr + UInt32.ofNat (4 + 8 * st.index)), .i32 count,
      .i32 st.buffer, .i32 (UInt32.ofNat (8 * st.index + 4)),
      .i32 st.aux10, .i32 st.aux11, .i32 st.aux12], []⟩

/-- The measure of the loop.  Each step writes one pair, so the number of
pairs that are left goes down. -/
def loopMeasure (count : Nat) (st : LoopState) : Nat :=
  count - st.index

/-! ## The three arms of the loop -/

/-- The continuation of the loop.  The first arm is the fall-through of the
last step, with the loop frame gone and the machine at `okReturn`.  The
second arm is the branch that both error paths of a step take, which lands
at the continuation of the allocation block.  The third arm is the
out-of-memory trap of the grow. -/
def LoopCont [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore pad scratch dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value)
    (loopControls errorControls : List ControlFrame)
    (errorCont : Program) (errorBelow : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ capacity : UInt32, ∀ buffer : UInt32, ∀ allocationId : Nat,
      ∀ blockBytes : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory,
      ∀ l10' : Value, ∀ l11' : Value, ∀ l12' : Value,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame (decoderDepth - 64) below' -∗
      Slices.ByteSlice 0 frame pad -∗
      pointsTo_u32 0 (frame + 4) capacity -∗
      pointsTo_u32 0 (frame + 8) buffer -∗
      pointsTo_u32 0 (frame + 12) count -∗
      Slices.ByteSlice 0 (frame + 16) scratch -∗
      Slices.ByteSlice 0 out outBefore -∗
      pointsTo_u32 0 hdr (ptr + UInt32.ofNat (4 + 8 * count.toNat)) -∗
      pointsTo_u32 0 (hdr + 4) (len - UInt32.ofNat (4 + 8 * count.toNat)) -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      LiveBlock heapId allocationId buffer (pairBlock capacity.toNat)
        blockBytes -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜count.toNat ≤ capacity.toNat ∧ 2 ≤ capacity.toNat ∧
        4 + 8 * count.toNat ≤ bytes.length ∧
        blockBytes.take (8 * count.toNat) = payload bytes count.toNat⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 count, .i32 (frame + 52),
                .i32 (len - UInt32.ofNat (4 + 8 * count.toNat)),
                .i32 (ptr + UInt32.ofNat (4 + 8 * count.toNat)), .i32 count,
                .i32 buffer, .i32 (UInt32.ofNat (8 * count.toNat + 4)),
                l10', l11', l12'],
            []⟩,
            okReturn, arity, remainder, loopControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
  ((∀ word0 : UInt32, ∀ word1 : UInt32, ∀ word2 : UInt32,
      ∀ word3 : UInt32,
      ∀ hdrPtr : UInt32, ∀ hdrLen : UInt32, ∀ capacity : UInt32,
      ∀ buffer : UInt32, ∀ length : UInt32,
      ∀ scratchAfter : List UInt8, ∀ below' : List UInt8,
      ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
      ∀ history' : AllocationHistory,
      ∀ l3' : Value, ∀ l5' : Value, ∀ l6' : Value, ∀ l9' : Value,
      ∀ l10' : Value, ∀ l12' : Value,
      RuntimeContext -∗ StackPointer frame -∗
      StackBelow frame (decoderDepth - 64) below' -∗
      Slices.ByteSlice 0 frame pad -∗
      pointsTo_u32 0 (frame + 4) capacity -∗
      pointsTo_u32 0 (frame + 8) buffer -∗
      pointsTo_u32 0 (frame + 12) length -∗
      Slices.ByteSlice 0 (frame + 16)
        (WordCodec.u32le.serialize [word0, word1, word2, word3] ++
          scratchAfter) -∗
      Slices.ByteSlice 0 out outBefore -∗
      pointsTo_u32 0 hdr hdrPtr -∗
      pointsTo_u32 0 (hdr + 4) hdrLen -∗
      Slices.ByteSlice 0 ptr bytes -∗
      Slices.ByteSlice 0 entryStackTop dataBytes -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams input output raised -∗
      ⌜word0 ≠ okTag ∧ scratchAfter.length = 32⌝ -∗
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3', .i32 (frame + 52), l5', l6', .i32 count,
                .i32 buffer, l9', l10', .i32 word0, l12'],
            errorBelow⟩,
            errorCont, arity, remainder, errorControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }]) ∧
    (∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage)))))

/-! ## The invariant -/

/-- The invariant at the head of one loop step.

`pad` is the four frame bytes below the vector words, and `scratch` is the
48 frame bytes above them.  The accepting path of a step writes neither, so
both are parameters.

The facts are, in order: the index is below the declared count; the index
is at most the capacity; the capacity is two pairs or more, which the grow
asks for; the input holds every byte that the loop read; the written part
of the buffer is the payload of the input; and the capacity fits the heap.

The loop holds the data segment, because the short-input arm of a step
builds its message from it. -/
def LoopInv [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore pad scratch dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value)
    (loopControls errorControls : List ControlFrame)
    (errorCont : Program) (errorBelow : List Value)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (st : LoopState) : HeapIProp := iprop(
  RuntimeContext ∗
  StackPointer frame ∗
  StackBelow frame (decoderDepth - 64) st.below ∗
  Slices.ByteSlice 0 frame pad ∗
  pointsTo_u32 0 (frame + 4) st.capacity ∗
  pointsTo_u32 0 (frame + 8) st.buffer ∗
  pointsTo_u32 0 (frame + 12) (UInt32.ofNat st.index) ∗
  Slices.ByteSlice 0 (frame + 16) scratch ∗
  Slices.ByteSlice 0 out outBefore ∗
  pointsTo_u32 0 hdr (ptr + UInt32.ofNat (4 + 8 * st.index)) ∗
  pointsTo_u32 0 (hdr + 4) (len - UInt32.ofNat (4 + 8 * st.index)) ∗
  Slices.ByteSlice 0 ptr bytes ∗
  Slices.ByteSlice 0 entryStackTop dataBytes ∗
  LiveBlock heapId st.allocationId st.buffer (pairBlock st.capacity.toNat)
    st.blockBytes ∗
  BumpHeap heapId st.storedCursor st.frontier st.history ∗
  Streams input output raised ∗
  ⌜st.index < count.toNat ∧
    st.index ≤ st.capacity.toNat ∧
    2 ≤ st.capacity.toNat ∧
    4 + 8 * st.index ≤ bytes.length ∧
    st.blockBytes.take (8 * st.index) = payload bytes st.index ∧
    CapacityFits st.capacity st.frontier⌝ ∗
  LoopCont out hdr ptr len frame count heapId bytes outBefore pad scratch
    dataBytes input output raised arity remainder loopControls errorControls
    errorCont errorBelow calls s E Φ)

end Project.RustHashMap.Decoder
