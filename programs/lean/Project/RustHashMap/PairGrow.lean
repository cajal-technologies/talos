import Project.RustHashMap.VecGrow

/-!
# The grow layer of the pair buffer

The borsh decoder keeps its pairs in a `Vec<(u32, u32)>`.  When that vector
is full, `Project.RustHashMap.Decoder.growBody` calls its generated
`grow_one`, absolute `func 26`.  That function calls the generic
`finish_grow`, absolute `func 27`, which calls the allocator.  This module
states the contracts of the two functions.

`Project.RustHashMap.VecGrow` states the same pair of contracts for the
byte vector of the five drivers.  The two layers differ in three ways:

* one element is eight bytes, not one, and the alignment is 4, not 1;
* absolute `func 27` takes the element size and the alignment as operands,
  so `Func24Spec` is generic in both.  Absolute `func 13`, the grow of
  `collect_entries`, is its other caller;
* the new capacity is `max (2 * capacity) 4`, not `max (2 * capacity) 8`.

Absolute `func 27` reports a capacity overflow through the result slot, and
absolute `func 26` turns that report into `call 99` and `unreachable`.
`Func23Spec` must exclude that arm, so it asks for
`8 * max (2 * capacity) 4 <= 2147483644`.
`Project.RustHashMap.Decoder.grow_no_overflow` gives that bound from the
allocator fact that the decoder loop carries.

The null-pointer arm of absolute `func 27` is dead as well.  The bump
allocator of this program traps through `talos.oom` rather than returning
zero, so `Func55Spec` and `Func58Spec` have no null result.
-/

namespace Project.RustHashMap.PairGrow

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open scoped Wasm.SmallStep.Outcome

/-! ## The witnesses of one grow -/

/-- The storage that a grow starts from: no block, or one live block. -/
inductive FinishSource where
  | empty
  | allocated (allocationId : Nat) (allBytes : List UInt8)

/-- The ownership of a grow source.  `oldLayout` is the layout of the block
that the caller gives up. -/
def FinishSourceOwn [WasmHeapGS Universal.State]
    (heapId : GName) (oldCapacity oldPtr : UInt32)
    (oldLayout : AllocLayout) : FinishSource → HeapIProp
  | .empty => iprop(⌜oldCapacity = 0⌝)
  | .allocated allocationId allBytes => iprop(
      ⌜0 < oldCapacity.toNat ∧ oldLayout.Valid⌝ ∗
      LiveBlock heapId allocationId oldPtr oldLayout allBytes)

/-- The allocation history after a grow from `source`. -/
def finishHistory (history : AllocationHistory) (source : FinishSource)
    (oldPtr : UInt32) (oldLayout : AllocLayout) (newPtr : UInt32)
    (newLayout : AllocLayout) : AllocationHistory :=
  match source with
  | .empty => history.allocate newPtr newLayout
  | .allocated allocationId _ =>
      history.reallocate allocationId oldPtr oldLayout newPtr newLayout

/-- The old block is a prefix of the new block after a grow. -/
def finishCopied (source : FinishSource) (oldLayout : AllocLayout)
    (newBytes : List UInt8) : Prop :=
  match source with
  | .empty => True
  | .allocated _ allBytes => newBytes.take oldLayout.size = allBytes

/-- The twelve result bytes of a successful `finish_grow`: the tag `0`, the
new pointer, and the size of the new block in bytes. -/
def finishResultBytes (newPtr newSize : UInt32) : List UInt8 :=
  WordCodec.u32le.serialize [0, newPtr, newSize]

theorem finishResultBytes_length (newPtr newSize : UInt32) :
    (finishResultBytes newPtr newSize).length = 12 := by
  unfold finishResultBytes
  rw [WordCodec.u32le_serialize_length]
  rfl

/-! ## The contract of `finish_grow` -/

/-- The result continuation of absolute `func 27`.  Arithmetic success
carries a normal arm and an OOM arm, because the modular proof does not own
the physical memory cap.  Arithmetic OOM carries only the terminal arm.
Both OOM arms hand back the resources of the call, with the OOM marker
set. -/
def FinishContinuation [WasmSmallStepGS hlc Universal.State]
    (result oldCapacity oldPtr : UInt32)
    (oldLayout newLayout : AllocLayout) (source : FinishSource)
    (resultBefore : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ newBytes : List UInt8,
          RuntimeContext -∗
          Slices.ByteSlice 0 result
            (finishResultBytes newPtr (UInt32.ofNat newLayout.size)) -∗
          BumpHeap heapId finish finish.toNat
            (finishHistory history source oldPtr oldLayout newPtr
              newLayout) -∗
          LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
          ⌜finishCopied source oldLayout newBytes⌝ -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∧
        (Slices.ByteSlice 0 result resultBefore -∗
          FinishSourceOwn heapId oldCapacity oldPtr oldLayout source -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      Slices.ByteSlice 0 result resultBefore -∗
      FinishSourceOwn heapId oldCapacity oldPtr oldLayout source -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func24`, absolute index 27, the generic `finish_grow`.  The
operands are the result slot, the old capacity, the old pointer, the new
capacity, the alignment, and the element size, in machine order.

The two error arms of the body are dead under this precondition.  The
64-bit product does not overflow, because `newLayout.Valid` bounds the
product by `UInt32.size`.  The signed guard holds, because `newLayout.Valid`
bounds the product by `2147483648 - alignment`. -/
def Func24Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (result oldCapacity oldPtr newCapacity alignment elemSize : UInt32)
    (oldLayout newLayout : AllocLayout) (source : FinishSource)
    (resultBefore : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 27
      [.i32 elemSize, .i32 alignment, .i32 newCapacity, .i32 oldPtr,
        .i32 oldCapacity, .i32 result]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Slices.ByteSlice 0 result resultBefore ∗
        FinishSourceOwn heapId oldCapacity oldPtr oldLayout source ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜resultBefore.length = 12 ∧
          result.toNat + 12 < UInt32.size ∧
          oldLayout.size = elemSize.toNat * oldCapacity.toNat ∧
          newLayout.size = elemSize.toNat * newCapacity.toNat ∧
          oldLayout.alignment = alignment.toNat ∧
          newLayout.alignment = alignment.toNat ∧
          (alignment.toNat = 1 ∨ alignment.toNat = 4) ∧
          newLayout.Valid ∧
          oldLayout.size < newLayout.size⌝ ∗
        FinishContinuation result oldCapacity oldPtr oldLayout newLayout
          source resultBefore heapId storedCursor frontier history input
          output raised callerLocals stack code arity remainder controls
          calls s E Φ)

/-! ## The pair buffer -/

/-- The capacity that absolute `func 26` selects. -/
def pairPushCapacity (capacity : Nat) : Nat :=
  max (2 * capacity) 4

/-- The layout of a block of `capacity` pairs.  One pair is eight bytes and
the alignment is four. -/
def pairBlock (capacity : Nat) : AllocLayout :=
  { size := 8 * capacity, alignment := 4 }

/-- The two-word header of the pair buffer: the capacity at `header` and
the pointer at `header + 4`.  The length word at `header + 8` stays with
the caller, because absolute `func 26` never reads it. -/
def PairHeader [WasmHeapGS Universal.State]
    (header capacity ptr : UInt32) : HeapIProp :=
  iprop(pointsTo_u32 0 header capacity ∗
    pointsTo_u32 0 (header + 4) ptr)

/-- The reserve after a normal `grow_one`.  The function never touches the
first four bytes.  `finish_grow` overwrites the other twelve. -/
def pairReserveShadow (shadow : List UInt8) (newPtr newSize : UInt32) :
    List UInt8 :=
  shadow.take 4 ++ finishResultBytes newPtr newSize

theorem pairReserveShadow_length (shadow : List UInt8)
    (newPtr newSize : UInt32) (hlength : shadow.length = 16) :
    (pairReserveShadow shadow newPtr newSize).length = 16 := by
  unfold pairReserveShadow
  rw [List.length_append, List.length_take, finishResultBytes_length]
  simp [hlength]

/-! ## The contract of `grow_one` -/

/-- The result continuation of absolute `func 26`.  The frame of the
function is the sixteen bytes below the stack pointer `sp`.  A normal
return restores `sp`, and the header holds the new capacity and the new
pointer.  The final history is hidden, because no caller depends on it.

The normal arm reports `frontier + newLayout.size ≤ finish.toNat`.  The
decoder loop needs that fact to carry
`Project.RustHashMap.Decoder.CapacityFits` across the grow. -/
def PairGrowContinuation [WasmSmallStepGS hlc Universal.State]
    (sp header capacity ptr : UInt32) (source : FinishSource)
    (shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let newCapacityNat := pairPushCapacity capacity.toNat
  let newLayout : AllocLayout := pairBlock newCapacityNat
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ newBytes : List UInt8, ∀ finalHistory : AllocationHistory,
          RuntimeContext -∗
          StackPointer sp -∗
          StackReserve (sp - 16)
            (pairReserveShadow shadow newPtr
              (UInt32.ofNat newLayout.size)) -∗
          PairHeader header (UInt32.ofNat newCapacityNat) newPtr -∗
          LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
          BumpHeap heapId finish finish.toNat finalHistory -∗
          ⌜finishCopied source (pairBlock capacity.toNat) newBytes ∧
            frontier + newLayout.size ≤ finish.toNat⌝ -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∧
        (StackPointer (sp - 16) -∗
          StackReserve (sp - 16) shadow -∗
          PairHeader header capacity ptr -∗
          FinishSourceOwn heapId capacity ptr (pairBlock capacity.toNat)
            source -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      StackPointer (sp - 16) -∗
      StackReserve (sp - 16) shadow -∗
      PairHeader header capacity ptr -∗
      FinishSourceOwn heapId capacity ptr (pairBlock capacity.toNat)
        source -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func23`, absolute index 26, the generated `grow_one` of the pair
buffer.  The one operand is the address of the two-word header.  The
capacity bound excludes the generated capacity-overflow edge. -/
def Func23Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (header sp capacity ptr : UInt32) (source : FinishSource)
    (shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 26 [.i32 header]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackReserve (sp - 16) shadow ∗
        PairHeader header capacity ptr ∗
        FinishSourceOwn heapId capacity ptr (pairBlock capacity.toNat)
          source ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜16 ≤ sp.toNat ∧ header.toNat + 8 < UInt32.size ∧
          8 * pairPushCapacity capacity.toNat ≤ 2147483644⌝ ∗
        PairGrowContinuation sp header capacity ptr source shadow heapId
          storedCursor frontier history input output raised callerLocals
          stack code arity remainder controls calls s E Φ)

end Project.RustHashMap.PairGrow
