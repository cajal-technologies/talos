import Project.RustHashMap.PairGrow
import Project.RustHashMap.BodyContracts

/-!
# The contract of `RawVec::grow_amortized`

Absolute `func 13`, local `func10`, is the generic
`alloc::raw_vec::RawVec::grow_amortized` of the hash map program.  It is
WAT lines 2555 to 2634 of
`programs/rust/build/rust_hash_map/program.wat`.  Two bodies call it:

* absolute `func 7`, `sorted_entries`, at WAT 1211 to 1215, with the
  element size 8 and the alignment 4;
* absolute `func 8`, the reply writer, at WAT 1384 to 1389 and 1421 to
  1426, with the element size 1 and the alignment 1.

`Project.RustHashMap.PairGrow.Func23Spec` states the same layer for
absolute `func 26`, the `grow_one` of the pair buffer.  The two differ in
one way only: absolute `func 26` fixes the element size and the alignment
and absolute `func 13` takes both as operands, in the same way that
absolute `func 27` does.  So this contract reuses `FinishSource`,
`FinishSourceOwn`, `finishHistory` and `finishCopied` of that module
without change.

## The body

The body commits a 16-byte frame at WAT 2557 to 2560, checks the sum of
the length and the addition, computes the new capacity, calls absolute
`func 27` with a 12-byte result slot at `frame + 4`, reads the answer and
stores the new capacity and the new pointer in the two-word header.

The new capacity is the compiled `max(max(2 * cap, required), min_cap)`
of WAT 2578 to 2602, where `min_cap` is 8 for a one-byte element and 4
otherwise.  `growCapacity` is that number.

## The depth

Absolute `func 27` holds no `global.get 0` and
`Project.RustHashMap.PairGrow.Func24Spec` takes no stack resource at all,
so it adds nothing below its caller.  `growDepth` is therefore the frame
of absolute `func 13` alone.

## The two dead arms

X-F13-ADD of `Analysis/scope-and-exclusions.md` is the `call 99` and
`unreachable` at WAT 2572, behind the overflow guard at WAT 2563 to 2570.
The precondition kills it with `len + additional < UInt32.size`.

X-F13-OOM is the `call 99` and `unreachable` at WAT 2618, behind the
guard at WAT 2609 to 2613 that reads the tag word of the result slot.
The precondition kills it with the size bound, which makes the new layout
valid, so `Func24Spec` returns the tag `0`.
-/

namespace Project.RustHashMap.GrowContract

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

/-! ## Constants -/

/-- The capacity that absolute `func 13` selects: twice the old capacity,
or the capacity the caller needs, whichever is larger, and never below
the minimum that the element size fixes. -/
def growCapacity (capacity required elemSize : Nat) : Nat :=
  max (max (2 * capacity) required) (if elemSize = 1 then 8 else 4)

/-- The stack that absolute `func 27` takes below its caller.  The body
holds no `global.get 0`, and `Func24Spec` takes no stack resource, so the
answer is zero. -/
def finishGrowDepth : Nat := 0

/-- The stack that absolute `func 13` takes below its caller: its own
16-byte frame, and nothing more. -/
def growDepth : Nat := 16 + finishGrowDepth

theorem growDepth_eq : growDepth = 16 := rfl

/-- The allocation history after one `grow_amortized`.  The body only
forwards the answer of absolute `func 27`, so the history is the one that
`finishHistory` names. -/
def growHistory (history : AllocationHistory) (source : FinishSource)
    (oldPtr : UInt32) (oldLayout : AllocLayout) (newPtr : UInt32)
    (newLayout : AllocLayout) : AllocationHistory :=
  finishHistory history source oldPtr oldLayout newPtr newLayout

/-! ## The result continuation -/

/-- The result continuation of absolute `func 13`.  The frame is the
sixteen bytes below the stack pointer `sp`.  A normal return restores
`sp`, and the two-word header holds the new capacity and the new pointer.

The shape follows
`Project.RustHashMap.PairGrow.PairGrowContinuation`, with two changes:
the element size and the alignment are operands, and the final history is
exact rather than existential, because the body changes nothing after
absolute `func 27` returns. -/
def GrowContinuation [WasmSmallStepGS hlc Universal.State]
    (sp header cap ptr len additional align size : UInt32)
    (source : FinishSource) (below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let newCapacityNat :=
    growCapacity cap.toNat (len.toNat + additional.toNat) size.toNat
  let oldLayout : AllocLayout :=
    { size := size.toNat * cap.toNat, alignment := align.toNat }
  let newLayout : AllocLayout :=
    { size := size.toNat * newCapacityNat, alignment := align.toNat }
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ newBytes : List UInt8, ∀ below' : List UInt8,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp growDepth below' -∗
          pointsTo_u32 0 header (UInt32.ofNat newCapacityNat) -∗
          pointsTo_u32 0 (header + 4) newPtr -∗
          LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
          BumpHeap heapId finish finish.toNat
            (growHistory history source ptr oldLayout newPtr newLayout) -∗
          ⌜finishCopied source oldLayout newBytes⌝ -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls
            calls s E Φ) ∧
        (StackPointer (sp - 16) -∗
          StackBelow sp growDepth below -∗
          pointsTo_u32 0 header cap -∗
          pointsTo_u32 0 (header + 4) ptr -∗
          FinishSourceOwn heapId cap ptr oldLayout source -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      StackPointer (sp - 16) -∗
      StackBelow sp growDepth below -∗
      pointsTo_u32 0 header cap -∗
      pointsTo_u32 0 (header + 4) ptr -∗
      FinishSourceOwn heapId cap ptr oldLayout source -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-! ## The contract -/

/-- Absolute `func 13`, local `func10`, `RawVec::grow_amortized`.

The five arguments in source order are the two-word header, the current
length, the addition, the alignment and the element size, so local 0 is
the header, local 1 the length, local 2 the addition, local 3 the
alignment and local 4 the element size.  Both call sites push them in
that order, so the operand list carries the element size on top.

The length and the addition enter the body through one sum only, so the
contract states the two bounds on the sum and nothing about each one
alone. -/
def Func10Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp header cap ptr len additional align size : UInt32)
    (source : FinishSource) (below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 13
      [.i32 size, .i32 align, .i32 additional, .i32 len, .i32 header]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp growDepth below ∗
        pointsTo_u32 0 header cap ∗
        pointsTo_u32 0 (header + 4) ptr ∗
        FinishSourceOwn heapId cap ptr
          { size := size.toNat * cap.toNat,
            alignment := align.toNat } source ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜(align = 1 ∨ align = 4) ∧ (size = 1 ∨ size = 8) ∧
          header.toNat + 8 < UInt32.size ∧
          len.toNat + additional.toNat < UInt32.size ∧
          cap.toNat < len.toNat + additional.toNat ∧
          size.toNat *
              growCapacity cap.toNat (len.toNat + additional.toNat)
                size.toNat ≤ 2147483648 - align.toNat ∧
          growDepth ≤ sp.toNat⌝ ∗
        GrowContinuation sp header cap ptr len additional align size
          source below heapId storedCursor frontier history input output
          raised callerLocals stack code arity remainder controls calls
          s E Φ)

end Project.RustHashMap.GrowContract
