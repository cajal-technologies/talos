import Project.RustHashMap.Allocator

/-!
# Call contracts of the hash map allocator functions

The four allocator functions of the hash map program are the same compiled
code as the mergesort ones.  This module states their contracts in the
mergesort shape over the hash map allocator layer:

* `Func55Spec`: local `func55`, absolute index 58, the bump allocator.
* `Func57Spec`: local `func57`, absolute index 60, the no-op deallocator.
* `Func58Spec`: local `func58`, absolute index 61, the reallocator.
* `Func59Spec`: local `func59`, absolute index 62, the zeroed allocator.

The `talos.oom` shim (local `func56`, absolute index 59) has its contract
`Func56Spec` in `Project.RustHashMap.Contracts`.
-/

namespace Project.RustHashMap.AllocatorContracts

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open scoped Wasm.SmallStep.Outcome

/-! ## Allocator result continuations -/

/-- Arithmetic OOM has only the terminal arm.  Arithmetic success has both a
normal arm and an exact OOM arm for `memory.grow = -1`; no compiler-generated
allocation-error continuation is exposed. -/
def AllocContinuation [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (layout : AllocLayout)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  match classifyBump frontier layout with
  | .success base finish => iprop(
      (∀ bytes : List UInt8,
          RuntimeContext -∗
          BumpHeap heapId finish finish.toNat
            (history.allocate base layout) -∗
          LiveBlock heapId history.nextId base layout bytes -∗
          Streams input output raised -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls
            calls s E Φ) ∧
        (BumpHeap heapId storedCursor frontier history -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func55`, absolute index 58. -/
def Func55Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (size alignment : UInt32) (layout : AllocLayout)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 58 [.i32 alignment, .i32 size]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜layout.Matches size alignment ∧ layout.Valid ∧
          (layout.alignment = 1 ∨ layout.alignment = 4)⌝ ∗
        AllocContinuation heapId storedCursor frontier history layout
          input output raised callerLocals stack code arity remainder controls
          calls s E Φ)

def ReallocContinuation [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (oldId : Nat) (oldPtr : UInt32) (oldLayout : AllocLayout)
    (oldBytes : List UInt8) (newLayout : AllocLayout)
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
          BumpHeap heapId finish finish.toNat
            (history.reallocate oldId oldPtr oldLayout newPtr newLayout) -∗
          LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
          ⌜newBytes.take (min oldLayout.size newLayout.size) =
            oldBytes.take (min oldLayout.size newLayout.size)⌝ -∗
          Streams input output raised -∗
          ResumeWP [.i32 newPtr] callerLocals stack code arity remainder controls
            calls s E Φ) ∧
        (BumpHeap heapId storedCursor frontier history -∗
          LiveBlock heapId oldId oldPtr oldLayout oldBytes -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      BumpHeap heapId storedCursor frontier history -∗
      LiveBlock heapId oldId oldPtr oldLayout oldBytes -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func58`, absolute index 61. -/
def Func58Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (oldPtr oldSize alignment newSize : UInt32)
    (oldLayout newLayout : AllocLayout)
    (heapId : GName) (oldId : Nat) (oldBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 61
      [.i32 newSize, .i32 alignment, .i32 oldSize, .i32 oldPtr]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        BumpHeap heapId storedCursor frontier history ∗
        LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
        Streams input output raised ∗
        ⌜oldLayout.Matches oldSize alignment ∧
          newLayout.Matches newSize alignment ∧
          oldLayout.Valid ∧ newLayout.Valid ∧
          (oldLayout.alignment = 1 ∨ oldLayout.alignment = 4) ∧
          oldLayout.size < newLayout.size⌝ ∗
        ReallocContinuation heapId storedCursor frontier history oldId oldPtr
          oldLayout oldBytes newLayout input output raised callerLocals stack
          code arity remainder controls calls s E Φ)

def ZeroAllocContinuation [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (layout : AllocLayout)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  match classifyBump frontier layout with
  | .success base finish => iprop(
      (RuntimeContext -∗
        BumpHeap heapId finish finish.toNat
          (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout
          (List.replicate layout.size 0) -∗
        Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls
          calls s E Φ) ∧
      (BumpHeap heapId storedCursor frontier history -∗
        Streams input output true -∗
        Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func59`, absolute index 62. -/
def Func59Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (size alignment : UInt32) (layout : AllocLayout)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 62 [.i32 alignment, .i32 size]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜layout.Matches size alignment ∧ layout.Valid ∧
          layout.alignment = 4⌝ ∗
        ZeroAllocContinuation heapId storedCursor frontier history layout
          input output raised callerLocals stack code arity remainder controls
          calls s E Φ)

/-- Local `func57`, absolute index 60, performs only the logical retirement. -/
def Func57Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (ptr size alignment : UInt32) (layout : AllocLayout)
    (heapId : GName) (allocationId : Nat) (bytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 60 [.i32 alignment, .i32 size, .i32 ptr]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        BumpHeap heapId storedCursor frontier history ∗
        LiveBlock heapId allocationId ptr layout bytes ∗
        ⌜size.toNat = layout.size ∧
          alignment.toNat = layout.alignment ∧
          (layout.alignment = 1 ∨ layout.alignment = 4)⌝ ∗
        (RuntimeContext -∗
          BumpHeap heapId storedCursor frontier
            (history.retire allocationId ptr layout) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

end Project.RustHashMap.AllocatorContracts
