import Project.RustHashMap.AllocatorContracts

/-!
# Entry contracts of the five hash map exports

Each export of the hash map program is a wrapper with one `call`:

* `map_contains_key` is local `func25`, absolute index 28, and calls 19.
* `map_get` is local `func26`, absolute index 29, and calls 21.
* `map_insert` is local `func27`, absolute index 30, and calls 3.
* `map_len` is local `func28`, absolute index 31, and calls 22.
* `map_remove` is local `func29`, absolute index 32, and calls 9.

`EntrySpec` states the contract of one wrapper in the shape that the
adequacy bridge consumes.  The wrapper starts with the whole shadow stack,
the empty bump heap, and the input stream.  A normal return leaves the
expected output in the stream.  The only other outcome is the `talos.oom`
trap with the OOM marker set.  All other resources are hidden, because no
compiled function calls a wrapper.

The precise contracts of the five driver functions (3, 9, 19, 21, and 22)
come with their body proofs.  Each wrapper contract follows from its driver
contract by one `call` step and by hiding the driver resources.
-/

namespace Project.RustHashMap.EntryContracts

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open scoped Wasm.SmallStep.Outcome

/-- Ownership of mutable Wasm global zero, the Rust shadow stack pointer. -/
def StackPointer [WasmGlobalGS Universal.State]
    (sp : UInt32) : HeapIProp :=
  globalPointsToAt 0 0 (.i32 sp)

/-- A raw initialized stack region. -/
abbrev StackRegion [WasmHeapGS Universal.State]
    (low : UInt32) (bytes : List UInt8) : HeapIProp :=
  Slices.ByteSlice 0 low bytes

/-- The size of the whole shadow stack: every byte below the initial stack
top.  The data segment starts at the stack top, so the stack is exactly the
low addresses. -/
def stackSize : Nat := entryStackTop.toNat

/-- The resources an export leaves after a normal return: the output stream
holds `output` and the OOM marker is clear.  The remaining input is not
constrained. -/
def ExportSuccess [WasmHostStateGS Universal.State]
    (output : List UInt8) : HeapIProp :=
  iprop(∃ remaining : List UInt8, Streams remaining output false)

/-- The resources an export leaves after the `talos.oom` trap: the OOM
marker is set.  The streams are not constrained. -/
def ExportOOM [WasmHostStateGS Universal.State] : HeapIProp :=
  iprop(∃ remaining output : List UInt8, Streams remaining output true)

/-- The entry contract of the export wrapper at `absoluteIndex`.  The
function `expected` gives the output bytes for each input.

The wrapper takes the thread-local `RandomState` region as well as the
shadow stack.  `collect_entries` reads and writes those cells, and they sit
above the stack top, so they are a separate resource. -/
def EntrySpec [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat) (expected : List UInt8 → List UInt8) : Prop :=
  ∀ (heapId : GName) (input stackBytes dataBytes randomState : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract absoluteIndex [] callerLocals stack code arity remainder
      controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer entryStackTop ∗
        StackRegion 0 stackBytes ∗
        StackRegion entryStackTop dataBytes ∗
        StackRegion randomStateCell randomState ∗
        BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
        Streams input [] false ∗
        ⌜stackBytes.length = stackSize ∧
          dataBytes.length = dataSegmentSize ∧
          randomState.length = randomStateSize⌝ ∗
        (RuntimeContext -∗ ExportSuccess (expected input) -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∗
        (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage))))

/-- Local `func25`, absolute index 28, the `map_contains_key` wrapper. -/
def Func25Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 28 Project.RustHashMap.Spec.containsKeyOutput

/-- Local `func26`, absolute index 29, the `map_get` wrapper. -/
def Func26Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 29 Project.RustHashMap.Spec.getOutput

/-- Local `func27`, absolute index 30, the `map_insert` wrapper. -/
def Func27Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 30 Project.RustHashMap.Spec.insertOutput

/-- Local `func28`, absolute index 31, the `map_len` wrapper. -/
def Func28Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 31 Project.RustHashMap.Spec.lenOutput

/-- Local `func29`, absolute index 32, the `map_remove` wrapper. -/
def Func29Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 32 Project.RustHashMap.Spec.removeOutput

end Project.RustHashMap.EntryContracts
