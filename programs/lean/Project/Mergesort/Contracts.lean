import Project.Mergesort.Representations
import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Authoritative main specifications for generated merge-sort

This file contains exactly one contract family for each in-scope import and
each reachable generated function (`func0`--`func11`).  It contains no contract
for excluded functions 12--55.  These frozen statements have passed the
body-side and call-site audits, including the terminal current-instance
ownership correction validated by the import-2/`func6` proofs and the distinct
shim/import operand orders validated by the import-0/1 and `func10`/`func11`
proofs.  They are interfaces, not body proofs.
-/

namespace Project.Mergesort.Contracts

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

/-- A call site with its top-of-stack operands already in machine order. -/
def callExpr (absoluteIndex : Nat) (operands : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Expr Universal.State :=
  .running
    ⟨{ callerLocals with values := operands ++ stack },
      .call absoluteIndex :: code, arity, remainder, controls, calls⟩

/-- The caller state after a normal return, with result operands in machine
top-of-stack order. -/
def resumeExpr (results : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Expr Universal.State :=
  .running
    ⟨{ callerLocals with values := results ++ stack },
      code, arity, remainder, controls, calls⟩

def ResumeWP [WasmSmallStepGS hlc Universal.State]
    (results : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  WP (resumeExpr results callerLocals stack code arity remainder controls calls)
    @ s; E [{ Φ }]

def CallContract [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat) (operands : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (resources : HeapIProp) : Prop :=
  resources ⊢ WP (callExpr absoluteIndex operands callerLocals stack code arity
    remainder controls calls) @ s; E [{ Φ }]

def readContractAt [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat)
    (operands : UInt32 → UInt32 → List Value) : Prop :=
  ∀ (ptr requested : UInt32) (buffer input output : List UInt8)
    (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    let count := min requested.toNat input.length
    CallContract absoluteIndex (operands ptr requested)
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Streams input output raised ∗
        ByteSlice ptr buffer ∗
        ⌜requested.toNat = buffer.length ∧ 0 < requested.toNat⌝ ∗
        (RuntimeContext -∗
          Streams (input.drop count) output raised -∗
          ByteSlice ptr (input.take count ++ buffer.drop count) -∗
          ⌜count ≤ requested.toNat⌝ -∗
          ResumeWP [.i32 (UInt32.ofNat count)] callerLocals stack code arity
            remainder controls calls s E Φ))

def writeContractAt [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat)
    (operands : UInt32 → UInt32 → List Value) : Prop :=
  ∀ (ptr requested : UInt32) (bytes input output : List UInt8)
    (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract absoluteIndex (operands ptr requested)
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Streams input output raised ∗
        ByteSlice ptr bytes ∗
        ⌜requested.toNat = bytes.length ∧ 0 < requested.toNat⌝ ∗
        (RuntimeContext -∗
          Streams input (output ++ bytes) raised -∗
          ByteSlice ptr bytes -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Imports 0--2 -/

/-- Import 0, `stdio.read`. -/
def Import0Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  readContractAt (hlc := hlc) 0
    (fun ptr requested => [.i32 ptr, .i32 requested])

/-- Import 1, `stdio.write`. -/
def Import1Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  writeContractAt (hlc := hlc) 1
    (fun ptr requested => [.i32 ptr, .i32 requested])

/-- Import 2, the valid terminal `talos.oom` outcome. -/
def Import2Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 2 [] callerLocals stack code arity remainder controls calls
      s E Φ iprop(
        RuntimeContext ∗ Streams input output raised ∗
        (Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))

/-! ## RawVec storage transition witnesses -/

inductive GrowSource where
  | empty
  | allocated (allocationId : Nat) (allBytes spare : List UInt8)

def GrowSourceOwn [WasmHeapGS Universal.State]
    (heapId : GName) (oldCapacity oldPtr : UInt32)
    (initialized : List UInt8) : GrowSource → HeapIProp
  | .empty => iprop(⌜oldCapacity = 0 ∧ oldPtr = 1 ∧ initialized = []⌝)
  | .allocated allocationId allBytes spare => iprop(
      ⌜0 < oldCapacity.toNat ∧
        initialized.length ≤ oldCapacity.toNat ∧
        allBytes = initialized ++ spare ∧
        spare.length = oldCapacity.toNat - initialized.length⌝ ∗
      LiveBlock heapId allocationId oldPtr
        { size := oldCapacity.toNat, alignment := 1 } allBytes)

private theorem GrowSourceOwn_to_VecStorage
    [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) (source : GrowSource) :
    GrowSourceOwn heapId capacity ptr initialized source ⊢
      VecStorage heapId capacity ptr initialized := by
  cases source with
  | empty =>
      unfold GrowSourceOwn VecStorage
      iintro Hsource
      ileft
      iexact Hsource
  | allocated allocationId allBytes spare =>
      unfold GrowSourceOwn VecStorage
      iintro Hsource
      iright
      iexists allocationId, allBytes, spare
      iexact Hsource

/-- `VecStorage` and `func0`'s source witness are the same ownership with the
allocation details made explicit.  This is the exact `func1 -> func0`
call-preparation/reassembly bridge. -/
theorem VecStorage_as_growSource
    [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) :
    VecStorage heapId capacity ptr initialized ⊣⊢
      iprop(∃ source : GrowSource,
        GrowSourceOwn heapId capacity ptr initialized source) := by
  constructor
  · iintro Hstorage
    isimp only [VecStorage] at Hstorage
    icases Hstorage with (%hempty | Hallocated)
    · iexists GrowSource.empty
      isimp only [GrowSourceOwn]
      ipureexact hempty
    · icases Hallocated with
        ⟨%allocationId, %allBytes, %spare, Hfacts, Hblock⟩
      iexists GrowSource.allocated allocationId allBytes spare
      isimp only [GrowSourceOwn]
      iframe
  · iintro ⟨%source, Hsource⟩
    iapply GrowSourceOwn_to_VecStorage heapId capacity ptr initialized source
    iexact Hsource

def growHistory (history : AllocationHistory) (source : GrowSource)
    (oldCapacity oldPtr newPtr : UInt32) (newLayout : AllocLayout) :
    AllocationHistory :=
  match source with
  | .empty => history.allocate newPtr newLayout
  | .allocated allocationId _ _ =>
      history.reallocate allocationId oldPtr
        { size := oldCapacity.toNat, alignment := 1 } newPtr newLayout

def growCopied (source : GrowSource) (oldCapacity : UInt32)
    (newBytes : List UInt8) : Prop :=
  match source with
  | .empty => True
  | .allocated _ allBytes _ =>
      newBytes.take oldCapacity.toNat = allBytes

def growResultBytes (pointer capacity : UInt32) : List UInt8 :=
  serialize [0, pointer, capacity]

/-- Exact contents of `func1`'s sixteen-byte temporary frame after a normal
grow.  The function never touches the first four bytes; `func0` overwrites the
remaining twelve with its tag, pointer, and byte-capacity result. -/
def reserveSuccessShadow (shadow : List UInt8)
    (pointer capacity : UInt32) : List UInt8 :=
  shadow.take 4 ++ growResultBytes pointer capacity

theorem reserveSuccessShadow_length (shadow : List UInt8)
    (pointer capacity : UInt32) (hlength : shadow.length = 16) :
    (reserveSuccessShadow shadow pointer capacity).length = 16 := by
  unfold reserveSuccessShadow growResultBytes
  rw [List.length_append, List.length_take, serialize_length]
  simp [hlength]

/-- Even when pure bump arithmetic selects `.success`, the modular WP does not
own the physical store's instantiated memory-cap metadata.  The additive
conjunction in that branch therefore requires the caller to accept both the
normal allocation result and the same exact pre-commit OOM terminal used by
the `.oom` classification. -/
def FinishGrowContinuation [WasmSmallStepGS hlc Universal.State]
    (result oldCapacity oldPtr newCapacity : UInt32)
    (source : GrowSource) (initialized growBefore : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let newLayout : AllocLayout :=
    { size := newCapacity.toNat, alignment := 1 }
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ newBytes : List UInt8,
          RuntimeContext -∗
          ByteSlice result (growResultBytes newPtr newCapacity) -∗
          BumpHeap heapId finish finish.toNat
            (growHistory history source oldCapacity oldPtr newPtr newLayout) -∗
          LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
          ⌜growCopied source oldCapacity newBytes ∧
            newBytes.take initialized.length = initialized⌝ -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∧
        (ByteSlice result growBefore -∗
          GrowSourceOwn heapId oldCapacity oldPtr initialized source -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      ByteSlice result growBefore -∗
      GrowSourceOwn heapId oldCapacity oldPtr initialized source -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func0`, absolute index 3.  Its valid-input specialization has only
normal success or the distinguished OOM terminal outcome. -/
def Func0Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (result oldCapacity oldPtr newCapacity alignment elementSize : UInt32)
    (source : GrowSource) (initialized growBefore : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    let newLayout : AllocLayout :=
      { size := newCapacity.toNat, alignment := 1 }
    CallContract 3
      [.i32 elementSize, .i32 alignment, .i32 newCapacity, .i32 oldPtr,
        .i32 oldCapacity, .i32 result]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        ByteSlice result growBefore ∗
        GrowSourceOwn heapId oldCapacity oldPtr initialized source ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜alignment = 1 ∧ elementSize = 1 ∧
          growBefore.length = 12 ∧
          8 ≤ newCapacity.toNat ∧
          oldCapacity.toNat < newCapacity.toNat ∧
          newLayout.Valid⌝ ∗
        FinishGrowContinuation result oldCapacity oldPtr newCapacity source
          initialized growBefore heapId storedCursor frontier history input
          output raised callerLocals stack code arity remainder controls calls
          s E Φ)

def ReserveContinuation [WasmSmallStepGS hlc Universal.State]
    (totalBytes : Nat) (current : List UInt8)
    (capacity ptr : UInt32) (initialized shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (remaining output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let newCapacityNat :=
    selectedCapacity initialized.length current.length capacity.toNat
  let newCapacity := UInt32.ofNat newCapacityNat
  let newLayout : AllocLayout :=
    { size := newCapacityNat, alignment := 1 }
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ finalHistory : AllocationHistory,
          RuntimeContext -∗
          StackPointer driverBase -∗
          StackReserve reserveBase
            (reserveSuccessShadow shadow newPtr newCapacity) -∗
          VecU8 heapId driverBase newCapacity newPtr initialized -∗
          BumpHeap heapId finish finish.toNat finalHistory -∗
          ⌜VecReserveHistory history finalHistory capacity ptr newPtr newLayout ∧
            GeometricVecFacts totalBytes
              (initialized.length + current.length) remaining.length
              newCapacity newPtr finish.toNat finalHistory⌝ -∗
          Streams remaining output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∧
        (StackPointer reserveBase -∗
          StackReserve reserveBase shadow -∗
          VecU8 heapId driverBase capacity ptr initialized -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams remaining output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      StackPointer reserveBase -∗
      StackReserve reserveBase shadow -∗
      VecU8 heapId driverBase capacity ptr initialized -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams remaining output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func1`, absolute index 4.  The explicit arithmetic and lineage
facts are the originating proof obligations for both excluded `func43` edges. -/
def Func1Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (header length additional alignment elementSize : UInt32)
    (totalBytes : Nat) (current remaining : List UInt8)
    (capacity ptr : UInt32) (initialized shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    let newCapacityNat :=
      selectedCapacity initialized.length current.length capacity.toNat
    let newLayout : AllocLayout :=
      { size := newCapacityNat, alignment := 1 }
    CallContract 4
      [.i32 elementSize, .i32 alignment, .i32 additional, .i32 length,
        .i32 header]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer driverBase ∗
        StackReserve reserveBase shadow ∗
        VecU8 heapId driverBase capacity ptr initialized ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams remaining output raised ∗
        ⌜header = driverBase ∧ alignment = 1 ∧ elementSize = 1 ∧
          length.toNat = initialized.length ∧
          additional.toNat = current.length ∧
          current.length = min 256
            (current.length + remaining.length) ∧
          0 < current.length ∧ current.length % 4 = 0 ∧
          capacity.toNat - initialized.length < current.length ∧
          totalBytes = initialized.length + current.length + remaining.length ∧
          GeometricVecFacts totalBytes initialized.length
            (current.length + remaining.length) capacity ptr frontier history ∧
          initialized.length + current.length < UInt32.size ∧
          newCapacityNat < UInt32.size ∧ newLayout.Valid⌝ ∗
        ReserveContinuation totalBytes current capacity ptr initialized shadow
          heapId storedCursor frontier history remaining output raised
          callerLocals stack code arity remainder controls calls s E Φ)

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

/-- Local `func5`, absolute index 8. -/
def Func5Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (size alignment : UInt32) (layout : AllocLayout)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 8 [.i32 alignment, .i32 size]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜layout.Matches size alignment ∧ layout.Valid ∧
          (layout.alignment = 1 ∨ layout.alignment = 4)⌝ ∗
        AllocContinuation heapId storedCursor frontier history layout
          input output raised callerLocals stack code arity remainder controls
          calls s E Φ)

/-- Local `func6`, absolute index 9. -/
def Func6Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 9 [] callerLocals stack code arity remainder controls calls
      s E Φ iprop(
        RuntimeContext ∗ Streams input output raised ∗
        (Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))

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

/-- Local `func8`, absolute index 11. -/
def Func8Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
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
    CallContract 11
      [.i32 newSize, .i32 alignment, .i32 oldSize, .i32 oldPtr]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        BumpHeap heapId storedCursor frontier history ∗
        LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
        Streams input output raised ∗
        ⌜oldLayout.Matches oldSize alignment ∧
          newLayout.Matches newSize alignment ∧
          oldLayout.Valid ∧ newLayout.Valid ∧
          oldLayout.alignment = 1 ∧
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

/-- Local `func9`, absolute index 12. -/
def Func9Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (size alignment : UInt32) (layout : AllocLayout)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 12 [.i32 alignment, .i32 size]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜layout.Matches size alignment ∧ layout.Valid ∧
          layout.alignment = 4⌝ ∗
        ZeroAllocContinuation heapId storedCursor frontier history layout
          input output raised callerLocals stack code arity remainder controls
          calls s E Φ)

/-! ## Success-only reachable functions -/

/-- `func2`'s exact piecewise scratch result. -/
def SortResultBuffers
    [WasmHeapGS Universal.State]
    (source scratch : UInt32)
    (input scratchInput sorted : List UInt32) : HeapIProp := iprop%
  SortBuffers source scratch sorted
      (if input.length ≤ 1 then scratchInput else sorted) ∗
    ⌜SortedPermutation input sorted⌝

/-- Local `func2`, absolute index 5. -/
def Func2Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (source n scratch scratchN : UInt32)
    (input scratchInput : List UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 5 [.i32 scratchN, .i32 scratch, .i32 n, .i32 source]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗ SortBuffers source scratch input scratchInput ∗
        ⌜n.toNat = input.length ∧
          scratchN.toNat = scratchInput.length⌝ ∗
        (∀ sorted : List UInt32,
          RuntimeContext -∗
          SortResultBuffers source scratch input scratchInput sorted -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-- Local `func3`, absolute index 6, is the sole public entry contract.  Its
only terminal alternative is phase-classified `talos.oom`. -/
def Func3Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (heapId : GName) (original : List UInt32) (entryBytes : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 6 [] callerLocals stack code arity remainder controls calls
      s E Φ iprop(
        RuntimeContext ∗
        StackPointer entryStackTop ∗
        StackRegion entryStackLow entryBytes ∗
        BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
        Streams (serialize original) [] false ∗
        ⌜entryBytes.length = 288⌝ ∗
        (RuntimeContext -∗ DriverSuccess heapId original -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∗
        ((∃ phase : DriverOOMPhase,
            DriverOOMState heapId original phase) -∗
          Φ (.trapped (.host OOM.trapMessage))))

/-- Local `func4`, absolute index 7, is the allocation marker identity. -/
def Func4Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 7 [] callerLocals stack code arity remainder controls calls
      s E Φ iprop(RuntimeContext ∗
        (RuntimeContext -∗ ResumeWP [] callerLocals stack code arity remainder
          controls calls s E Φ))

/-- Local `func7`, absolute index 10, performs only the logical retirement. -/
def Func7Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (ptr size alignment : UInt32) (layout : AllocLayout)
    (heapId : GName) (allocationId : Nat) (bytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 10 [.i32 alignment, .i32 size, .i32 ptr]
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

/-! ## ABI-only local shims -/

/-- Local `func10`, absolute index 13. -/
def Func10Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  readContractAt (hlc := hlc) 13
    (fun ptr requested => [.i32 requested, .i32 ptr])

/-- Local `func11`, absolute index 14. -/
def Func11Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  writeContractAt (hlc := hlc) 14
    (fun ptr requested => [.i32 requested, .i32 ptr])

end Project.Mergesort.Contracts
