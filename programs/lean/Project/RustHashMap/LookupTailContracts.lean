import Project.RustHashMap.LookupTailDefs
import Project.RustHashMap.DriverTailProof

/-!
# The tails of the two lookup drivers: the contracts

`Project.RustHashMap.LookupTailDefs` cuts the code of the two lookup
drivers after the read phase into fragments.  This file states what each
tail proves.  The two statements are the interface between the read phase,
which `Project.RustHashMap.ContainsKeyRead` and
`Project.RustHashMap.GetRead` prove, and the body proofs that come next.

Both statements mirror `Project.RustHashMap.DriverTail.DriverTailSpec`.
Each tail takes four things beyond the resources of its read phase:

* 320 bytes below the reserve, which together with the sixteen bytes of
  the reserve make the region that the callees need;
* the `RandomState` cells, which `collect_entries` reads and writes;
* the whole data segment, out of which the key decoder cuts its static
  messages;
* the bound on the input length, so that the stored length word reads
  back as the number of input bytes.

Each tail gives back the runtime, the restored stack pointer and the
output stream, through
`Project.RustHashMap.DriverTailProof.TailDone`.  It drops the stack
bytes, the bump heap and every live block, which is sound because
`ExportSuccess` names only the output stream.

The deepest callee is the key decoder, so the region below each frame is
`lookupCalleeDepth` bytes.  `collect_entries` and `borsh::io::Error::new`
take less, and `collectDepth_le_lookup` and `errorNewDepth_le_lookup`
state that.
-/

namespace Project.RustHashMap.LookupTailContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.ContainsKeyRead
open Project.RustHashMap.GetRead
open Project.RustHashMap.LookupTailDefs
open scoped Wasm.SmallStep.Outcome

/-- The contract of the `map_contains_key` driver after its read loop.

The driver frame holds 304 bytes.  The entries vector header for `call 5`
sits at frame offsets 0 to 12, the output slot of the key decoder at 16 to
36, the input vector header at 36 to 48, and the 256-byte chunk buffer at
48 to 304.  The map slot is the first 32 bytes of the chunk buffer, at
offsets 48 to 80.

The tail has three exits.  The reject exit frees the decoded error and the
input buffer, and it writes nothing; `Spec.containsKeyOutput` is the empty
list there.  The accept exit writes one byte, which is the borsh `bool` of
the answer.  The allocator failure exit raises `talos.oom`. -/
def ContainsKeyTailSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (heapId : GName) (capacity ptr aux4 : UInt32)
    (input output : List UInt8)
    (reserve head chunk extra keysBefore dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterTail : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp},
    iprop(
      AfterReadCK heapId capacity ptr input reserve head chunk
        storedCursor frontier history output ∗
      Slices.ByteSlice 0
        (func16Base - UInt32.ofNat lookupCalleeDepth) extra ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      ⌜extra.length = 320 ∧ keysBefore.length = randomStateSize ∧
        dataBytes.length = dataSegmentSize ∧
        keysBefore[16]? ≠ some 2 ∧
        dataBytes.take 24 = staticTableBytes ∧
        input.length < UInt32.size⌝ ∗
      (DriverTailProof.TailDone
          (output ++ Project.RustHashMap.Spec.containsKeyOutput input)
          afterTail arity remainder controls calls s E Φ ∗
        (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨afterReadLocalsCK (UInt32.ofNat input.length) capacity ptr aux4,
          func16AfterRead ++ afterTail,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]

/-- The contract of the `map_get` driver after its read loop.

The driver frame holds 320 bytes.  The output slot of the lookup kernel
sits at frame offsets 8 to 16, the entries vector header for `call 5` at
16 to 28, the output slot of the key decoder at 32 to 52, the input vector
header at 52 to 64, and the 256-byte chunk buffer at 64 to 320.  The map
slot is the first 32 bytes of the chunk buffer, at offsets 64 to 96.

The tail has three exits.  The reject exit frees the decoded error and the
input buffer, and it writes nothing; `Spec.getOutput` is the empty list
there.  The accept exit writes one byte for `none` and five bytes for
`some`, which is the borsh `Option` of the answer.  The allocator failure
exit raises `talos.oom`. -/
def GetTailSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (heapId : GName) (capacity ptr aux4 : UInt32)
    (input output : List UInt8)
    (reserve head chunk extra keysBefore dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterTail : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp},
    iprop(
      AfterReadGet heapId capacity ptr input reserve head chunk
        storedCursor frontier history output ∗
      Slices.ByteSlice 0
        (func18Base - UInt32.ofNat lookupCalleeDepth) extra ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      ⌜extra.length = 320 ∧ keysBefore.length = randomStateSize ∧
        dataBytes.length = dataSegmentSize ∧
        keysBefore[16]? ≠ some 2 ∧
        dataBytes.take 24 = staticTableBytes ∧
        input.length < UInt32.size⌝ ∗
      (DriverTailProof.TailDone
          (output ++ Project.RustHashMap.Spec.getOutput input)
          afterTail arity remainder controls calls s E Φ ∗
        (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨afterReadLocalsGet (UInt32.ofNat input.length) capacity ptr aux4,
          func18AfterRead ++ afterTail,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]

end Project.RustHashMap.LookupTailContracts
