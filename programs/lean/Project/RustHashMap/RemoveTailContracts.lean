import Project.RustHashMap.RemoveTailDefs
import Project.RustHashMap.DriverTailProof

/-!
# The tail of the `map_remove` driver: the contract

`Project.RustHashMap.RemoveTailDefs` cuts the code of the `map_remove`
driver after the read phase into fragments.  This file states what the
tail proves.  The statement is the interface between the read phase,
which `Project.RustHashMap.RemoveRead` proves, and the body proof that
comes next.

The statement mirrors
`Project.RustHashMap.LookupTailContracts.GetTailSpec`, because the two
drivers share the frame size and the read phase.  The tail takes four
things beyond the resources of its read phase:

* 14080 bytes below the reserve, which together with the sixteen bytes of
  the reserve make the region that the callees need;
* the `RandomState` cells, which `collect_entries` reads and writes;
* the whole data segment, out of which the key decoder cuts its static
  messages;
* the bound on the input length, so that the stored length word reads
  back as the number of input bytes.

The tail gives back the runtime, the restored stack pointer and the
output stream, through `Project.RustHashMap.DriverTailProof.TailDone`.
It drops the stack bytes, the bump heap and every live block, which is
sound because `ExportSuccess` names only the output stream.

The deepest callee is `sorted_entries`, absolute `func 7`, so the region
below the frame is `removeCalleeDepth` bytes, which is `serializeDepth`.
The key decoder, `collect_entries`, the reply writer and
`borsh::io::Error::new` take less, and `keyDecoderDepth_le_remove`,
`collectDepth_le_remove`, `replyDepth_le_remove` and
`errorNewDepth_le_remove` state that.  The remove kernel, absolute
`func 11`, commits no frame at all.

Four of the five callees are proved already: `Func7Spec` by
`Project.RustHashMap.Func7Proof.func7_correct`, `Func4Spec` by
`Func4Proof.func4_correct`, `Func5Spec` by `Func5Proof.func5_correct`,
and `Func8Spec` by `Func8Proof.func8_correct`.  The fifth is
`Project.RustHashMap.CollectContract.Func2Spec`, which is still open, so
the theorem that discharges this contract is
`twp_remove_tail (hfunc2 : Func2Spec) : RemoveTailSpec`.
-/

namespace Project.RustHashMap.RemoveTailContracts

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
open Project.RustHashMap.EntriesContracts
open Project.RustHashMap.RemoveRead
open Project.RustHashMap.RemoveTailDefs
open scoped Wasm.SmallStep.Outcome

/-- The contract of the `map_remove` driver after its read loop.

The driver frame holds 320 bytes.  The entries vector header for
`call 5` sits at frame offsets 0 to 12, the output slot of the key
decoder at 16 to 36, the map slot that overlays it at 16 to 48, the input
vector header at 52 to 64, and the 256-byte chunk buffer at 64 to 320.
The tail reuses the first 40 bytes of the chunk buffer as the output slot
of the remove kernel, and the first 12 bytes of the new map value there
as the output header of `sorted_entries`.

The tail has two exits.  The reject exit frees the decoded error and the
input buffer, and it writes nothing; `Spec.removeOutput` is the empty
list there.  The accept exit writes the removed value as a borsh
`Option<u32>` and then the map that remains.  An allocator failure inside
a callee raises `talos.oom`. -/
def RemoveTailSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (heapId : GName) (capacity ptr aux4 : UInt32)
    (input output : List UInt8)
    (reserve head chunk extra keysBefore dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterTail : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp},
    iprop(
      AfterReadRm heapId capacity ptr input reserve head chunk
        storedCursor frontier history output ∗
      Slices.ByteSlice 0
        (func6Base - UInt32.ofNat removeCalleeDepth) extra ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      ⌜extra.length = 14080 ∧ keysBefore.length = randomStateSize ∧
        dataBytes.length = dataSegmentSize ∧
        keysBefore[16]? ≠ some 2 ∧
        dataBytes.take 24 = staticTableBytes ∧
        input.length < UInt32.size⌝ ∗
      (DriverTailProof.TailDone
          (output ++ Project.RustHashMap.Spec.removeOutput input)
          afterTail arity remainder controls calls s E Φ ∗
        (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨afterReadLocalsRm (UInt32.ofNat input.length) capacity ptr aux4,
          func6AfterRead ++ afterTail,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]

end Project.RustHashMap.RemoveTailContracts
