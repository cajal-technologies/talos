import Project.RustHashMap.DriverTailDefs
import Project.RustHashMap.CollectContract
import Project.RustHashMap.ReadAllPhase
import CodeLib.RustStd.HashMap.BorshBridge

/-!
# The tail of the `map_len` driver: the stack the callees take

`Project.RustHashMap.ReadAllPhase.twp_read_phase` gives `AfterRead`, which
returns only the sixteen bytes of `StackReserve` below the driver frame.
The three functions the tail calls take much more, and each takes a
different amount: the decoder 240 bytes, `collect_entries` 192, and
`borsh::io::Error::new` 160.

This module holds the plumbing for that difference.  `driverDepth` is the
deepest of the three.  The driver carries one region of that depth and
hands each callee the top part of it.  `StackBelow_split` cuts the region
and `StackBelow_join` puts it back.

The address side condition of each cut is a separate hypothesis, because
`func19Base` is a numeral and every use closes it by `decide`.  A general
proof would need the wrap bound, which no caller of this file has to
carry.
-/

namespace Project.RustHashMap.DriverTail

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
open Project.RustHashMap.ReadAll
open scoped Wasm.SmallStep.Outcome

/-! ## The stack region the tail carries -/

/-- The deepest stack that a callee of the tail takes below the driver
frame.  The decoder takes the most, so this is `decoderDepth`. -/
def driverDepth : Nat := 240

theorem driverDepth_decoder : decoderDepth = driverDepth := rfl

theorem collectDepth_le : collectDepth ≤ driverDepth := by decide

theorem errorNewDepth_le : errorNewDepth ≤ driverDepth := by decide

/-- Hand a callee the top `shallow` bytes of the region, and keep the rest.
The callee writes only its own part, so the kept part comes back
unchanged. -/
theorem StackBelow_split [WasmHeapGS Universal.State]
    (sp : UInt32) (deep shallow : Nat) (bytes : List UInt8)
    (hle : shallow ≤ deep)
    (haddr : sp - UInt32.ofNat deep + UInt32.ofNat (deep - shallow)
      = sp - UInt32.ofNat shallow) :
    StackBelow sp deep bytes ⊢
      iprop(Slices.ByteSlice 0 (sp - UInt32.ofNat deep)
          (bytes.take (deep - shallow)) ∗
        StackBelow sp shallow (bytes.drop (deep - shallow))) := by
  iintro Hbelow
  unfold StackBelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  have hsplit : bytes.take (deep - shallow) ++ bytes.drop (deep - shallow)
      = bytes := List.take_append_drop _ _
  have htakeLength : (bytes.take (deep - shallow)).length = deep - shallow := by
    rw [List.length_take, hlength]; omega
  ihave ⟨Hlow, Hhigh⟩ :=
    (Slices.ByteSlice_append 0 (sp - UInt32.ofNat deep)
      (bytes.take (deep - shallow)) (bytes.drop (deep - shallow))).mp $$ [Hbytes]
  · irw_exact [hsplit] with Hbytes
  isplitl_exact Hlow
  · isplitl_pureexact (by rw [List.length_drop, hlength]; omega)
    irw_exact [htakeLength, haddr] with Hhigh

/-- Put the region back together after a call. -/
theorem StackBelow_join [WasmHeapGS Universal.State]
    (sp : UInt32) (deep shallow : Nat) (low below : List UInt8)
    (hlow : low.length = deep - shallow)
    (hle : shallow ≤ deep)
    (haddr : sp - UInt32.ofNat deep + UInt32.ofNat (deep - shallow)
      = sp - UInt32.ofNat shallow) :
    iprop(Slices.ByteSlice 0 (sp - UInt32.ofNat deep) low ∗
        StackBelow sp shallow below) ⊢
      StackBelow sp deep (low ++ below) := by
  iintro ⟨Hlow, Hbelow⟩
  unfold StackBelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  isplitl_pureexact (by rw [List.length_append, hlow, hlength]; omega)
  iapply (Slices.ByteSlice_append 0 (sp - UInt32.ofNat deep) low below).mpr
  isplitl_exact Hlow
  · irw_exact [hlow, haddr] with Hbytes

/-- The read phase gives the sixteen bytes of `StackReserve` at
`func19Base - 16`.  With the 224 bytes below them, that is the region the
tail carries. -/
theorem StackBelow_of_reserve [WasmHeapGS Universal.State]
    (extra reserve : List UInt8) (hextra : extra.length = 224) :
    iprop(Slices.ByteSlice 0 (func19Base - UInt32.ofNat driverDepth) extra ∗
        StackReserve (func19Base - 16) reserve) ⊢
      StackBelow func19Base driverDepth (extra ++ reserve) := by
  have hlow : extra.length = driverDepth - 16 := by rw [hextra]; rfl
  have hle : (16 : Nat) ≤ driverDepth := by decide
  have haddr : func19Base - UInt32.ofNat driverDepth
      + UInt32.ofNat (driverDepth - 16) = func19Base - UInt32.ofNat 16 := by
    decide
  iintro ⟨Hextra, Hreserve⟩
  unfold StackReserve
  icases Hreserve with ⟨%hreserve, Hbytes⟩
  iapply StackBelow_join func19Base driverDepth 16 extra reserve hlow hle haddr
  isplitl_exact Hextra
  · unfold StackBelow
    isplitl_pureexact hreserve
    iexact Hbytes

/-! ## What the tail proves

`DriverTailSpec` is the contract of everything after the read loop.  The
proof of it comes next; the statement is separate so that the driver and
the wrapper can be written against a fixed interface.

The tail takes three things beyond `AfterRead`:

* 224 bytes below the reserve, which together with the reserve make the
  region the callees need;
* the `RandomState` cells, which `collect_entries` reads and writes;
* the bound on the input length, so that the stored length word reads back
  as the number of input bytes.

It gives back the runtime, the restored stack pointer and the output
stream.  It drops the stack bytes, the bump heap and every live block,
which is sound because `ExportSuccess` names only the output stream.

Both error paths write nothing.  A short input, an input whose payload
stops early, and an input with unread bytes left over all reach the same
epilogue, and `Spec.lenOutput` is the empty list on each of them.  That is
what the three lemmas of `Wasm.RustStd.HashMap.BorshBridge` state.
-/

/-- The contract of the `map_len` driver after its read loop. -/
def DriverTailSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (heapId : GName) (capacity ptr aux4 : UInt32)
    (input output : List UInt8)
    (reserve head chunk slice tail extra keysBefore : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterTail : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp},
    iprop(
      AfterRead heapId capacity ptr input reserve head chunk slice tail
        storedCursor frontier history output ∗
      Slices.ByteSlice 0 (func19Base - UInt32.ofNat driverDepth) extra ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      ⌜extra.length = 224 ∧ keysBefore.length = randomStateSize ∧
        input.length < UInt32.size⌝ ∗
      ((∀ finalLocals : Locals,
          RuntimeContext -∗
          StackPointer entryStackTop -∗
          Streams [] (output ++ Project.RustHashMap.Spec.lenOutput input)
            false -∗
          WP (.running
            ⟨finalLocals, afterTail, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }]) ∗
        (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨afterReadLocals (UInt32.ofNat input.length) capacity ptr aux4,
          ReadAll.func19AfterRead ++ afterTail,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]

end Project.RustHashMap.DriverTail
