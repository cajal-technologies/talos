import Project.RustHashMap.GetTailProof
import Project.RustHashMap.ExportWrappers
import Project.RustHashMap.DriverProof

/-!
# The `map_get` driver and its public line

Absolute function 21 is the `map_get` driver.  Its read phase is proved
in `Project.RustHashMap.GetRead` and its tail in
`Project.RustHashMap.GetTailProof`.  This file joins the two, and then
carries the result through
`Project.RustHashMap.ExportWrappers.mapGet_of_driver` to the public
partial contract `Spec.MapGetSpec`.

Every theorem here takes one body contract as a named hypothesis:
`collect_entries` at absolute function 5.  Neither of them carries
`@[proves]`.  `Project.RustHashMap.MapGet` discharges the contract and
carries the tag.

The driver owns 656 of the 1048576 stack bytes: 320 bytes of frame, and
336 bytes below the frame for its callees.  The key decoder is the
deepest callee, so the region below the frame is `lookupCalleeDepth`
bytes.  The split point is `1048576 - 320 - 336 = 1047920`.
-/

namespace Project.RustHashMap.GetDriverProof

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
open Project.RustHashMap.GetRead
open Project.RustHashMap.LookupTailDefs
open Project.RustHashMap.GetTailProof
open scoped Wasm.SmallStep.Outcome

/-! ## The input length fits in a word -/

/-- Read the input length bound out of the read-phase result and keep the
result. -/
theorem AfterReadGet_length_lt [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (input reserve head chunk : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8) :
    AfterReadGet heapId capacity ptr input reserve head chunk
        storedCursor frontier history output ⊢
      iprop(⌜input.length < UInt32.size⌝ ∗
        AfterReadGet heapId capacity ptr input reserve head chunk
          storedCursor frontier history output) := by
  iintro Hafter
  isimp only [AfterReadGet] at Hafter
  icases Hafter with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hchunk, Hbump,
    Hstreams, %hshape⟩
  isimp only [VecU8] at Hvec
  icases Hvec with ⟨Hheader, Hlen, Hstorage⟩
  ihave ⟨%hlt, Hstorage⟩ :=
    Project.RustHashMap.DriverProof.VecStorage_length_lt heapId capacity
      ptr input $$ Hstorage
  isplitl_pureexact hlt
  isimp only [AfterReadGet, VecU8]
  iframe
  ipureexact hshape

/-! ## The driver -/

private theorem func18_index :
    Project.RustHashMap.«module».funcs[21 - 3]? =
      some Project.RustHashMap.func18Def := by rfl

private theorem func18Def_body :
    Project.RustHashMap.func18Def.body =
      readPrologue getMap ++
        .block 0 0 (readPhaseBody getMap) :: func18AfterRead :=
  func18_shape

private theorem func18Def_numParams :
    Project.RustHashMap.func18Def.numParams = 0 := rfl

private theorem func18Def_arity :
    Project.RustHashMap.func18Def.results.length = 0 := rfl

set_option maxHeartbeats 2000000 in
/-- The `map_get` driver, from the entry resources to the return. -/
theorem func18_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc)) :
    ExportWrappers.Func18Spec (hlc := hlc) := by
  unfold ExportWrappers.Func18Spec EntrySpec CallContract callExpr
  intro heapId input stackBytes dataBytes randomState callerLocals stack
    code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hstack, Hdata, Hrandom, Hbump, Hstreams, %hlens,
    Hcont, Hoom⟩
  obtain ⟨hstack, hdata, hrandom, hstate, hstatic⟩ := hlens
  -- the 656 bytes of the driver frame and the region below it
  icases (ByteSlice_split_at 0 1047920 stackBytes
    (by rw [hstack]; decide)).mp $$ Hstack with ⟨_Hlow, Hhigh⟩
  isimp only [UInt32.reduceToNat,
    show (0 : UInt32) + 1047920 = 1047920 by decide] at Hhigh
  icases (ByteSlice_split_at 1047920 320 (stackBytes.drop 1047920)
    (by rw [List.length_drop, hstack]; decide)).mp $$ Hhigh
    with ⟨Hextra, Hframe⟩
  isimp only [UInt32.reduceToNat,
    show (1047920 : UInt32) = func18Base - UInt32.ofNat lookupCalleeDepth
      by decide] at Hextra
  isimp only [UInt32.reduceToNat,
    show (1047920 : UInt32) + 320 = func18Base - 16 by decide] at Hframe
  have hextra : ((stackBytes.drop 1047920).take 320).length = 320 := by
    rw [List.length_take, List.length_drop, hstack]; decide
  have hframe : ((stackBytes.drop 1047920).drop 320).length = 336 := by
    rw [List.length_drop, List.length_drop, hstack]; decide
  -- enter the driver
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 21
      Project.RustHashMap.func18Def (by decide) func18_index with Hmodule =>
      Hmodule
  simp only [func18Def_numParams, func18Def_arity, func18Def_body,
    List.nil_append, List.take_zero, List.reverse_nil, List.drop_zero]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · isimp only [RuntimeContext]
    iframe
  iapply twp_get_read_phase
    Project.RustHashMap.DriverProof.func98_correct heapId input []
    ((stackBytes.drop 1047920).drop 320) 0 heapBase.toNat
    AllocationHistory.empty func18AfterRead hframe
  isplitl_exacts [Hruntime Hsp Hframe Hbump Hstreams]
  isplit
  · iintro %capacity %ptr %storedCursor' %frontier' %history' %reserve %head
      %chunk %aux4 Hafter
    ihave ⟨%hinput, Hafter⟩ :=
      AfterReadGet_length_lt heapId capacity ptr input reserve head chunk
        storedCursor' frontier' history' [] $$ Hafter
    rw [← List.append_nil GetRead.func18AfterRead]
    iapply twp_get_tail hfunc2 heapId capacity ptr aux4 input []
      reserve head chunk ((stackBytes.drop 1047920).take 320) randomState
      dataBytes storedCursor' frontier' history' []
    isplitl_exacts [Hafter Hextra Hrandom Hdata]
    isplitl_pureexact ⟨hextra, hrandom, hdata, hstate, hstatic, hinput⟩
    isplitl [Hcont]
    · -- the driver falls off the end of its body and returns
      isimp only [DriverTailProof.TailDone]
      iintro %finalLocals Hruntime Hsp Hstreams
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
      simp only [List.take_zero, List.nil_append]
      ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
      · isimp only [RuntimeContext]
        iframe
      ihave Hsuccess :
          ExportSuccess (Project.RustHashMap.Spec.getOutput input)
          $$ [Hstreams]
      · iunfold ExportSuccess
        iexists []
        iexact Hstreams
      isimp only [ResumeWP, resumeExpr, List.nil_append] at Hcont
      iapply Hcont $$ Hruntime Hsuccess
    · iexact Hoom
  · iintro %remaining' Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining', []
    iexact Hstreams

/-! ## The public line, conditional on `collect_entries` -/

/-- The public partial contract of `map_get`, conditional on the one body
contract.  This theorem keeps it as a hypothesis, so it is not tagged
`@[proves]`; `Project.RustHashMap.MapGet` is. -/
theorem mapGet_of_collect
    (hfunc2 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      CollectContract.Func2Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapGetSpec :=
  ExportWrappers.mapGet_of_driver
    (fun {_hlc} [_] => func18_correct_of hfunc2)

end Project.RustHashMap.GetDriverProof
