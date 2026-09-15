import Project.RustHashMap.ContainsKeyTailProof
import Project.RustHashMap.ExportWrappers
import Project.RustHashMap.DriverProof

/-!
# The `map_contains_key` driver and its public line

Absolute function 19 is the `map_contains_key` driver.  Its read phase is
proved in `Project.RustHashMap.ContainsKeyRead` and its tail in
`Project.RustHashMap.ContainsKeyTailProof`.  This file joins the two, and
then carries the result through
`Project.RustHashMap.ExportWrappers.mapContainsKey_of_driver` to the
public partial contract `Spec.MapContainsKeySpec`.

One body contract stays open: `collect_entries` at absolute function 5.
Every theorem here takes it as a named hypothesis, so neither of them
carries `@[proves]`.  The tag goes on when that body lands.

The driver owns 640 of the 1048576 stack bytes: 304 bytes of frame, and
336 bytes below the frame for its callees.  The key decoder is the
deepest callee, so the region below the frame is `lookupCalleeDepth`
bytes.  The split point is `1048576 - 304 - 336 = 1047936`.
-/

namespace Project.RustHashMap.ContainsKeyDriverProof

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
open Project.RustHashMap.ContainsKeyRead
open Project.RustHashMap.LookupTailDefs
open Project.RustHashMap.ContainsKeyTailProof
open scoped Wasm.SmallStep.Outcome

/-! ## The input length fits in a word -/

/-- Read the input length bound out of the read-phase result and keep the
result. -/
theorem AfterReadCK_length_lt [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (input reserve head chunk : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8) :
    AfterReadCK heapId capacity ptr input reserve head chunk
        storedCursor frontier history output ⊢
      iprop(⌜input.length < UInt32.size⌝ ∗
        AfterReadCK heapId capacity ptr input reserve head chunk
          storedCursor frontier history output) := by
  iintro Hafter
  isimp only [AfterReadCK] at Hafter
  icases Hafter with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hchunk, Hbump,
    Hstreams, %hshape⟩
  isimp only [VecU8] at Hvec
  icases Hvec with ⟨Hheader, Hlen, Hstorage⟩
  ihave ⟨%hlt, Hstorage⟩ :=
    Project.RustHashMap.DriverProof.VecStorage_length_lt heapId capacity
      ptr input $$ Hstorage
  isplitl_pureexact hlt
  isimp only [AfterReadCK, VecU8]
  iframe
  ipureexact hshape

/-! ## The driver -/

private theorem func16_index :
    Project.RustHashMap.«module».funcs[19 - 3]? =
      some Project.RustHashMap.func16Def := by rfl

private theorem func16Def_body :
    Project.RustHashMap.func16Def.body =
      readPrologue containsKeyMap ++
        .block 0 0 (readPhaseBody containsKeyMap) :: func16AfterRead :=
  func16_shape

private theorem func16Def_numParams :
    Project.RustHashMap.func16Def.numParams = 0 := rfl

private theorem func16Def_arity :
    Project.RustHashMap.func16Def.results.length = 0 := rfl

set_option maxHeartbeats 2000000 in
/-- The `map_contains_key` driver, from the entry resources to the
return. -/
theorem func16_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc)) :
    ExportWrappers.Func16Spec (hlc := hlc) := by
  unfold ExportWrappers.Func16Spec EntrySpec CallContract callExpr
  intro heapId input stackBytes dataBytes randomState callerLocals stack
    code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hstack, Hdata, Hrandom, Hbump, Hstreams, %hlens,
    Hcont, Hoom⟩
  obtain ⟨hstack, hdata, hrandom, hstate, hstatic⟩ := hlens
  -- the 640 bytes of the driver frame and the region below it
  icases (ByteSlice_split_at 0 1047936 stackBytes
    (by rw [hstack]; decide)).mp $$ Hstack with ⟨_Hlow, Hhigh⟩
  isimp only [UInt32.reduceToNat,
    show (0 : UInt32) + 1047936 = 1047936 by decide] at Hhigh
  icases (ByteSlice_split_at 1047936 320 (stackBytes.drop 1047936)
    (by rw [List.length_drop, hstack]; decide)).mp $$ Hhigh
    with ⟨Hextra, Hframe⟩
  isimp only [UInt32.reduceToNat,
    show (1047936 : UInt32) = func16Base - UInt32.ofNat lookupCalleeDepth
      by decide] at Hextra
  isimp only [UInt32.reduceToNat,
    show (1047936 : UInt32) + 320 = func16Base - 16 by decide] at Hframe
  have hextra : ((stackBytes.drop 1047936).take 320).length = 320 := by
    rw [List.length_take, List.length_drop, hstack]; decide
  have hframe : ((stackBytes.drop 1047936).drop 320).length = 320 := by
    rw [List.length_drop, List.length_drop, hstack]; decide
  -- enter the driver
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 19
      Project.RustHashMap.func16Def (by decide) func16_index with Hmodule =>
      Hmodule
  simp only [func16Def_numParams, func16Def_arity, func16Def_body,
    List.nil_append, List.take_zero, List.reverse_nil, List.drop_zero]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · isimp only [RuntimeContext]
    iframe
  iapply twp_contains_key_read_phase
    Project.RustHashMap.DriverProof.func98_correct heapId input []
    ((stackBytes.drop 1047936).drop 320) 0 heapBase.toNat
    AllocationHistory.empty func16AfterRead hframe
  isplitl_exacts [Hruntime Hsp Hframe Hbump Hstreams]
  isplit
  · iintro %capacity %ptr %storedCursor' %frontier' %history' %reserve %head
      %chunk %aux4 Hafter
    ihave ⟨%hinput, Hafter⟩ :=
      AfterReadCK_length_lt heapId capacity ptr input reserve head chunk
        storedCursor' frontier' history' [] $$ Hafter
    rw [← List.append_nil ContainsKeyRead.func16AfterRead]
    iapply twp_contains_key_tail hfunc2 heapId capacity ptr aux4 input []
      reserve head chunk ((stackBytes.drop 1047936).take 320) randomState
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
          ExportSuccess (Project.RustHashMap.Spec.containsKeyOutput input)
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

/-- The public partial contract of `map_contains_key`, conditional on the
one open body contract.  This theorem is not tagged `@[proves]`, because
its hypothesis is not discharged yet. -/
theorem mapContainsKey_of_collect
    (hfunc2 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      CollectContract.Func2Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapContainsKeySpec :=
  ExportWrappers.mapContainsKey_of_driver
    (fun {_hlc} [_] => func16_correct_of hfunc2)

end Project.RustHashMap.ContainsKeyDriverProof
