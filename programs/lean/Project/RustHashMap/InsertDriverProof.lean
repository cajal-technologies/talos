import Project.RustHashMap.InsertTailProof
import Project.RustHashMap.Func3Proof
import Project.RustHashMap.ExportWrappers
import Project.RustHashMap.DriverProof

/-!
# The `map_insert` driver and its public line

Absolute function 3 is the `map_insert` driver, local `func0`.  Its read
phase is proved in `Project.RustHashMap.InsertRead` and its tail in
`Project.RustHashMap.InsertTailProof`.  This file joins the two, and then
carries the result through
`Project.RustHashMap.ExportWrappers.mapInsert_of_driver` to the public
partial contract `Spec.MapInsertSpec`.

Two body contracts stay open: `collect_entries` at absolute function 5,
and the insert shim at absolute function 6.  `Func3Proof.func3_correct_of`
gives the shim under `Func15InsertSpec`, so the second theorem here takes
that contract instead.  Every theorem takes its open contracts as named
hypotheses, so none of them carries `@[proves]`.  The tag goes on when
the two bodies land.

The driver owns 14464 of the 1048576 stack bytes: 368 bytes of frame, 16
bytes of stack reserve, and 14080 bytes below the reserve for its
callees.  `sorted_entries` is the deepest callee, so the region below the
frame is `insertCalleeDepth` bytes, which is 14096.  The split point is
`1048576 - 14464 = 1034112`, and the read phase takes the top 384 bytes.

## The two arms

The read phase of `map_insert` has two exits, so its continuation is a
conjunction.  The non-empty arm stops at WAT 123 and the empty arm at WAT
173.  Each arm hands its own pure side condition to the caller, so this
file needs no case split of its own: the non-empty arm gives
`input ≠ []` and the empty arm gives `input = []`.

## The continuation of the read phase

The driver body is `readPrologue insertMap ++ .block 0 0 insOuterBody ::
insEpilogue`, so the code after the outer block is `insEpilogue`.  The
tail contract names that code `insEpilogue ++ afterTail`.  The driver
returns by falling off the end of its body, so `afterTail` is the empty
program here.
-/

namespace Project.RustHashMap.InsertDriverProof

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
open Project.RustHashMap.MapOpContracts
open Project.RustHashMap.ReadAll
open Project.RustHashMap.InsertRead
open Project.RustHashMap.InsertTailDefs
open Project.RustHashMap.InsertTailContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The input length fits in a word -/

/-- Read the input length bound out of the read-phase result and keep the
result. -/
theorem AfterReadIns_length_lt [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (input reserve head mid chunk top : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8) :
    AfterReadIns heapId capacity ptr input reserve head mid chunk top
        storedCursor frontier history output ⊢
      iprop(⌜input.length < UInt32.size⌝ ∗
        AfterReadIns heapId capacity ptr input reserve head mid chunk top
          storedCursor frontier history output) := by
  iintro Hafter
  isimp only [AfterReadIns] at Hafter
  icases Hafter with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hmid, Hchunk,
    Htop, Hbump, Hstreams, %hshape⟩
  isimp only [VecU8] at Hvec
  icases Hvec with ⟨Hheader, Hlen, Hstorage⟩
  ihave ⟨%hlt, Hstorage⟩ :=
    Project.RustHashMap.DriverProof.VecStorage_length_lt heapId capacity
      ptr input $$ Hstorage
  isplitl_pureexact hlt
  isimp only [AfterReadIns, VecU8]
  iframe
  ipureexact hshape

/-! ## The driver -/

private theorem func0_index :
    Project.RustHashMap.«module».funcs[3 - 3]? =
      some Project.RustHashMap.func0Def := by rfl

private theorem func0Def_body :
    Project.RustHashMap.func0Def.body =
      readPrologue insertMap ++
        .block 0 0 insOuterBody :: insEpilogue :=
  func0_shape

private theorem func0Def_numParams :
    Project.RustHashMap.func0Def.numParams = 0 := rfl

private theorem func0Def_arity :
    Project.RustHashMap.func0Def.results.length = 0 := rfl

set_option maxHeartbeats 2000000 in
/-- The `map_insert` driver, from the entry resources to the return. -/
theorem func0_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (hfunc3 : MapOpContracts.Func3Spec (hlc := hlc)) :
    ExportWrappers.Func0Spec (hlc := hlc) := by
  unfold ExportWrappers.Func0Spec EntrySpec CallContract callExpr
  intro heapId input stackBytes dataBytes randomState callerLocals stack
    code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hstack, Hdata, Hrandom, Hbump, Hstreams, %hlens,
    Hcont, Hoom⟩
  obtain ⟨hstack, hdata, hrandom⟩ := hlens
  -- the 14464 bytes of the driver frame and the region below it
  icases (ByteSlice_split_at 0 1034112 stackBytes
    (by rw [hstack]; decide)).mp $$ Hstack with ⟨_Hlow, Hhigh⟩
  isimp only [UInt32.reduceToNat,
    show (0 : UInt32) + 1034112 = 1034112 by decide] at Hhigh
  icases (ByteSlice_split_at 1034112 14080 (stackBytes.drop 1034112)
    (by rw [List.length_drop, hstack]; decide)).mp $$ Hhigh
    with ⟨Hextra, Hframe⟩
  isimp only [UInt32.reduceToNat,
    show (1034112 : UInt32) = func0Base - UInt32.ofNat insertCalleeDepth
      by decide] at Hextra
  isimp only [UInt32.reduceToNat,
    show (1034112 : UInt32) + 14080 = func0Base - 16 by decide] at Hframe
  have hextra : ((stackBytes.drop 1034112).take 14080).length = 14080 := by
    rw [List.length_take, List.length_drop, hstack]; decide
  have hframe : ((stackBytes.drop 1034112).drop 14080).length = 384 := by
    rw [List.length_drop, List.length_drop, hstack]; decide
  -- enter the driver
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 3
      Project.RustHashMap.func0Def (by decide) func0_index with Hmodule =>
      Hmodule
  simp only [func0Def_numParams, func0Def_arity, func0Def_body,
    List.nil_append, List.take_zero, List.reverse_nil, List.drop_zero]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · isimp only [RuntimeContext]
    iframe
  iapply twp_insert_read_phase
    Project.RustHashMap.DriverProof.func98_correct heapId input []
    ((stackBytes.drop 1034112).drop 14080) 0 heapBase.toNat
    AllocationHistory.empty insEpilogue hframe
  isplitl_exacts [Hruntime Hsp Hframe Hbump Hstreams]
  isplit
  · -- the non-empty arm, WAT 123
    iintro %capacity %ptr %storedCursor' %frontier' %history' %reserve
      %head %mid %chunk %top %byte %length %hne Hafter
    ihave ⟨%hinput, Hafter⟩ :=
      AfterReadIns_length_lt heapId capacity ptr input reserve head mid
        chunk top storedCursor' frontier' history' [] $$ Hafter
    rw [← List.append_nil InsertRead.insEpilogue]
    iapply (InsertTailProof.twp_insert_tail hfunc2 hfunc3).1 heapId
      capacity ptr byte length input [] reserve head mid chunk top
      ((stackBytes.drop 1034112).take 14080) randomState dataBytes
      storedCursor' frontier' history' [] hne
    isplitl_exacts [Hafter Hextra Hrandom Hdata]
    isplitl_pureexact ⟨hextra, hrandom, hdata, hinput⟩
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
          ExportSuccess (Project.RustHashMap.Spec.insertOutput input)
          $$ [Hstreams]
      · iunfold ExportSuccess
        iexists []
        iexact Hstreams
      isimp only [ResumeWP, resumeExpr, List.nil_append] at Hcont
      iapply Hcont $$ Hruntime Hsuccess
    · iexact Hoom
  · isplit
    · -- the empty arm, WAT 173
      iintro %reserve %head %mid %top %hempty Hempty
      rw [← List.append_nil InsertRead.insEpilogue]
      iapply (InsertTailProof.twp_insert_tail hfunc2 hfunc3).2 heapId
        input [] reserve head mid top
        ((stackBytes.drop 1034112).take 14080) dataBytes 0
        heapBase.toNat AllocationHistory.empty [] hempty
      isplitl_exacts [Hempty Hextra Hdata]
      isplitl_pureexact ⟨hextra, hdata⟩
      isplitl [Hcont]
      · isimp only [DriverTailProof.TailDone]
        iintro %finalLocals Hruntime Hsp Hstreams
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
        simp only [List.take_zero, List.nil_append]
        ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
        · isimp only [RuntimeContext]
          iframe
        ihave Hsuccess :
            ExportSuccess (Project.RustHashMap.Spec.insertOutput input)
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

/-- The `map_insert` driver under the contract of `collect_entries` and
the contract of `HashMap::insert`.  `Func3Proof.func3_correct_of` turns
the second one into the contract of the insert shim. -/
theorem func0_correct_of_insert [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (hins : MapOpContracts.Func15InsertSpec (hlc := hlc)) :
    ExportWrappers.Func0Spec (hlc := hlc) :=
  func0_correct_of hfunc2 (Func3Proof.func3_correct_of hins)

/-! ## The public line, conditional on the two open bodies -/

/-- The public partial contract of `map_insert`, conditional on the two
open body contracts.  This theorem is not tagged `@[proves]`, because its
hypotheses are not discharged yet. -/
theorem mapInsert_of_bodies
    (hfunc2 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      CollectContract.Func2Spec (hlc := hlc))
    (hins : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      MapOpContracts.Func15InsertSpec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapInsertSpec :=
  ExportWrappers.mapInsert_of_driver
    (fun {_hlc} [_] => func0_correct_of_insert hfunc2 hins)

end Project.RustHashMap.InsertDriverProof
