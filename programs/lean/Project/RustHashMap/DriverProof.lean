import Project.RustHashMap.DriverTailProof
import Project.RustHashMap.Func97Proof
import Project.RustHashMap.Func98Proof
import Project.RustHashMap.Func58Proof
import Project.RustHashMap.Adequacy

/-!
# The `map_len` driver and its export wrapper

Absolute function 22 is the `map_len` driver.  Its read phase is proved in
`Project.RustHashMap.ReadAllPhase` and its tail in
`Project.RustHashMap.DriverTailProof`.  This file joins the two, and then
carries the result through the one-instruction wrapper at absolute function
31 to the public partial contract `Spec.MapLenSpec`.

Three body contracts stay open: the borsh decoder at absolute 4, the
`collect_entries` at absolute 5, and `io::Error::new` at absolute 55.  Every
theorem here takes them as named hypotheses, so none of them carries
`@[proves]`.  The tag goes on when the three bodies land.
-/

namespace Project.RustHashMap.DriverProof

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
open Project.RustHashMap.Func55Proof
open Project.RustHashMap.Func58Proof
open Project.RustHashMap.Func97Proof
open Project.RustHashMap.Func98Proof
open Project.RustHashMap.DriverTail
open Project.RustHashMap.DriverTailProof
open Project.RustHashMap.ReadAll
open scoped Wasm.SmallStep.Outcome

/-! ## The two entry contracts -/

/-- Absolute function 22, the `map_len` driver.  It takes the same entry
resources as its wrapper, because the wrapper passes everything through. -/
def Func19Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 22 Project.RustHashMap.Spec.lenOutput

/-! ## The grow contract, which needs no open body -/

/-- The `Vec<u8>` grow path of the read loop.  Its three callees are all
proved, so the read phase takes no hypothesis. -/
theorem func98_correct [WasmSmallStepGS hlc Universal.State] :
    Func98Spec (hlc := hlc) :=
  func98_correct_of (func97_correct_of func55_correct func58_correct)

/-! ## The input length fits in a word -/

/-- Vector storage bounds the initialized prefix by the capacity, so the
length of the input is a word. -/
theorem VecStorage_length_lt [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32) (initialized : List UInt8) :
    VecStorage heapId capacity ptr initialized ⊢
      iprop(⌜initialized.length < UInt32.size⌝ ∗
        VecStorage heapId capacity ptr initialized) := by
  iintro Hstorage
  isimp only [VecStorage] at Hstorage
  icases Hstorage with
    (%hempty | ⟨%allocationId, %allBytes, %spare, %hfacts, Hblock⟩)
  · isplitl_pureexact (by rw [hempty.2.2]; decide)
    isimp only [VecStorage]
    ileft
    ipureexact hempty
  · isplitl_pureexact (by
      have hlt : capacity.toNat < UInt32.size := capacity.toNat_lt_size
      have hle : initialized.length ≤ capacity.toNat := hfacts.2.1
      omega)
    isimp only [VecStorage]
    iright
    iexists allocationId, allBytes, spare
    isplitl_pureexact hfacts
    iexact Hblock

/-- Read the input length bound out of the read-phase result and keep the
result. -/
theorem AfterRead_length_lt [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (input reserve head chunk slice tail : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8) :
    AfterRead heapId capacity ptr input reserve head chunk slice tail
        storedCursor frontier history output ⊢
      iprop(⌜input.length < UInt32.size⌝ ∗
        AfterRead heapId capacity ptr input reserve head chunk slice tail
          storedCursor frontier history output) := by
  iintro Hafter
  isimp only [AfterRead] at Hafter
  icases Hafter with ⟨Hruntime, Hsp, Hreserve, Hhead, Hchunk, Hslice, Hvec,
    Htail, Hbump, Hstreams, %hshape⟩
  isimp only [VecU8] at Hvec
  icases Hvec with ⟨Hheader, Hlen, Hstorage⟩
  ihave ⟨%hlt, Hstorage⟩ :=
    VecStorage_length_lt heapId capacity ptr input $$ Hstorage
  isplitl_pureexact hlt
  isimp only [AfterRead, VecU8]
  iframe
  ipureexact hshape

/-! ## The driver -/

private theorem func19_index :
    Project.RustHashMap.«module».funcs[22 - 3]? =
      some Project.RustHashMap.func19Def := by rfl

private theorem func19Def_body :
    Project.RustHashMap.func19Def.body =
      readPrologue ++ .block 0 0 readPhaseBody :: func19AfterRead :=
  func19_shape

private theorem func19Def_numParams :
    Project.RustHashMap.func19Def.numParams = 0 := rfl

private theorem func19Def_arity :
    Project.RustHashMap.func19Def.results.length = 0 := rfl

/-- The `map_len` driver, from the entry resources to the return. -/
theorem func19_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc)) (hfunc2 : Func2Spec (hlc := hlc))
    (hfunc52 : Func52Spec (hlc := hlc)) :
    Func19Spec (hlc := hlc) := by
  unfold Func19Spec EntrySpec CallContract callExpr
  intro heapId input stackBytes dataBytes randomState callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hstack, Hdata, Hrandom, Hbump, Hstreams, %hlens, Hcont,
    Hoom⟩
  obtain ⟨hstack, hdata, hrandom⟩ := hlens
  -- the 544 bytes of the driver frame and the region below it
  icases (ByteSlice_split_at 0 1048032 stackBytes
    (by rw [hstack]; decide)).mp $$ Hstack with ⟨_Hlow, Hhigh⟩
  isimp only [UInt32.reduceToNat,
    show (0 : UInt32) + 1048032 = 1048032 by decide] at Hhigh
  icases (ByteSlice_split_at 1048032 224 (stackBytes.drop 1048032)
    (by rw [List.length_drop, hstack]; decide)).mp $$ Hhigh
    with ⟨Hextra, Hframe⟩
  isimp only [UInt32.reduceToNat,
    show (1048032 : UInt32) = func19Base - UInt32.ofNat driverDepth
      by decide] at Hextra
  isimp only [UInt32.reduceToNat,
    show (1048032 : UInt32) + 224 = func19Base - 16 by decide] at Hframe
  have hextra : ((stackBytes.drop 1048032).take 224).length = 224 := by
    rw [List.length_take, List.length_drop, hstack]; decide
  have hframe : ((stackBytes.drop 1048032).drop 224).length = 320 := by
    rw [List.length_drop, List.length_drop, hstack]; decide
  -- enter the driver
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 22
      Project.RustHashMap.func19Def (by decide) func19_index with Hmodule =>
      Hmodule
  simp only [func19Def_numParams, func19Def_arity, func19Def_body,
    List.nil_append, List.take_zero, List.reverse_nil, List.drop_zero]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · isimp only [RuntimeContext]
    iframe
  iapply twp_read_phase func98_correct heapId input []
    ((stackBytes.drop 1048032).drop 224) 0 heapBase.toNat
    AllocationHistory.empty func19AfterRead hframe
  isplitl_exacts [Hruntime Hsp Hframe Hbump Hstreams]
  isplit
  · iintro %capacity %ptr %storedCursor' %frontier' %history' %reserve %head
      %chunk %slice %tail %aux4 Hafter
    ihave ⟨%hinput, Hafter⟩ :=
      AfterRead_length_lt heapId capacity ptr input reserve head chunk slice
        tail storedCursor' frontier' history' [] $$ Hafter
    rw [← List.append_nil ReadAll.func19AfterRead]
    iapply twp_driver_tail hfunc1 hfunc2 hfunc52 heapId capacity ptr aux4
      input [] reserve head chunk slice tail
      ((stackBytes.drop 1048032).take 224) randomState storedCursor'
      frontier' history' []
    isplitl_exacts [Hafter Hextra Hrandom]
    isplitl_pureexact ⟨hextra, hrandom, hinput⟩
    isplitl [Hcont]
    · -- the driver falls off the end of its body and returns
      iintro %finalLocals Hruntime Hsp Hstreams
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
      simp only [List.take_zero, List.nil_append]
      ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
      · isimp only [RuntimeContext]
        iframe
      ihave Hsuccess : ExportSuccess (Project.RustHashMap.Spec.lenOutput input)
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

/-! ## The wrapper -/

private theorem func28_index :
    Project.RustHashMap.«module».funcs[31 - 3]? =
      some Project.RustHashMap.func28Def := by rfl

private theorem func28Def_numParams :
    Project.RustHashMap.func28Def.numParams = 0 := rfl

private theorem func28Def_arity :
    Project.RustHashMap.func28Def.results.length = 0 := rfl

private theorem func28Def_toLocals :
    Project.RustHashMap.func28Def.toLocals [] = (⟨[], [], []⟩ : Locals) := rfl

private theorem func28Def_body :
    Project.RustHashMap.func28Def.body = Instruction.call 22 :: [] := rfl

/-- A call contract with no operands, taken from an empty frame, is an
entailment at its call site. -/
private theorem callContract_entails [WasmSmallStepGS hlc Universal.State]
    {absoluteIndex arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    {resources : HeapIProp}
    (h : CallContract absoluteIndex [] (⟨[], [], []⟩ : Locals) [] [] arity
      remainder controls calls s E Φ resources) :
    resources ⊢ WP (.running
        ⟨(⟨[], [], []⟩ : Locals), Instruction.call absoluteIndex :: [], arity,
          remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := h

/-- The `map_len` export wrapper.  Its body is one call. -/
theorem func28_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc19 : Func19Spec (hlc := hlc)) :
    Func28Spec (hlc := hlc) := by
  unfold Func28Spec EntrySpec CallContract callExpr
  intro heapId input stackBytes dataBytes randomState callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hstack, Hdata, Hrandom, Hbump, Hstreams, %hlens, Hcont,
    Hoom⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 31
      Project.RustHashMap.func28Def (by decide) func28_index with Hmodule =>
      Hmodule
  simp only [func28Def_numParams, func28Def_arity, func28Def_toLocals,
    func28Def_body, List.nil_append, List.take_zero, List.reverse_nil,
    List.drop_zero]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · isimp only [RuntimeContext]
    iframe
  iapply callContract_entails (hfunc19 heapId input stackBytes dataBytes
    randomState
    (callerLocals := (⟨[], [], []⟩ : Locals)) (stack := []) (code := [])
    (arity := 0) (remainder := []) (controls := []))
  isplitl_exacts [Hruntime Hsp Hstack Hdata Hrandom Hbump Hstreams]
  isplitl_pureexact hlens
  isplitl [Hcont]
  · iintro Hruntime Hsuccess
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
    simp only [List.take_zero, List.nil_append]
    ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
    · isimp only [RuntimeContext]
      iframe
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hcont
    iapply Hcont $$ Hruntime Hsuccess
  · iexact Hoom

/-! ## The public line, conditional on the three bodies -/

/-- The public partial contract of `map_len`, conditional on the three open
body contracts.  This theorem is not tagged `@[proves]`, because its
hypotheses are not discharged yet. -/
theorem mapLen_of_bodies
    (hfunc1 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func1Spec (hlc := hlc))
    (hfunc2 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func2Spec (hlc := hlc))
    (hfunc52 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func52Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapLenSpec :=
  Project.RustHashMap.Adequacy.len_of_func28
    (fun {_hlc} [_] =>
      func28_correct_of (func19_correct_of hfunc1 hfunc2 hfunc52))

end Project.RustHashMap.DriverProof
