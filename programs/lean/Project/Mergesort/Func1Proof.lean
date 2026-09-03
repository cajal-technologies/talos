import Project.Mergesort.Func0Proof

/-!
# Proof of the generated RawVec reserve wrapper

This file proves local `func1` (absolute Wasm index 4) conditionally from the
authoritative `Func0Spec`.  Its two compiler-generated RawVec panic calls are
excluded at the checked-addition and result-tag guards supplied by the valid
public-input invariants.
-/

namespace Project.Mergesort.Func1Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

private theorem func1_index :
    Project.Mergesort.module.funcs[1]? =
      some Project.Mergesort.func1Def := by
  rfl

private theorem byteSlice_address_eq
    [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {bytes : List UInt8}
    (haddress : address = address') :
    Representations.ByteSlice address bytes ⊢
      Representations.ByteSlice address' bytes := by
  rw [haddress]

private theorem pointsTo_u32_address_eq
    [WasmSmallStepGS hlc Universal.State]
    {address address' value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 0 address value ⊢ pointsTo_u32 0 address' value := by
  rw [haddress]

/-- Preserve the complete allocator/source ownership while extracting the
authoritative live-record lookup needed by `VecReserveHistory`. -/
private theorem growSource_live_lookup
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (oldId : Nat)
    (oldCapacity oldPtr : UInt32) (initialized allBytes spare : List UInt8) :
    iprop(BumpHeap heapId storedCursor frontier history ∗
      GrowSourceOwn heapId oldCapacity oldPtr initialized
        (.allocated oldId allBytes spare)) ⊢
      iprop(BumpHeap heapId storedCursor frontier history ∗
        GrowSourceOwn heapId oldCapacity oldPtr initialized
          (.allocated oldId allBytes spare) ∗
        ⌜get? history.records oldId = some
          (liveMeta oldPtr
            { size := oldCapacity.toNat, alignment := 1 })⌝) := by
  iintro ⟨Hbump, Hsource⟩
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired,
      %ownedPages, Hpages, %hheap⟩
  isimp only [GrowSourceOwn, LiveBlock] at Hsource
  icases Hsource with ⟨%hsource, Htoken, Hbytes, %hblock⟩
  ihave %hlookup : ⌜get? history.records oldId = some
      (liveMeta oldPtr
        { size := oldCapacity.toNat, alignment := 1 })⌝ $$ [Hauth Htoken]
  · iapply AllocMetaAuth_token_agree
    iframe Hauth Htoken
  isplitl [Hcursor Hfrontier Hauth Hretired Hpages]
  · unfold BumpHeap
    iframe Hcursor Hfrontier Hauth Hretired
    iexists ownedPages
    iframe Hpages
    ipureexact hheap
  isplitl [Htoken Hbytes]
  · unfold GrowSourceOwn LiveBlock
    isplitr
    · ipureintro
      exact hsource
    · iframe Htoken Hbytes
      ipureexact hblock
  · ipureintro
    exact hlookup

private theorem growSource_reserveHistory
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (capacity ptr : UInt32)
    (initialized : List UInt8) (source : GrowSource) :
    iprop(BumpHeap heapId storedCursor frontier history ∗
      GrowSourceOwn heapId capacity ptr initialized source) ⊢
      iprop(BumpHeap heapId storedCursor frontier history ∗
        GrowSourceOwn heapId capacity ptr initialized source ∗
        ⌜∀ newPtr : UInt32, ∀ newLayout : AllocLayout,
          VecReserveHistory history
            (growHistory history source capacity ptr newPtr newLayout)
            capacity ptr newPtr newLayout⌝) := by
  cases source with
  | empty =>
      iintro ⟨Hbump, Hsource⟩
      isimp only [GrowSourceOwn] at Hsource
      icases Hsource with %hsource
      isplitl_exact Hbump
      isplitl []
      · unfold GrowSourceOwn
        ipureexact hsource
      · ipureintro
        intro newPtr newLayout
        rcases hsource with ⟨rfl, rfl, rfl⟩
        simp [VecReserveHistory, growHistory]
  | allocated oldId allBytes spare =>
      iintro Hresources
      ihave Hfacts := growSource_live_lookup heapId storedCursor frontier
        history oldId capacity ptr initialized allBytes spare $$ Hresources
      icases Hfacts with ⟨Hbump, Hsource, %hlookup⟩
      isimp only [GrowSourceOwn] at Hsource
      icases Hsource with ⟨%hsource, Hblock⟩
      have hcapacity : capacity ≠ 0 := by
        intro hzero
        have := congrArg UInt32.toNat hzero
        simp only [UInt32.toNat_zero] at this
        omega
      ihave Hsource : GrowSourceOwn heapId capacity ptr initialized
          (.allocated oldId allBytes spare) $$ [Hblock]
      · unfold GrowSourceOwn
        isplitr
        · ipureintro
          exact hsource
        · iexact Hblock
      isplitl_exact Hbump
      isplitl_exact Hsource
      · ipureintro
        intro newPtr newLayout
        unfold VecReserveHistory growHistory
        rw [if_neg hcapacity]
        exact ⟨oldId, hlookup, rfl⟩

theorem func1_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc0 : Func0Spec (hlc := hlc)) :
    Func1Spec (hlc := hlc) := by
  unfold Func1Spec CallContract callExpr
  intro header length additional alignment elementSize totalBytes current
    remaining capacity ptr initialized shadow heapId storedCursor frontier
    history output raised callerLocals stack code arity remainder controls
    calls s E Φ
  dsimp only
  iintro ⟨Hruntime, Hsp, Hreserve, Hvec, Hbump, Hstreams, %hfacts, Hcont⟩
  rcases hfacts with
    ⟨rfl, rfl, rfl, hlengthWord, hadditionalWord, hread, hcurrent,
      hcurrentAlign, hnotFits, htotal, hgeo, hsumBound, hnewBound,
      hnewValid⟩
  let newCapacityNat :=
    selectedCapacity initialized.length current.length capacity.toNat
  let newCapacity := UInt32.ofNat newCapacityNat
  let newLayout : AllocLayout :=
    { size := newCapacityNat, alignment := 1 }
  have hnewCapacityWord : newCapacity.toNat = newCapacityNat :=
    UInt32.toNat_ofNat_of_lt' hnewBound
  have hnewPositive : 0 < newCapacity.toNat := by
    rw [hnewCapacityWord]
    unfold newCapacityNat selectedCapacity
    omega
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 4
      Project.Mergesort.func1Def (by decide) func1_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func1Def, Project.Mergesort.func1,
    Function.toLocals, Function.numParams]
  ihave HreserveParts := (StackReserve_split reserveBase shadow).mp $$ Hreserve
  icases HreserveParts with
    ⟨%headBytes, %growBefore, %hshadow, Hhead, HgrowBefore⟩
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩
  ihave HsourceEx := (VecStorage_as_growSource heapId capacity ptr
    initialized).mp $$ Hstorage
  icases HsourceEx with ⟨%source, Hsource⟩
  ihave HsourceFacts := growSource_reserveHistory heapId storedCursor
    frontier history capacity ptr initialized source $$ [Hbump Hsource]
  · iframe
  icases HsourceFacts with ⟨Hbump, Hsource, %hreserveHistory⟩
  have hheadWord : UInt32.ofNat headBytes.length = 4 := by
    rw [hshadow.2.1]
    decide
  have hgrowAddress :
      reserveBase + UInt32.ofNat headBytes.length = reserveBase + 4 := by
    rw [hheadWord]
  have hlengthBound : initialized.length < UInt32.size := by omega
  have hcurrentBound : current.length < UInt32.size := by omega
  have hlengthOfNat :
      (UInt32.ofNat initialized.length).toNat = initialized.length :=
    UInt32.toNat_ofNat_of_lt' hlengthBound
  have hcurrentOfNat :
      (UInt32.ofNat current.length).toNat = current.length :=
    UInt32.toNat_ofNat_of_lt' hcurrentBound
  have hsumWord :
      length + additional =
        UInt32.ofNat (initialized.length + current.length) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hlengthWord, hadditionalWord,
      Nat.mod_eq_of_lt (by norm_num [UInt32.size] at hsumBound ⊢; omega),
      UInt32.toNat_ofNat_of_lt' hsumBound]
  have hguard : additional ≤ length + additional := by
    rw [UInt32.le_iff_toNat_le_toNat, hsumWord,
      UInt32.toNat_ofNat_of_lt' hsumBound, hadditionalWord]
    omega
  have hdoubleBound : 2 * capacity.toNat < UInt32.size := by
    have hle : 2 * capacity.toNat ≤ newCapacityNat := by
      unfold newCapacityNat selectedCapacity
      omega
    omega
  have hdoubleWord : capacity <<< (1 : UInt32) =
      UInt32.ofNat (2 * capacity.toNat) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_shiftLeft,
      show (1 : UInt32).toNat % 32 = 1 by decide,
      Nat.shiftLeft_eq, pow_one,
      Nat.mod_eq_of_lt (by
        norm_num [UInt32.size] at hdoubleBound ⊢
        omega),
      UInt32.toNat_ofNat_of_lt' hdoubleBound]
    omega
  let firstMaxNat := max (initialized.length + current.length)
    (2 * capacity.toNat)
  have hfirstMaxBound : firstMaxNat < UInt32.size := by
    unfold firstMaxNat
    omega
  have hfirstMaxWord :
      (if UInt32.ofNat (initialized.length + current.length) >
          UInt32.ofNat (2 * capacity.toNat) then
        UInt32.ofNat (initialized.length + current.length)
       else UInt32.ofNat (2 * capacity.toNat)) =
        UInt32.ofNat firstMaxNat := by
    apply UInt32.toNat_inj.mp
    split <;> rename_i hcmp
    · rw [UInt32.toNat_ofNat_of_lt' hsumBound,
        UInt32.toNat_ofNat_of_lt' hfirstMaxBound]
      change initialized.length + current.length =
        max (initialized.length + current.length) (2 * capacity.toNat)
      rw [max_eq_left]
      change UInt32.ofNat (2 * capacity.toNat) <
        UInt32.ofNat (initialized.length + current.length) at hcmp
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hsumBound,
        UInt32.toNat_ofNat_of_lt' hdoubleBound] at hcmp
      omega
    · rw [UInt32.toNat_ofNat_of_lt' hdoubleBound,
        UInt32.toNat_ofNat_of_lt' hfirstMaxBound]
      change 2 * capacity.toNat =
        max (initialized.length + current.length) (2 * capacity.toNat)
      rw [max_eq_right]
      change ¬ UInt32.ofNat (2 * capacity.toNat) <
        UInt32.ofNat (initialized.length + current.length) at hcmp
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hsumBound,
        UInt32.toNat_ofNat_of_lt' hdoubleBound] at hcmp
      omega
  have hselectedWord : UInt32.ofNat (max firstMaxNat 8) = newCapacity := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_ofNat_of_lt' (by
      unfold firstMaxNat newCapacityNat selectedCapacity at *
      omega), hnewCapacityWord]
    unfold newCapacityNat selectedCapacity firstMaxNat
    omega
  isimp only [StackPointer] at Hsp
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  wasm_twp_pures [twp_const twp_sub]
  rw [show driverBase - 16 = reserveBase by decide]
  wasm_twp_pures [twp_localTee]
  simp only [List.length]
  iapply twp_globalSet $$ Hsp
  iintro Hsp
  wasm_twp_pures [twp_block twp_localGet twp_localGet twp_add]
  rw [hsumWord]
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_geU (result := 1) (by
    rw [if_pos (by simpa only [← hsumWord] using hguard)])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [UInt32.add_comm 4 reserveBase]
  wasm_twp_pures [twp_localGet]
  ihave Hcapacity' : pointsTo_u32 0 (driverBase + 0) capacity $$ [Hcapacity]
  · rw [UInt32.add_zero]
    iexact Hcapacity
  iapply twp_load32 (address := driverBase) (offset := 0) capacity
      (by decide) (by decide) (by decide) (by decide) $$ Hcapacity'
  iintro Hcapacity
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_load32 ptr (by decide) (by decide) (by decide) (by decide) $$
    Hpointer
  iintro Hpointer
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
  rw [show (1 : UInt32) % 32 = 1 by decide, hdoubleWord]
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_gtU]
  iapply twp_select (selected := .i32 (UInt32.ofNat firstMaxNat)) (by
    by_cases hcmp : UInt32.ofNat (initialized.length + current.length) >
        UInt32.ofNat (2 * capacity.toNat)
    · have hw : UInt32.ofNat (initialized.length + current.length) =
          UInt32.ofNat firstMaxNat := by
        simpa only [if_pos hcmp] using hfirstMaxWord
      rw [if_pos hcmp,
        if_pos (by decide : (1 : UInt32) ≠ 0)]
      exact congrArg Value.i32 hw.symm
    · have hw : UInt32.ofNat (2 * capacity.toNat) =
          UInt32.ofNat firstMaxNat := by
        simpa only [if_neg hcmp] using hfirstMaxWord
      rw [if_neg hcmp,
        if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      exact congrArg Value.i32 hw.symm)
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_eq]
  iapply twp_select (selected := .i32 8) (by simp)
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_gtU]
  iapply twp_select (selected := .i32 newCapacity) (by
    rw [← hselectedWord]
    by_cases hcmp : UInt32.ofNat firstMaxNat > 8
    · have hn : 8 ≤ firstMaxNat := by
        change (8 : UInt32) < UInt32.ofNat firstMaxNat at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hfirstMaxBound,
          show (8 : UInt32).toNat = 8 by decide] at hcmp
        omega
      simp [hcmp, max_eq_left hn]
    · have hn : firstMaxNat ≤ 8 := by
        change ¬ (8 : UInt32) < UInt32.ofNat firstMaxNat at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hfirstMaxBound,
          show (8 : UInt32).toNat = 8 by decide] at hcmp
        omega
      simp [hcmp, max_eq_right hn])
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  have Hfunc0 : Func0Spec (hlc := hlc) := hfunc0
  unfold Func0Spec CallContract callExpr at Hfunc0
  dsimp only at Hfunc0
  simp only [List.cons_append, List.nil_append] at Hfunc0
  iapply Hfunc0 (result := reserveBase + 4)
    (oldCapacity := capacity) (oldPtr := ptr)
    (newCapacity := newCapacity) (alignment := 1) (elementSize := 1)
    (source := source) (initialized := initialized)
    (growBefore := growBefore) (heapId := heapId)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := remaining) (output := output)
    (raised := raised)
    (callerLocals := {
      params := [.i32 driverBase, .i32 8, .i32 newCapacity, .i32 1, .i32 1]
      locals := [ValueType.i32.zero].set
        (5 - (0 + 1 + 1 + 1 + 1 + 1)) (.i32 reserveBase)
      values := [] })
    (stack := [])
  ihave HgrowBeforeAt := byteSlice_address_eq hgrowAddress $$ HgrowBefore
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl_exact HgrowBeforeAt
  isplitl_exact Hsource
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isplitl []
  · ipureintro
    have hcapacityInitialized : initialized.length ≤ capacity.toNat := by
      rcases hgeo with hempty | hshort | hlarge
      · rcases hempty with ⟨_hcapacity, _hptr, hlength, _hremaining,
          _hfrontier, _hhistory⟩
        omega
      · rcases hshort with ⟨_hremaining, hlength, _htotal, hcapacity,
          _hptr, _hfrontier, _hhistory⟩
        rw [hlength, hcapacity]
        exact le_max_left _ _
      · rcases hlarge with
          ⟨_exponent, _hlower, _hupper, _hcapacity, hlength,
            _htotal, _hptr, _hfrontier, _hhistory⟩
        exact hlength
    have holdNew : capacity.toNat < newCapacity.toNat := by
      rw [hnewCapacityWord]
      unfold newCapacityNat selectedCapacity
      omega
    have hvalid :
        ({ size := newCapacity.toNat, alignment := 1 } : AllocLayout).Valid := by
      rw [hnewCapacityWord]
      exact hnewValid
    exact ⟨rfl, rfl, hshadow.2.2, by
      rw [hnewCapacityWord]
      unfold newCapacityNat selectedCapacity
      omega, holdNew, hvalid⟩
  unfold FinishGrowContinuation
  dsimp only
  cases hdecision : classifyBump frontier newLayout with
  | oom =>
      have hdecisionCont : classifyBump frontier
          { size := selectedCapacity initialized.length current.length
              capacity.toNat, alignment := 1 } = .oom := by
        simpa only [newLayout, newCapacityNat] using hdecision
      have hdecision' : classifyBump frontier
          { size := newCapacity.toNat, alignment := 1 } = .oom := by
        simpa only [newLayout, hnewCapacityWord] using hdecision
      rw [hdecision']
      iintro Hresult Hsource Hbump Hstreams
      ihave HsourceEx : iprop(∃ source,
          GrowSourceOwn heapId capacity ptr initialized source) $$ [Hsource]
      · iexists source
        iexact Hsource
      ihave Hstorage := (VecStorage_as_growSource heapId capacity ptr
        initialized).mpr $$ HsourceEx
      ihave HcapacityBase :=
        pointsTo_u32_address_eq (UInt32.add_zero driverBase) $$ Hcapacity
      ihave Hvec : VecU8 heapId driverBase capacity ptr initialized $$
          [HcapacityBase Hpointer Hlength Hstorage]
      · unfold VecU8 RawVecHeader
        iframe
      ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
      ihave Hreserve : StackReserve reserveBase shadow $$ [Hhead HresultAt]
      · iapply (StackReserve_split reserveBase shadow).mpr
        iexists headBytes, growBefore
        isplitr
        · ipureintro
          exact hshadow
        · iframe
      ihave Hsp' : StackPointer reserveBase $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      isimp only [ReserveContinuation, hdecisionCont] at Hcont
      iapply Hcont $$ Hsp' Hreserve Hvec Hbump Hstreams
  | success newPtr finish =>
      have hdecisionCont : classifyBump frontier
          { size := selectedCapacity initialized.length current.length
              capacity.toNat, alignment := 1 } = .success newPtr finish := by
        simpa only [newLayout, newCapacityNat] using hdecision
      have hdecision' : classifyBump frontier
          { size := newCapacity.toNat, alignment := 1 } =
            .success newPtr finish := by
        simpa only [newLayout, hnewCapacityWord] using hdecision
      rw [hdecision']
      isplit
      · iintro %newBytes Hruntime Hresult Hbump Hblock %hcopy Hstreams
        iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        isimp only [Representations.ByteSlice, growResultBytes] at Hresult
        icases Hresult with ⟨%hresultNowrap, HresultBytes⟩
        ihave Harray : arrayAt 0 (reserveBase + 4)
            [0, newPtr, newCapacity] $$ [HresultBytes]
        · iapply (arrayAt_eq_wordCells (reserveBase + 4)
            [0, newPtr, newCapacity]).mpr
          iexact HresultBytes
        isimp only [arrayAt] at Harray
        icases Harray with ⟨Htag, HnewPointer, HnewCapacity, _Hemp⟩
        wasm_twp_pures [twp_block twp_localGet]
        ihave Htag' : pointsTo_u32 0 (reserveBase + 4) 0 $$ [Htag]
        · iexact Htag
        iapply twp_load32 (address := reserveBase) (offset := 4) 0
            (by decide) (by decide) (by decide) (by decide) $$ Htag'
        iintro Htag
        wasm_twp_pures [twp_const]
        iapply twp_ne (result := 1) (by decide)
        iapply twp_brIf (by decide) (by rfl)
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        wasm_twp_pures [twp_localGet]
        ihave HnewPointer' : pointsTo_u32 0 (reserveBase + 8) newPtr $$
            [HnewPointer]
        · rw [← show reserveBase + 4 + 4 = reserveBase + 8 by decide]
          iexact HnewPointer
        iapply twp_load32 (address := reserveBase) (offset := 8) newPtr
            (by decide) (by decide) (by decide) (by decide) $$ HnewPointer'
        iintro HnewPointer
        wasm_twp_pures [twp_localSet]
        simp only [List.set]
        wasm_twp_pures [twp_localGet twp_localGet]
        iapply twp_store32 (address := driverBase) (offset := 0) capacity
            (by decide) (by decide) (by decide) (by decide) $$ Hcapacity
        iintro Hcapacity
        wasm_twp_pures [twp_localGet twp_localGet]
        iapply twp_store32 (address := driverBase) (offset := 4) ptr
            (by decide) (by decide) (by decide) (by decide) $$ Hpointer
        iintro Hpointer
        wasm_twp_pures [twp_localGet twp_const twp_add]
        rw [UInt32.add_comm 16 reserveBase,
          show reserveBase + 16 = driverBase by decide]
        iapply twp_globalSet $$ Hsp
        iintro Hsp
        iapply twp_returnFromCallFallthrough $$ Hmodule
        iintro Hmodule
        simp only [List.take_zero, List.nil_append]
        ihave HnewStorage := LiveBlock_to_VecStorage heapId history.nextId
          newCapacity newPtr initialized newBytes hnewPositive hcopy.2 $$ Hblock
        ihave HcapacityBase :=
          pointsTo_u32_address_eq (UInt32.add_zero driverBase) $$ Hcapacity
        ihave Hvec : VecU8 heapId driverBase newCapacity newPtr initialized $$
            [HcapacityBase Hpointer Hlength HnewStorage]
        · unfold VecU8 RawVecHeader
          iframe
        ihave Harray : arrayAt 0 (reserveBase + 4)
            [0, newPtr, newCapacity] $$ [Htag HnewPointer HnewCapacity]
        · isimp only [arrayAt]
          isplitl_exact Htag
          isplitl [HnewPointer]
          · iapply pointsTo_u32_address_eq (by decide :
                reserveBase + 8 = reserveBase + 4 + 4)
            iexact HnewPointer
          isplitl_exact HnewCapacity
          · itrivial
        ihave HresultBytes : WordCells (reserveBase + 4)
            [0, newPtr, newCapacity] $$ [Harray]
        · iapply (arrayAt_eq_wordCells (reserveBase + 4)
            [0, newPtr, newCapacity]).mp
          iexact Harray
        ihave Hresult : Representations.ByteSlice (reserveBase + 4)
            (growResultBytes newPtr newCapacity) $$ [HresultBytes]
        · unfold Representations.ByteSlice growResultBytes
          iframe HresultBytes
          ipureexact hresultNowrap
        have hheadTake : shadow.take 4 = headBytes := by
          rw [hshadow.1]
          simp [hshadow.2.1]
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve reserveBase
            (reserveSuccessShadow shadow newPtr newCapacity) $$ [Hhead HresultAt]
        · iapply (StackReserve_split reserveBase
            (reserveSuccessShadow shadow newPtr newCapacity)).mpr
          iexists headBytes, growResultBytes newPtr newCapacity
          isplitr
          · ipureintro
            constructor
            · unfold reserveSuccessShadow
              rw [hheadTake]
            exact ⟨hshadow.2.1, by
              unfold growResultBytes
              rw [serialize_length]
              norm_num⟩
          · iframe
        have hreserve : VecReserveHistory history
            (growHistory history source capacity ptr newPtr newLayout)
            capacity ptr newPtr newLayout :=
          hreserveHistory newPtr newLayout
        have hgeoNew := GeometricVecFacts.reserveSuccess totalBytes
          initialized.length current.length remaining.length capacity ptr
          newPtr finish frontier history
          (growHistory history source capacity ptr newPtr newLayout)
          hgeo hread hcurrent hdecision hreserve
        ihave Hsp' : StackPointer driverBase $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isimp only [newCapacity, newCapacityNat] at Hreserve Hvec
        isimp only [newLayout, newCapacityNat, hnewCapacityWord] at Hbump
        have hnormalFacts :
            VecReserveHistory history
                (growHistory history source capacity ptr newPtr
                  { size := selectedCapacity initialized.length current.length
                      capacity.toNat, alignment := 1 })
                capacity ptr newPtr
                  { size := selectedCapacity initialized.length current.length
                      capacity.toNat, alignment := 1 } ∧
              GeometricVecFacts totalBytes
                (initialized.length + current.length) remaining.length
                (UInt32.ofNat (selectedCapacity initialized.length
                  current.length capacity.toNat)) newPtr finish.toNat
                (growHistory history source capacity ptr newPtr
                  { size := selectedCapacity initialized.length current.length
                      capacity.toNat, alignment := 1 }) := by
          simpa only [newLayout, newCapacityNat] using And.intro hreserve hgeoNew
        isimp only [ReserveContinuation, hdecisionCont] at Hcont
        ihave Hnormal := BI.and_elim_l $$ Hcont
        isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
        ihave Hnormal := Hnormal $$
          %(growHistory history source capacity ptr newPtr
            { size := selectedCapacity initialized.length current.length
                capacity.toNat, alignment := 1 })
        iapply Hnormal $$ Hruntime Hsp' Hreserve Hvec Hbump
          %hnormalFacts Hstreams
      · iintro Hresult Hsource Hbump Hstreams
        ihave HsourceEx : iprop(∃ source,
            GrowSourceOwn heapId capacity ptr initialized source) $$ [Hsource]
        · iexists source
          iexact Hsource
        ihave Hstorage := (VecStorage_as_growSource heapId capacity ptr
          initialized).mpr $$ HsourceEx
        ihave HcapacityBase :=
          pointsTo_u32_address_eq (UInt32.add_zero driverBase) $$ Hcapacity
        ihave Hvec : VecU8 heapId driverBase capacity ptr initialized $$
            [HcapacityBase Hpointer Hlength Hstorage]
        · unfold VecU8 RawVecHeader
          iframe
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve reserveBase shadow $$ [Hhead HresultAt]
        · iapply (StackReserve_split reserveBase shadow).mpr
          iexists headBytes, growBefore
          isplitr
          · ipureintro
            exact hshadow
          · iframe
        ihave Hsp' : StackPointer reserveBase $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        isimp only [ReserveContinuation, hdecisionCont] at Hcont
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ Hsp' Hreserve Hvec Hbump Hstreams

end Project.Mergesort.Func1Proof
