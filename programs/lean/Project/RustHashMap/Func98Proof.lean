import Project.RustHashMap.VecGrow

/-!
# Proof of the generated `grow_one`

This file proves local `func98` (absolute index 101) from `Func97Spec`.
The proof follows `Project.Mergesort.Func1Proof`.  The stack pointer is
symbolic, because the five drivers of the program have frames of different
sizes.  The call of the generated `handle_alloc_error` is excluded at the
result-tag guard.
-/

namespace Project.RustHashMap.Func98Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open scoped Wasm.SmallStep.Outcome

private theorem func98_index :
    Project.RustHashMap.«module».funcs[98]? =
      some Project.RustHashMap.func98Def := by rfl

theorem byteSlice_address_eq
    [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {bytes : List UInt8}
    (haddress : address = address') :
    Slices.ByteSlice 0 address bytes ⊢
      Slices.ByteSlice 0 address' bytes := by
  rw [haddress]

theorem pointsTo_u32_address_eq
    [WasmSmallStepGS hlc Universal.State]
    {address address' value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 0 address value ⊢ pointsTo_u32 0 address' value := by
  rw [haddress]

/-- Read the lower frontier bound of the allocator without a change of
ownership. -/
theorem BumpHeap_frontier_lower
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) :
    BumpHeap heapId storedCursor frontier history ⊢
      iprop(BumpHeap heapId storedCursor frontier history ∗
        ⌜heapBase.toNat ≤ frontier⌝) := by
  iintro Hbump
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
  isplitl [Hcursor Hfrontier Hauth Hretired Hpages]
  · unfold BumpHeap
    iframe Hcursor Hfrontier Hauth Hretired
    iexists ownedPages
    iframe_pureexact using [Hpages] => hheap
  · ipureexact hheap.1

theorem func98_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc97 : Func97Spec (hlc := hlc)) :
    Func98Spec (hlc := hlc) := by
  unfold Func98Spec CallContract callExpr
  intro header sp capacity ptr initialized shadow heapId storedCursor
    frontier history input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hreserve, Hvec, Hbump, Hstreams, %hfacts, Hcont⟩
  rcases hfacts with ⟨hsp, hheader, hpush⟩
  obtain ⟨hdoubleBound, hnewBound, hnewLower, holdNew, hnewValid⟩ :=
    hpush.layout
  let newCapacityNat := pushCapacity capacity.toNat
  let newCapacity := UInt32.ofNat newCapacityNat
  let newLayout : AllocLayout :=
    { size := newCapacityNat, alignment := 1 }
  have hsize : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hnewCapacityWord : newCapacity.toNat = newCapacityNat :=
    UInt32.toNat_ofNat_of_lt' hnewBound
  have hnewPositive : 0 < newCapacity.toNat := by
    rw [hnewCapacityWord]
    omega
  have hframe : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using hsp))]
    rfl
  have hf4 : (sp - 16 + 4).toNat = (sp - 16).toNat + 4 := by
    simpa using Slices.byteOffset_toNat (sp - 16) 4 (by omega)
  have hf8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by
    simpa using Slices.byteOffset_toNat (sp - 16) 8 (by omega)
  have hf4_1 : (sp - 16 + 4 + 1).toNat = (sp - 16 + 4).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 4) 1 (by omega)
  have hf4_2 : (sp - 16 + 4 + 2).toNat = (sp - 16 + 4).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 4) 2 (by omega)
  have hf4_3 : (sp - 16 + 4 + 3).toNat = (sp - 16 + 4).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 4) 3 (by omega)
  have hf8_1 : (sp - 16 + 8 + 1).toNat = (sp - 16 + 8).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 8) 1 (by omega)
  have hf8_2 : (sp - 16 + 8 + 2).toNat = (sp - 16 + 8).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 8) 2 (by omega)
  have hf8_3 : (sp - 16 + 8 + 3).toNat = (sp - 16 + 8).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 8) 3 (by omega)
  have hh0_1 : (header + 1).toNat = header.toNat + 1 := by
    simpa using Slices.byteOffset_toNat header 1 (by omega)
  have hh0_2 : (header + 2).toNat = header.toNat + 2 := by
    simpa using Slices.byteOffset_toNat header 2 (by omega)
  have hh0_3 : (header + 3).toNat = header.toNat + 3 := by
    simpa using Slices.byteOffset_toNat header 3 (by omega)
  have hh4 : (header + 4).toNat = header.toNat + 4 := by
    simpa using Slices.byteOffset_toNat header 4 (by omega)
  have hh4_1 : (header + 4 + 1).toNat = (header + 4).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (header + 4) 1 (by omega)
  have hh4_2 : (header + 4 + 2).toNat = (header + 4).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (header + 4) 2 (by omega)
  have hh4_3 : (header + 4 + 3).toNat = (header + 4).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (header + 4) 3 (by omega)
  have hdoubleWord : capacity <<< (1 : UInt32) =
      UInt32.ofNat (2 * capacity.toNat) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_shiftLeft,
      show (1 : UInt32).toNat % 32 = 1 by decide,
      Nat.shiftLeft_eq, pow_one,
      Nat.mod_eq_of_lt (by
        norm_num [UInt32.size] at hdoubleBound ⊢; omega),
      UInt32.toNat_ofNat_of_lt' hdoubleBound]
    omega
  have hselectedWord :
      (if (if UInt32.ofNat (2 * capacity.toNat) > (8 : UInt32) then
            (1 : UInt32) else 0) ≠ 0 then
          Value.i32 (UInt32.ofNat (2 * capacity.toNat))
        else Value.i32 8) = Value.i32 newCapacity := by
    by_cases hcmp : UInt32.ofNat (2 * capacity.toNat) > (8 : UInt32)
    · rw [if_pos hcmp, if_pos (by decide : (1 : UInt32) ≠ 0)]
      have hn : 8 < 2 * capacity.toNat := by
        change (8 : UInt32) < UInt32.ofNat (2 * capacity.toNat) at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hdoubleBound,
          show (8 : UInt32).toNat = 8 by decide] at hcmp
        exact hcmp
      show Value.i32 (UInt32.ofNat (2 * capacity.toNat)) =
        Value.i32 (UInt32.ofNat (pushCapacity capacity.toNat))
      unfold pushCapacity
      rw [max_eq_left (by omega)]
    · rw [if_neg hcmp, if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      have hn : 2 * capacity.toNat ≤ 8 := by
        change ¬ (8 : UInt32) < UInt32.ofNat (2 * capacity.toNat) at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hdoubleBound,
          show (8 : UInt32).toNat = 8 by decide] at hcmp
        omega
      show Value.i32 8 =
        Value.i32 (UInt32.ofNat (pushCapacity capacity.toNat))
      unfold pushCapacity
      rw [max_eq_right hn]
      rfl
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 101
      Project.RustHashMap.func98Def (by decide) func98_index with Hmodule
  simp [Project.RustHashMap.func98Def, Project.RustHashMap.func98,
    Function.toLocals, Function.numParams]
  ihave HreserveParts := (StackReserve_split (sp - 16) shadow).mp $$ Hreserve
  icases HreserveParts with
    ⟨%headBytes, %growBefore, %hshadow, Hhead, HgrowBefore⟩
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩
  ihave ⟨%source, Hsource⟩ := (VecStorage_as_growSource heapId capacity ptr
    initialized).mp $$ Hstorage
  ihave ⟨Hbump, %hfrontierLow⟩ := BumpHeap_frontier_lower heapId storedCursor
    frontier history $$ Hbump
  have hheadWord : UInt32.ofNat headBytes.length = 4 := by
    rw [hshadow.2.1]; decide
  have hgrowAddress :
      sp - 16 + UInt32.ofNat headBytes.length = sp - 16 + 4 := by
    rw [hheadWord]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm 4 (sp - 16)]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr capacity hh0_1 hh0_2 hh0_3 with Hcapacity
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := header) (offset := 4) ptr
      (by simpa using hh4) hh4_1 hh4_2 hh4_3 with Hpointer
  wasm_twp_pures [twp_localGet twp_const twp_shl]
  rw [show (1 : UInt32) % 32 = 1 by decide, hdoubleWord]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_localGet twp_const twp_gtU]
  iapply twp_select (selected := .i32 newCapacity) hselectedWord.symm
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  have Hfunc97 : Func97Spec (hlc := hlc) := hfunc97
  unfold Func97Spec CallContract callExpr at Hfunc97
  dsimp only at Hfunc97
  simp only [List.cons_append, List.nil_append] at Hfunc97
  iapply Hfunc97 (result := sp - 16 + 4)
    (oldCapacity := capacity) (oldPtr := ptr)
    (newCapacity := newCapacity)
    (source := source) (initialized := initialized)
    (growBefore := growBefore) (heapId := heapId)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals := {
      params := [.i32 header]
      locals := [.i32 (sp - 16), .i32 newCapacity, ValueType.i32.zero]
      values := [] })
    (stack := [])
  ihave HgrowBeforeAt := byteSlice_address_eq hgrowAddress $$ HgrowBefore
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl_exacts [HgrowBeforeAt Hsource Hbump Hstreams]
  isplitl_pureexact (by
    refine ⟨hshadow.2.2, ?_, ?_, ?_⟩
    · rw [hnewCapacityWord]; exact hnewLower
    · rw [hnewCapacityWord]; exact holdNew
    · simpa only [hnewCapacityWord] using hnewValid)
  unfold FinishGrowContinuation
  dsimp only
  cases hdecision : classifyBump frontier newLayout with
  | oom =>
      have hdecisionCont : classifyBump frontier
          { size := pushCapacity capacity.toNat, alignment := 1 } = .oom := by
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
      ihave Hvec : VecU8 heapId header capacity ptr initialized $$
          [Hcapacity Hpointer Hlength Hstorage]
      · unfold VecU8 RawVecHeader
        iframe
      ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
      ihave Hreserve : StackReserve (sp - 16) shadow $$ [Hhead HresultAt]
      · iapply (StackReserve_split (sp - 16) shadow).mpr
        iexists headBytes, growBefore
        isplitr_pureexact hshadow
        · iframe
      ihave Hsp' : StackPointer (sp - 16) $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      isimp only [GrowOneContinuation, hdecisionCont] at Hcont
      iapply Hcont $$ Hsp' Hreserve Hvec Hbump Hstreams
  | success newPtr finish =>
      have hdecisionCont : classifyBump frontier
          { size := pushCapacity capacity.toNat, alignment := 1 } =
            .success newPtr finish := by
        simpa only [newLayout, newCapacityNat] using hdecision
      have hdecision' : classifyBump frontier
          { size := newCapacity.toNat, alignment := 1 } =
            .success newPtr finish := by
        simpa only [newLayout, hnewCapacityWord] using hdecision
      rw [hdecision']
      isplit
      · iintro %newBytes Hruntime Hresult Hbump Hblock %hcopy Hstreams
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        isimp only [Slices.ByteSlice, growResultBytes] at Hresult
        icases Hresult with ⟨%hresultNowrap, HresultBytes⟩
        ihave Harray : arrayAt 0 (sp - 16 + 4)
            [0, newPtr, newCapacity] $$ [HresultBytes]
        · iapply (Slices.arrayAt_eq_wordCells 0 (sp - 16 + 4)
            [0, newPtr, newCapacity]).mpr
          iexact HresultBytes
        isimp only [arrayAt] at Harray
        icases Harray with ⟨Htag, HnewPointer, HnewCapacity, _Hemp⟩
        wasm_twp_pures [twp_block twp_localGet]
        wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 4) 0
            (by simpa using hf4) hf4_1 hf4_2 hf4_3 with Htag
        wasm_twp_pures [twp_const]
        iapply twp_ne (result := 1) (by decide)
        iapply twp_brIf (by decide) (by rfl)
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        wasm_twp_pures [twp_localGet]
        have hplus8 : sp - 16 + 4 + 4 = sp - 16 + 8 := by
          simp only [UInt32.add_assoc, UInt32.reduceAdd]
        ihave HnewPointer' : pointsTo_u32 0 (sp - 16 + 8) newPtr $$
            [HnewPointer]
        · irw_exact [← hplus8] with HnewPointer
        wasm_twp_bind twp_load32 (address := sp - 16) (offset := 8) newPtr
            (by simpa using hf8) hf8_1 hf8_2 hf8_3 with HnewPointer' =>
            HnewPointer
        wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        wasm_twp_pures [twp_localGet twp_localGet]
        ihave Hcapacity' := pointsTo_u32_address_eq (UInt32.add_zero header).symm $$
          Hcapacity
        wasm_twp_bind twp_store32 (address := header) (offset := 0) capacity
            (by simp) (by simpa using hh0_1) (by simpa using hh0_2)
            (by simpa using hh0_3) with Hcapacity' => Hcapacity
        isimp only [UInt32.add_zero] at Hcapacity
        wasm_twp_pures [twp_localGet twp_localGet]
        wasm_twp_rebind twp_store32 (address := header) (offset := 4) ptr
            (by simpa using hh4) hh4_1 hh4_2 hh4_3 with Hpointer
        wasm_twp_pures [twp_localGet twp_const twp_add]
        rw [show (16 : UInt32) + (sp - 16) = sp by
          rw [UInt32.add_comm, UInt32.sub_add_cancel]]
        wasm_twp_rebind twp_globalSet with Hsp
        wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
        simp only [List.take_zero, List.nil_append]
        ihave HnewStorage := LiveBlock_to_VecStorage heapId history.nextId
          newCapacity newPtr initialized newBytes hnewPositive hcopy.2 $$
          Hblock
        ihave Hvec : VecU8 heapId header newCapacity newPtr initialized $$
            [Hcapacity Hpointer Hlength HnewStorage]
        · unfold VecU8 RawVecHeader
          iframe
        ihave Harray : arrayAt 0 (sp - 16 + 4)
            [0, newPtr, newCapacity] $$ [Htag HnewPointer HnewCapacity]
        · isimp only [arrayAt]
          isplitl_exact Htag
          isplitl [HnewPointer]
          · iapply pointsTo_u32_address_eq hplus8.symm
            iexact HnewPointer
          isplitl_exact HnewCapacity
          · itrivial
        ihave HresultBytes : Slices.WordCells 0 (sp - 16 + 4)
            [0, newPtr, newCapacity] $$ [Harray]
        · iapply (Slices.arrayAt_eq_wordCells 0 (sp - 16 + 4)
            [0, newPtr, newCapacity]).mp
          iexact Harray
        ihave Hresult : Slices.ByteSlice 0 (sp - 16 + 4)
            (growResultBytes newPtr newCapacity) $$ [HresultBytes]
        · unfold Slices.ByteSlice growResultBytes
          iframe_pureexact using [HresultBytes] => hresultNowrap
        have hheadTake : shadow.take 4 = headBytes := by
          rw [hshadow.1]
          simp [hshadow.2.1]
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve (sp - 16)
            (reserveSuccessShadow shadow newPtr newCapacity) $$
            [Hhead HresultAt]
        · iapply (StackReserve_split (sp - 16)
            (reserveSuccessShadow shadow newPtr newCapacity)).mpr
          iexists headBytes, growResultBytes newPtr newCapacity
          isplitr_pureexact (by
            constructor
            · unfold reserveSuccessShadow
              rw [hheadTake]
            exact ⟨hshadow.2.1, by
              unfold growResultBytes
              rw [WordCodec.u32le_serialize_length]
              rfl⟩)
          iframe
        have hpushNew := PushVecFacts.growSuccess newPtr finish hpush
          hfrontierLow hdecisionCont
        ihave Hsp' : StackPointer sp $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        iclose_map_runtime Hruntime with Hmodule Henv
        isimp only [newCapacity, newCapacityNat] at Hreserve Hvec
        isimp only [GrowOneContinuation, hdecisionCont] at Hcont
        ihave Hnormal := BI.and_elim_l $$ Hcont
        isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
        ihave Hnormal := Hnormal $$
          %(growHistory history source capacity ptr newPtr
            { size := newCapacity.toNat, alignment := 1 })
        iapply Hnormal $$ Hruntime Hsp' Hreserve Hvec Hbump %hpushNew Hstreams
      · iintro Hresult Hsource Hbump Hstreams
        ihave HsourceEx : iprop(∃ source,
            GrowSourceOwn heapId capacity ptr initialized source) $$ [Hsource]
        · iexists source
          iexact Hsource
        ihave Hstorage := (VecStorage_as_growSource heapId capacity ptr
          initialized).mpr $$ HsourceEx
        ihave Hvec : VecU8 heapId header capacity ptr initialized $$
            [Hcapacity Hpointer Hlength Hstorage]
        · unfold VecU8 RawVecHeader
          iframe
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve (sp - 16) shadow $$ [Hhead HresultAt]
        · iapply (StackReserve_split (sp - 16) shadow).mpr
          iexists headBytes, growBefore
          isplitr_pureexact hshadow
          · iframe
        ihave Hsp' : StackPointer (sp - 16) $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        isimp only [GrowOneContinuation, hdecisionCont] at Hcont
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ Hsp' Hreserve Hvec Hbump Hstreams

end Project.RustHashMap.Func98Proof
