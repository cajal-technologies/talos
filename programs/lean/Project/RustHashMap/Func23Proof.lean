import Project.RustHashMap.Func24Proof
import Project.RustHashMap.Func98Proof

/-!
# Proof of the `grow_one` of the pair buffer

This file proves local `func23` (absolute index 26) from `Func24Spec`.
The body is the one that `Project.RustHashMap.Func98Proof` proves at
absolute 101.  Three parts differ.  The header holds no length word.  The
element size is eight bytes.  The capacity floor is four pairs.

The call of the generated `handle_alloc_error` is dead at the result-tag
guard, because `Func24Spec` always reports the tag `0`.  The capacity
bound of `Func23Spec` makes the new layout valid, and so makes
`Func24Spec` apply.
-/

namespace Project.RustHashMap.Func23Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.PairGrow
open Project.RustHashMap.Func98Proof
open scoped Wasm.SmallStep.Outcome

private theorem func23_index :
    Project.RustHashMap.«module».funcs[23]? =
      some Project.RustHashMap.func23Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The `grow_one` of the pair buffer.  It doubles the capacity, keeps a
floor of four pairs, and writes the new capacity and the new pointer back
into the header. -/
theorem func23_correct [WasmSmallStepGS hlc Universal.State] :
    Func23Spec (hlc := hlc) := by
  unfold Func23Spec CallContract callExpr
  intro header sp capacity ptr source shadow heapId storedCursor frontier
    history input output raised callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hreserve, Hheader, Hsource, Hbump, Hstreams,
    %hfacts, Hcont⟩
  rcases hfacts with ⟨hsp, hheader, hcapBound⟩
  have hcapMax : 8 * max (2 * capacity.toNat) 4 ≤ 2147483644 := hcapBound
  let newCapacityNat := pairPushCapacity capacity.toNat
  have hnewUnfold : newCapacityNat = max (2 * capacity.toNat) 4 := rfl
  let newCapacity := UInt32.ofNat newCapacityNat
  let oldLayout : AllocLayout := pairBlock capacity.toNat
  let newLayout : AllocLayout := pairBlock newCapacityNat
  have hsize : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hdoubleBound : 2 * capacity.toNat < UInt32.size := by
    rw [hsize]; omega
  have hnewBound : newCapacityNat < UInt32.size := by
    rw [hnewUnfold, hsize]; omega
  have hnewCapacityWord : newCapacity.toNat = newCapacityNat :=
    UInt32.toNat_ofNat_of_lt' hnewBound
  have hnewFloor : 4 ≤ newCapacityNat := by rw [hnewUnfold]; omega
  have hnewValid : newLayout.Valid := by
    refine ⟨?_, ?_, ⟨2, ?_⟩, ?_, ?_, ?_, ?_⟩
    · show 0 < 8 * newCapacityNat
      omega
    · show 0 < 4
      omega
    · show (4 : Nat) = 2 ^ 2
      norm_num
    · show (4 : Nat) ≤ 2147483648
      omega
    · show 8 * newCapacityNat ≤ 2147483648 - 4
      rw [hnewUnfold]; omega
    · show 8 * newCapacityNat < UInt32.size
      rw [hnewUnfold, hsize]; omega
    · show (4 : Nat) < UInt32.size
      rw [hsize]; omega
  have holdNew : oldLayout.size < newLayout.size := by
    show 8 * capacity.toNat < 8 * newCapacityNat
    rw [hnewUnfold]; omega
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
      (if (if UInt32.ofNat (2 * capacity.toNat) > (4 : UInt32) then
            (1 : UInt32) else 0) ≠ 0 then
          Value.i32 (UInt32.ofNat (2 * capacity.toNat))
        else Value.i32 4) = Value.i32 newCapacity := by
    by_cases hcmp : UInt32.ofNat (2 * capacity.toNat) > (4 : UInt32)
    · rw [if_pos hcmp, if_pos (by decide : (1 : UInt32) ≠ 0)]
      have hn : 4 < 2 * capacity.toNat := by
        change (4 : UInt32) < UInt32.ofNat (2 * capacity.toNat) at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hdoubleBound,
          show (4 : UInt32).toNat = 4 by decide] at hcmp
        exact hcmp
      show Value.i32 (UInt32.ofNat (2 * capacity.toNat)) =
        Value.i32 (UInt32.ofNat newCapacityNat)
      rw [hnewUnfold, max_eq_left (by omega)]
    · rw [if_neg hcmp, if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      have hn : 2 * capacity.toNat ≤ 4 := by
        change ¬ (4 : UInt32) < UInt32.ofNat (2 * capacity.toNat) at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hdoubleBound,
          show (4 : UInt32).toNat = 4 by decide] at hcmp
        omega
      show Value.i32 4 = Value.i32 (UInt32.ofNat newCapacityNat)
      rw [hnewUnfold, max_eq_right hn]
      rfl
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 26
      Project.RustHashMap.func23Def (by decide) func23_index with Hmodule
  simp [Project.RustHashMap.func23Def, Project.RustHashMap.func23,
    Function.toLocals, Function.numParams]
  ihave HreserveParts := (StackReserve_split (sp - 16) shadow).mp $$ Hreserve
  icases HreserveParts with
    ⟨%headBytes, %growBefore, %hshadow, Hhead, HgrowBefore⟩
  isimp only [PairHeader] at Hheader
  icases Hheader with ⟨Hcapacity, Hpointer⟩
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
  wasm_twp_pures [twp_const twp_const]
  have Hfinish : Func24Spec (hlc := hlc) :=
    Project.RustHashMap.Func24Proof.func24_correct
  unfold Func24Spec CallContract callExpr at Hfinish
  simp only [List.cons_append, List.nil_append] at Hfinish
  iapply Hfinish (result := sp - 16 + 4) (oldCapacity := capacity)
    (oldPtr := ptr) (newCapacity := newCapacity) (alignment := 4)
    (elemSize := 8) (oldLayout := oldLayout) (newLayout := newLayout)
    (source := source) (resultBefore := growBefore) (heapId := heapId)
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
    refine ⟨hshadow.2.2, by rw [hf4]; omega, rfl, ?_, rfl, rfl,
      Or.inr rfl, hnewValid, holdNew⟩
    show 8 * newCapacityNat = (8 : UInt32).toNat * newCapacity.toNat
    rw [hnewCapacityWord]
    rfl)
  unfold FinishContinuation
  cases hdecision : classifyBump frontier newLayout with
  | oom =>
      have hdecisionCont :
          classifyBump frontier
            (pairBlock (pairPushCapacity capacity.toNat)) = .oom := by
        simpa only [newLayout, newCapacityNat] using hdecision
      iintro Hresult Hsource Hbump Hstreams
      ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
      ihave Hreserve : StackReserve (sp - 16) shadow $$ [Hhead HresultAt]
      · iapply (StackReserve_split (sp - 16) shadow).mpr
        iexists headBytes, growBefore
        isplitr_pureexact hshadow
        · iframe
      ihave Hsp' : StackPointer (sp - 16) $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      ihave Hheader : PairHeader header capacity ptr $$ [Hcapacity Hpointer]
      · unfold PairHeader
        iframe
      isimp only [PairGrowContinuation, hdecisionCont] at Hcont
      iapply Hcont $$ Hsp' Hreserve Hheader Hsource Hbump Hstreams
  | success newPtr finish =>
      have hdecisionCont :
          classifyBump frontier
            (pairBlock (pairPushCapacity capacity.toNat)) =
            .success newPtr finish := by
        simpa only [newLayout, newCapacityNat] using hdecision
      have hreach := classifyBump_success_reachable frontier newLayout newPtr
        finish hfrontierLow hnewValid (Or.inr rfl) hdecision
      have hfinishLow : frontier + newLayout.size ≤ finish.toNat := by
        have hstart := hreach.1
        have hend := hreach.2.2.2.2.2.1
        omega
      isplit
      · iintro %newBytes Hruntime Hresult Hbump Hblock %hcopy Hstreams
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        isimp only [Slices.ByteSlice, finishResultBytes] at Hresult
        icases Hresult with ⟨%hresultNowrap, HresultBytes⟩
        ihave Harray : arrayAt 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size] $$ [HresultBytes]
        · iapply (Slices.arrayAt_eq_wordCells 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size]).mpr
          iexact HresultBytes
        isimp only [arrayAt] at Harray
        icases Harray with ⟨Htag, HnewPointer, HnewSize, _Hemp⟩
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
        ihave Hcapacity' :=
          pointsTo_u32_address_eq (UInt32.add_zero header).symm $$ Hcapacity
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
        ihave Hheader : PairHeader header newCapacity newPtr $$
            [Hcapacity Hpointer]
        · unfold PairHeader
          iframe
        ihave Harray : arrayAt 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size] $$
            [Htag HnewPointer HnewSize]
        · isimp only [arrayAt]
          isplitl_exact Htag
          isplitl [HnewPointer]
          · iapply pointsTo_u32_address_eq hplus8.symm
            iexact HnewPointer
          isplitl_exact HnewSize
          · itrivial
        ihave HresultBytes : Slices.WordCells 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size] $$ [Harray]
        · iapply (Slices.arrayAt_eq_wordCells 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size]).mp
          iexact Harray
        ihave Hresult : Slices.ByteSlice 0 (sp - 16 + 4)
            (finishResultBytes newPtr (UInt32.ofNat newLayout.size)) $$
            [HresultBytes]
        · unfold Slices.ByteSlice finishResultBytes
          iframe_pureexact using [HresultBytes] => hresultNowrap
        have hheadTake : shadow.take 4 = headBytes := by
          rw [hshadow.1]
          simp [hshadow.2.1]
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve (sp - 16)
            (pairReserveShadow shadow newPtr
              (UInt32.ofNat newLayout.size)) $$ [Hhead HresultAt]
        · iapply (StackReserve_split (sp - 16)
            (pairReserveShadow shadow newPtr
              (UInt32.ofNat newLayout.size))).mpr
          iexists headBytes,
            finishResultBytes newPtr (UInt32.ofNat newLayout.size)
          isplitr_pureexact (by
            refine ⟨?_, hshadow.2.1, finishResultBytes_length _ _⟩
            unfold pairReserveShadow
            rw [hheadTake])
          iframe
        ihave Hsp' : StackPointer sp $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        iclose_map_runtime Hruntime with Hmodule Henv
        isimp only [PairGrowContinuation, hdecisionCont] at Hcont
        ihave Hnormal := BI.and_elim_l $$ Hcont
        isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
        ihave Hnormal := Hnormal $$ %newBytes
          %(finishHistory history source ptr oldLayout newPtr newLayout)
        iapply Hnormal $$ Hruntime Hsp' Hreserve Hheader Hblock Hbump
          %⟨hcopy, hfinishLow⟩ Hstreams
      · iintro Hresult Hsource Hbump Hstreams
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve (sp - 16) shadow $$ [Hhead HresultAt]
        · iapply (StackReserve_split (sp - 16) shadow).mpr
          iexists headBytes, growBefore
          isplitr_pureexact hshadow
          · iframe
        ihave Hsp' : StackPointer (sp - 16) $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        ihave Hheader : PairHeader header capacity ptr $$ [Hcapacity Hpointer]
        · unfold PairHeader
          iframe
        isimp only [PairGrowContinuation, hdecisionCont] at Hcont
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ Hsp' Hreserve Hheader Hsource Hbump Hstreams

end Project.RustHashMap.Func23Proof
