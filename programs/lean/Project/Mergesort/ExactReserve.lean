import Project.Mergesort.ExactAllocator
import Project.Mergesort.Func1Proof

/-!
# Reserve with linear exact page ownership

The actual finish-grow and reserve calls carry the updated page token through
allocation, copied bytes, result writeback, and vector-header reconstruction.
Arithmetic acceptance and fit under the physical cap imply normal return.
The token is separate from the persistent allocation-policy interface.
-/

namespace Project.Mergesort.ExactReserve

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Contracts Project.Mergesort.Representations
open Project.Mergesort.Func0Proof Project.Mergesort.Func1Proof
open scoped Wasm.SmallStep.Outcome

/-- Compiled `call 3`, including the first-allocation and copying branches,
returns its updated exact page token with the successful twelve-byte result. -/
theorem twp_func0_call_exact [WasmSmallStepGS hlc Universal.State]
    (result oldCapacity oldPtr newCapacity alignment elementSize : UInt32)
    (source : GrowSource) (initialized growBefore : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (input output : List UInt8) (raised : Bool)
    (newPtr finish : UInt32) (pages cap : Nat)
    (hfacts : alignment = 1 ∧ elementSize = 1 ∧ growBefore.length = 12 ∧
      8 ≤ newCapacity.toNat ∧ oldCapacity.toNat < newCapacity.toNat ∧
      ({ size := newCapacity.toNat, alignment := 1 } : AllocLayout).Valid)
    (hclassify : classifyBump frontier
      { size := newCapacity.toNat, alignment := 1 } = .success newPtr finish)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hpages : pages ≤ cap) (hhard : cap ≤ Module.memoryHardCap)
    (hfit : (allocatorRequiredPages finish).toNat ≤ cap)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    let newLayout : AllocLayout := { size := newCapacity.toNat, alignment := 1 }
    CallContract 3
      [.i32 elementSize, .i32 alignment, .i32 newCapacity, .i32 oldPtr,
        .i32 oldCapacity, .i32 result]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗ memoryCapOwn 0 cap ∗ memoryPagesHalf pages ∗
        ByteSlice result growBefore ∗
        GrowSourceOwn heapId oldCapacity oldPtr initialized source ∗
        BumpHeap heapId storedCursor frontier history ∗ Streams input output raised ∗
        (∀ newBytes : List UInt8, RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
          ByteSlice result (growResultBytes newPtr newCapacity) -∗
          BumpHeap heapId finish finish.toNat
            (growHistory history source oldCapacity oldPtr newPtr newLayout) -∗
          LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
          ⌜growCopied source oldCapacity newBytes ∧
            newBytes.take initialized.length = initialized⌝ -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)) := by
  dsimp only
  unfold CallContract callExpr
  iintro ⟨Hruntime, Hcap, Hexact, Hresult, Hsource, Hbump, Hstreams, Hcont⟩
  isimp only [Representations.ByteSlice] at Hresult
  icases Hresult with ⟨%hresultNowrap, HresultBytes⟩
  ihave Hresult : Representations.ByteSlice result growBefore $$ [HresultBytes]
  · unfold Representations.ByteSlice
    iframe_pureexact using [HresultBytes] => hresultNowrap
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.Mergesort.module 3
      Project.Mergesort.func0Def (by decide) (by rfl) with Hmodule
  simp [Project.Mergesort.func0Def, Project.Mergesort.func0,
    Function.toLocals, Function.numParams]
  rcases hfacts with
    ⟨rfl, rfl, hgrowLength, hnewLower, holdNew, hnewValid⟩
  let newLayout : AllocLayout :=
    { size := newCapacity.toNat, alignment := 1 }
  have hnewMatches : newLayout.Matches newCapacity 1 := by
    unfold AllocLayout.Matches newLayout
    constructor
    · rfl
    · change (1 : UInt32).toNat = 1
      decide
  have hnewUpper : newCapacity.toNat ≤ 2147483647 := by simpa using hnewValid.2.2.2.2.1
  have hhigh :
      UInt64.ofNat newCapacity.toNat >>> (32 : UInt64) = 0 := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_shiftRight]
    rw [show (32 : UInt64).toNat % 64 = 32 by decide]
    norm_num [Nat.shiftRight_eq_div_pow]
    have hword : newCapacity.toNat < 2 ^ 32 := newCapacity.toBitVec.isLt
    omega
  have hwrap :
      UInt32.ofNat
          (newCapacity.toUInt64.toNat % 2 ^ 32) =
        newCapacity := by
    simp
  wasm_twp_pures [twp_const twp_localSet] using [List.length]
  wasm_twp_pures [twp_const twp_localSet] using [List.length]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_extendUI32 twp_localGet
    twp_extendUI32 twp_mulI64]
  have hproduct : UInt64.ofNat (1 : UInt32).toNat *
      UInt64.ofNat newCapacity.toNat = UInt64.ofNat newCapacity.toNat := by
    rw [show (1 : UInt32).toNat = 1 by decide]
    simp
  rw [hproduct]
  wasm_twp_localTee [List.length]
  wasm_twp_pures [twp_constI64 twp_shrUI64]
  rw [show (32 : UInt64) % 64 = 32 by decide, hhigh]
  wasm_twp_pures [twp_wrapI64]
  norm_num
  wasm_twp_pures [twp_eqz]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  wasm_twp_pures [twp_block twp_localGet twp_wrapI64] rewriting [hwrap]
  wasm_twp_localTee [List.set]
  wasm_twp_pures [twp_const twp_localGet twp_sub]
  have hcapacityGuard : newCapacity ≤ (2147483648 : UInt32) - 1 := by
    rw [UInt32.le_iff_toNat_le_toNat]; exact hnewUpper
  iapply twp_leU (result := 1) (by rw [if_pos hcapacityGuard])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_block twp_block twp_block twp_block]
  cases source with
  | empty =>
      isimp only [GrowSourceOwn] at Hsource
      icases Hsource with %hsource
      rcases hsource with ⟨rfl, rfl, rfl⟩
      wasm_twp_pures [twp_localGet twp_eqz]
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      wasm_twp_pures [twp_block twp_localGet]
      have hnewNonzero : newCapacity ≠ 0 := by
        intro hzero
        have := congrArg UInt32.toNat hzero; simp only [UInt32.toNat_zero] at this
        omega
      iapply twp_brIf hnewNonzero (by rfl)
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      have Hmark : Func4Spec (hlc := hlc) :=
        Project.Mergesort.ContractProofs.func4_correct
      unfold Func4Spec CallContract callExpr at Hmark
      simp only [List.nil_append] at Hmark
      iapply Hmark
        (callerLocals :=
          { params := [.i32 result, .i32 0, .i32 1, .i32 newCapacity,
              .i32 1, .i32 1]
            locals := [.i32 1, .i32 4, .i64 newCapacity.toUInt64]
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      · unfold ResumeWP resumeExpr
        simp only [List.nil_append]
        iintro Hruntime
        iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
        wasm_twp_pures [twp_localGet twp_localGet]
        have Halloc := @ExactAllocator.twp_func5_call_exact hlc inferInstance
          newCapacity 1 newLayout heapId storedCursor frontier history newPtr finish
          pages cap input output raised hnewMatches hnewValid (Or.inl rfl)
          hclassify hmode hpages hhard hfit
        unfold CallContract callExpr at Halloc
        simp only [List.cons_append, List.nil_append] at Halloc
        iapply Halloc
          (callerLocals :=
            { params := [.i32 result, .i32 0, .i32 1, .i32 newCapacity,
                .i32 1, .i32 1]
              locals := [.i32 1, .i32 4, .i64 newCapacity.toUInt64]
              values := [] })
          (stack := [])
        isplitl [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isplitl_exacts [Hcap Hexact Hbump Hstreams]
        iintro %newBytes Hruntime Hcap Hexact Hbump Hblock Hstreams
        isimp only [ResumeWP, resumeExpr, List.nil_append,
          List.append_nil]
        wasm_twp_localSet [List.length, List.set]
        wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
        ihave ⟨Hblock, %hnewPtrNonzero⟩ := LiveBlock_with_nonnull heapId
          history.nextId newPtr newLayout newBytes $$ Hblock
        wasm_twp_pures [twp_localGet]
        iapply twp_brIf hnewPtrNonzero (by rfl)
        simp only [List.take_zero, List.nil_append]
        ihave Hnormal := Hcont $$ %newBytes
        have Htail := twp_func0_success_tail
            (source := GrowSource.empty) (result := result)
            (oldCapacity := 0) (oldPtr := 1)
            (newCapacity := newCapacity) (newPtr := newPtr)
            (finish := finish)
            (product := newCapacity.toUInt64)
            (newBytes := newBytes) (growBefore := growBefore)
            (initialized := []) (heapId := heapId)
            (newId := history.nextId)
            (finalHistory := history.allocate newPtr newLayout)
            (input := input) (output := output) (raised := raised)
            (callerLocals := callerLocals) (stack := stack)
            (code := code) (arity := arity) (remainder := remainder)
            (controls := controls) (calls := calls)
            (middleBody := func0MiddleBody)
            (outerBody := func0OuterBody)
            (s := s) (E := E) (Φ := Φ)
            hgrowLength hresultNowrap hnewPtrNonzero (by
              simp [growCopied])
        simp only [func0MiddleBody, func0OuterBody,
          func0FinalCode, Project.Mergesort.func0,
          List.drop, List.length_nil, List.take_zero] at Htail
        iapply Htail
        isimp only [newLayout, growHistory] at Hbump
        isimp only [newLayout, growHistory] at Hblock
        isimp only [newLayout, growHistory] at Hnormal
        isimp only [newLayout, growHistory]
        isplitl_exacts [Hruntime Hresult Hbump Hblock Hstreams]
        · iintro Hruntime Hresult Hbump Hblock Hcopied Hstreams
          try isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          iapply Hnormal $$ Hruntime Hcap Hexact Hresult Hbump Hblock Hcopied Hstreams
  | allocated oldId allBytes spare =>
      isimp only [GrowSourceOwn] at Hsource
      icases Hsource with ⟨%hsource, Hblock⟩
      have holdPositive : 0 < oldCapacity.toNat := hsource.1
      have holdNonzero : oldCapacity ≠ 0 := by
        intro hzero
        have := congrArg UInt32.toNat hzero; simp only [UInt32.toNat_zero] at this
        omega
      let oldLayout : AllocLayout :=
        { size := oldCapacity.toNat, alignment := 1 }
      have holdMatches : oldLayout.Matches oldCapacity 1 := by
        simp [oldLayout, AllocLayout.Matches]
      have holdValid : oldLayout.Valid := by
        change 0 < oldCapacity.toNat ∧ 0 < 1 ∧
          (∃ exponent, 1 = 2 ^ exponent) ∧ 1 ≤ 2147483648 ∧
          oldCapacity.toNat ≤ 2147483648 - 1 ∧
          oldCapacity.toNat < UInt32.size ∧ 1 < UInt32.size
        refine ⟨holdPositive, by omega, ⟨0, by norm_num⟩, by omega,
          ?_, ?_, by norm_num [UInt32.size]⟩
        · omega
        · exact oldCapacity.toBitVec.isLt
      wasm_twp_pures [twp_localGet]
      iapply twp_eqz (by rw [if_neg holdNonzero])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet twp_mul]
      rw [show oldCapacity * (1 : UInt32) = oldCapacity by bv_normalize]
      wasm_twp_pures [twp_localGet twp_localGet]
      have Hrealloc := @ExactAllocator.twp_func8_call_exact hlc inferInstance
        oldPtr oldCapacity newCapacity oldLayout newLayout heapId oldId allBytes
        storedCursor frontier history newPtr finish pages cap input output raised
        ⟨holdMatches, hnewMatches, holdValid, hnewValid, rfl, holdNew⟩
        hclassify hmode hpages hhard hfit
      unfold CallContract callExpr at Hrealloc
      simp only [List.cons_append, List.nil_append] at Hrealloc
      iapply Hrealloc
        (callerLocals :=
          { params := [.i32 result, .i32 oldCapacity, .i32 oldPtr,
              .i32 newCapacity, .i32 1, .i32 1]
            locals := [.i32 1, .i32 4, .i64 newCapacity.toUInt64]
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      isplitl_exacts [Hcap Hexact Hbump Hblock Hstreams]
      iintro %newBytes Hruntime Hcap Hexact Hbump Hblock %hcopy Hstreams
      simp only [oldLayout, newLayout] at hcopy
      rw [min_eq_left (Nat.le_of_lt holdNew)] at hcopy
      isimp only [ResumeWP, resumeExpr, List.nil_append,
        List.append_nil]
      wasm_twp_localSet [List.length, List.set]
      wasm_twp_pures [twp_br] using [List.take_zero, List.nil_append]
      ihave ⟨Hblock, %hnewPtrNonzero⟩ := LiveBlock_with_nonnull heapId
        history.nextId newPtr newLayout newBytes $$ Hblock
      wasm_twp_pures [twp_localGet]
      iapply twp_brIf hnewPtrNonzero (by rfl)
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      have hprefix : newBytes.take initialized.length = initialized := by
        have hcopyInit := congrArg
          (List.take initialized.length) hcopy
        simp only [List.take_take,
          min_eq_left hsource.2.1] at hcopyInit
        rw [hcopyInit, hsource.2.2.1]
        simp
      have hcopied : growCopied
          (.allocated oldId allBytes spare) oldCapacity newBytes ∧
          newBytes.take initialized.length = initialized := by
        constructor
        · unfold growCopied
          have hallLength : allBytes.length = oldCapacity.toNat := by
            rw [hsource.2.2.1, List.length_append,
              hsource.2.2.2]
            omega
          rw [(List.take_eq_self_iff allBytes).mpr hallLength.le] at hcopy; exact hcopy
        · exact hprefix
      ihave Hnormal := Hcont $$ %newBytes
      have Htail := twp_func0_success_tail
          (source := GrowSource.allocated oldId allBytes spare)
          (result := result) (oldCapacity := oldCapacity)
          (oldPtr := oldPtr) (newCapacity := newCapacity)
          (newPtr := newPtr) (finish := finish)
          (product := newCapacity.toUInt64)
          (newBytes := newBytes) (growBefore := growBefore)
          (initialized := initialized) (heapId := heapId)
          (newId := history.nextId)
          (finalHistory := history.reallocate oldId oldPtr oldLayout
            newPtr newLayout)
          (input := input) (output := output) (raised := raised)
          (callerLocals := callerLocals) (stack := stack)
          (code := code) (arity := arity) (remainder := remainder)
          (controls := controls) (calls := calls)
          (middleBody := func0MiddleBody)
          (outerBody := func0OuterBody)
          (s := s) (E := E) (Φ := Φ)
          hgrowLength hresultNowrap hnewPtrNonzero hcopied
      simp only [func0MiddleBody, func0OuterBody,
        func0FinalCode, Project.Mergesort.func0,
        List.drop] at Htail
      iapply Htail
      isimp only [oldLayout, newLayout, growHistory] at Hbump
      isimp only [oldLayout, newLayout, growHistory] at Hblock
      isimp only [oldLayout, newLayout, growHistory] at Hnormal
      isimp only [oldLayout, newLayout, growHistory]
      isplitl_exacts [Hruntime Hresult Hbump Hblock Hstreams]
      · iintro Hruntime Hresult Hbump Hblock Hcopied Hstreams
        try isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        iapply Hnormal $$ Hruntime Hcap Hexact Hresult Hbump Hblock Hcopied Hstreams

/-- Compiled `call 4` restores the reserve stack frame and vector header,
retaining the exact page count and the allocation-history transition. -/
theorem twp_func1_call_exact [WasmSmallStepGS hlc Universal.State]
    (header length additional alignment elementSize : UInt32)
    (totalBytes : Nat) (current remaining : List UInt8)
    (capacity ptr : UInt32) (initialized shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8) (raised : Bool)
    (newPtr finish : UInt32) (pages cap : Nat)
    (hfacts : header = driverBase ∧ alignment = 1 ∧ elementSize = 1 ∧
      length.toNat = initialized.length ∧ additional.toNat = current.length ∧
      current.length = min 256 (current.length + remaining.length) ∧
      0 < current.length ∧ current.length % 4 = 0 ∧
      capacity.toNat - initialized.length < current.length ∧
      totalBytes = initialized.length + current.length + remaining.length ∧
      GeometricVecFacts totalBytes initialized.length
        (current.length + remaining.length) capacity ptr frontier history ∧
      initialized.length + current.length < UInt32.size ∧
      selectedCapacity initialized.length current.length capacity.toNat < UInt32.size ∧
      ({ size := selectedCapacity initialized.length current.length capacity.toNat,
         alignment := 1 } : AllocLayout).Valid)
    (hclassify : classifyBump frontier
      { size := selectedCapacity initialized.length current.length capacity.toNat,
        alignment := 1 } = .success newPtr finish)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hpages : pages ≤ cap) (hhard : cap ≤ Module.memoryHardCap)
    (hfit : (allocatorRequiredPages finish).toNat ≤ cap)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    let newCapacityNat := selectedCapacity initialized.length current.length capacity.toNat
    let newCapacity := UInt32.ofNat newCapacityNat
    let newLayout : AllocLayout := { size := newCapacityNat, alignment := 1 }
    CallContract 4 [.i32 elementSize, .i32 alignment, .i32 additional, .i32 length, .i32 header]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗ memoryCapOwn 0 cap ∗ memoryPagesHalf pages ∗
        StackPointer driverBase ∗ StackReserve reserveBase shadow ∗
        VecU8 heapId driverBase capacity ptr initialized ∗
        BumpHeap heapId storedCursor frontier history ∗ Streams remaining output raised ∗
        (∀ finalHistory : AllocationHistory,
          RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
          StackPointer driverBase -∗
          StackReserve reserveBase (reserveSuccessShadow shadow newPtr newCapacity) -∗
          VecU8 heapId driverBase newCapacity newPtr initialized -∗
          BumpHeap heapId finish finish.toNat finalHistory -∗
          ⌜VecReserveHistory history finalHistory capacity ptr newPtr newLayout ∧
            GeometricVecFacts totalBytes (initialized.length + current.length) remaining.length
              newCapacity newPtr finish.toNat finalHistory⌝ -∗
          Streams remaining output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)) := by
  dsimp only
  unfold CallContract callExpr
  iintro ⟨Hruntime, Hcap, Hexact, Hsp, Hreserve, Hvec, Hbump, Hstreams, Hcont⟩
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
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.Mergesort.module 4
      Project.Mergesort.func1Def (by decide) (by rfl) with Hmodule
  simp [Project.Mergesort.func1Def, Project.Mergesort.func1,
    Function.toLocals, Function.numParams]
  ihave HreserveParts := (StackReserve_split reserveBase shadow).mp $$ Hreserve
  icases HreserveParts with
    ⟨%headBytes, %growBefore, %hshadow, Hhead, HgrowBefore⟩
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩
  ihave ⟨%source, Hsource⟩ := (VecStorage_as_growSource heapId capacity ptr
    initialized).mp $$ Hstorage
  ihave HsourceFacts := growSource_reserveHistory heapId storedCursor
    frontier history capacity ptr initialized source $$ [Hbump Hsource]
  · iframe
  icases HsourceFacts with ⟨Hbump, Hsource, %hreserveHistory⟩
  have hheadWord : UInt32.ofNat headBytes.length = 4 := by
    rw [hshadow.2.1]; decide
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
        norm_num [UInt32.size] at hdoubleBound ⊢; omega),
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
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub] rewriting [show driverBase - 16 = reserveBase by decide]
  wasm_twp_localTee [List.length]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_block twp_localGet twp_localGet twp_add] rewriting [hsumWord]
  wasm_twp_localTee [List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_geU (result := 1) (by
    rw [if_pos (by simpa only [← hsumWord] using hguard)])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add] rewriting [UInt32.add_comm 4 reserveBase]
  wasm_twp_pures [twp_localGet]
  ihave Hcapacity' : pointsTo_u32 0 (driverBase + 0) capacity $$ [Hcapacity]
  · irw_exact [UInt32.add_zero] with Hcapacity
  wasm_twp_bind twp_load32 (address := driverBase) (offset := 0) capacity
      (by decide) (by decide) (by decide) (by decide) with Hcapacity' => Hcapacity
  wasm_twp_localTee [List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_load32 ptr (by decide) (by decide) (by decide) (by decide) $$
    Hpointer
  iintro Hpointer
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
  rw [show (1 : UInt32) % 32 = 1 by decide, hdoubleWord]
  wasm_twp_localTee [List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_gtU]
  iapply twp_select (selected := .i32 (UInt32.ofNat firstMaxNat)) (by
    by_cases hcmp : UInt32.ofNat (initialized.length + current.length) >
        UInt32.ofNat (2 * capacity.toNat)
    · have hw : UInt32.ofNat (initialized.length + current.length) =
          UInt32.ofNat firstMaxNat := by simpa only [if_pos hcmp] using hfirstMaxWord
      rw [if_pos hcmp,
        if_pos (by decide : (1 : UInt32) ≠ 0)]
      exact congrArg Value.i32 hw.symm
    · have hw : UInt32.ofNat (2 * capacity.toNat) =
          UInt32.ofNat firstMaxNat := by simpa only [if_neg hcmp] using hfirstMaxWord
      rw [if_neg hcmp,
        if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      exact congrArg Value.i32 hw.symm)
  wasm_twp_localTee [List.set]
  wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_eq]
  iapply twp_select (selected := .i32 8) (by simp)
  wasm_twp_localTee [List.set]
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
  wasm_twp_localTee [List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  have hfinishFacts : (1 : UInt32) = 1 ∧ (1 : UInt32) = 1 ∧
      growBefore.length = 12 ∧ 8 ≤ newCapacity.toNat ∧
      capacity.toNat < newCapacity.toNat ∧
      ({ size := newCapacity.toNat, alignment := 1 } : AllocLayout).Valid := by
    have hcapacityInitialized : initialized.length ≤ capacity.toNat := by
      rcases hgeo with hempty | hshort | hlarge
      · rcases hempty with ⟨_hcapacity, _hptr, hlength, _hremaining,
          _hfrontier, _hhistory⟩
        omega
      · rcases hshort with ⟨_hremaining, hlength, _htotal, hcapacity,
          _hptr, _hfrontier, _hhistory⟩
        rw [hlength, hcapacity]; exact le_max_left _ _
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
      simpa only [hnewCapacityWord] using hnewValid
    exact ⟨rfl, rfl, hshadow.2.2, by
      rw [hnewCapacityWord]
      unfold newCapacityNat selectedCapacity
      omega, holdNew, hvalid⟩
  have hdecision : classifyBump frontier newLayout = .success newPtr finish := hclassify
  have hdecision' : classifyBump frontier
      { size := newCapacity.toNat, alignment := 1 } = .success newPtr finish := by
    simpa only [newLayout, hnewCapacityWord] using hdecision
  have Hfunc0 := @twp_func0_call_exact hlc inferInstance
    (reserveBase + 4) capacity ptr newCapacity 1 1 source initialized growBefore
    heapId storedCursor frontier history remaining output raised newPtr finish pages cap
    hfinishFacts hdecision' hmode hpages hhard hfit
  dsimp only at Hfunc0
  unfold CallContract callExpr at Hfunc0
  simp only [List.cons_append, List.nil_append] at Hfunc0
  iapply Hfunc0
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
  isplitl_exacts [Hcap Hexact HgrowBeforeAt Hsource Hbump Hstreams]
  iintro %newBytes Hruntime Hcap Hexact Hresult Hbump Hblock %hcopy Hstreams
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
  wasm_twp_rebind twp_load32 (address := reserveBase) (offset := 4) 0
      (by decide) (by decide) (by decide) (by decide) with Htag
  wasm_twp_pures [twp_const]
  iapply twp_ne (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_localGet]
  ihave HnewPointer' : pointsTo_u32 0 (reserveBase + 8) newPtr $$
      [HnewPointer]
  · irw_exact [← show reserveBase + 4 + 4 = reserveBase + 8 by decide] with HnewPointer
  wasm_twp_bind twp_load32 (address := reserveBase) (offset := 8) newPtr
      (by decide) (by decide) (by decide) (by decide) with HnewPointer' => HnewPointer
  wasm_twp_localSet [List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := driverBase) (offset := 0) capacity
      (by decide) (by decide) (by decide) (by decide) with Hcapacity
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := driverBase) (offset := 4) ptr
      (by decide) (by decide) (by decide) (by decide) with Hpointer
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [UInt32.add_comm 16 reserveBase,
    show reserveBase + 16 = driverBase by decide]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
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
    iframe_pureexact using [HresultBytes] => hresultNowrap
  have hheadTake : shadow.take 4 = headBytes := by
    rw [hshadow.1]
    simp [hshadow.2.1]
  ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
  ihave Hreserve : StackReserve reserveBase
      (reserveSuccessShadow shadow newPtr newCapacity) $$ [Hhead HresultAt]
  · iapply (StackReserve_split reserveBase
      (reserveSuccessShadow shadow newPtr newCapacity)).mpr
    iexists headBytes, growResultBytes newPtr newCapacity
    isplitr_pureexact (by
      constructor
      · unfold reserveSuccessShadow
        rw [hheadTake]
      exact ⟨hshadow.2.1, by
        unfold growResultBytes
        rw [serialize_length]
        norm_num⟩)
    iframe
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
  iclose_runtime Hruntime with Hmodule Henv
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
  ihave Hnormal := Hcont
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
  ihave Hnormal := Hnormal $$
    %(growHistory history source capacity ptr newPtr
      { size := selectedCapacity initialized.length current.length
          capacity.toNat, alignment := 1 })
  iapply Hnormal $$ Hruntime Hcap Hexact Hsp' Hreserve Hvec Hbump
    %hnormalFacts Hstreams

end Project.Mergesort.ExactReserve
