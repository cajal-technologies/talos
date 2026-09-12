import Project.Mergesort.ExactWorkAllocators

/-!
# Normal completion of the driver with growing physical memory

The two work-array allocations update the linear page resource. Decoding,
sorting, output, and cleanup frame it through their existing total contracts.
-/

namespace Project.Mergesort.ExactCompleteDriver

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Contracts Project.Mergesort.Representations
open Project.Mergesort.DriverProof Project.Mergesort.MemoryBounds
open Project.Mergesort.BoundedDriverFacts Project.Mergesort.ExactWorkAllocators
open scoped Wasm.SmallStep.Outcome

theorem complete_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32)
    (capacity inputPtr : UInt32)
    (chunkBytes outputBytes reserveBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hgeo : BoundedGeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity inputPtr frontier history)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(ProgramPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId capacity inputPtr (serialize original) chunkBytes
        outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      (∀ finalLocals : Locals,
        ProgramPages original -∗ RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3AppendLocals inputPtr 0
            (UInt32.ofNat (4 * original.length)) 4 inputPtr 0
            (UInt32.ofNat (4 * original.length)) 0 0 0 [],
          func3AllocationBody, 0, [], func3ScratchSuccessControls, calls⟩ :
            Expr Universal.State) @ s; E [{ Phi }] := by
  let layout : AllocLayout :=
    { size := 4 * original.length, alignment := 4 }
  have hpositive : 0 < original.length :=
    List.length_pos_iff_ne_nil.mpr horiginal
  have hbyteBoundSigned : 4 * original.length < 2147483648 := by
    have htotal := GeometricVecFacts.completed_lt_signed
      (serialize original).length (serialize original).length 0 capacity
      inputPtr frontier history hgeo.1 rfl
    simpa only [serialize_length] using htotal
  have hbyteBound : 4 * original.length < UInt32.size := by
    norm_num [UInt32.size] at hbyteBoundSigned ⊢; omega
  have hlayoutValid : layout.Valid := align4Layout_valid_of_bounds (4 * original.length)
      (by omega) hbyteBoundSigned (by omega)
  have hfrontier : heapBase.toNat ≤ frontier :=
    geometricVec_frontier_ge_heapBase _ _ _ _ _ _ _ hgeo
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone⟩
  have HvaluesAlloc := ExactWorkAllocators.allocate_values heapId original
    capacity inputPtr (serialize original) chunkBytes outputBytes reserveBytes
    storedCursor frontier history horiginal rfl hgeo
    (func3AppendLocals inputPtr 0 (UInt32.ofNat (4 * original.length)) 4
      inputPtr 0 (UInt32.ofNat (4 * original.length)) 0 0 0 [])
    (by
      simp [func3AppendLocals, U32Codec, Spec.u32Codec]) hmode hfit
    (stack := [])
    (code := [.localTee 2, .eqz, .br_if 1] ++ func3DecodeSetup ++
      [.block 0 0 func3DecodeOuterBlockBody,
        .call 7, .localGet 9, .const 2, .shl, .localTee 10,
        .const 4, .call 12] ++ func3ScratchSuccessTail)
    (arity := 0) (remainder := [])
    (controls := func3ScratchSuccessControls) (calls := calls)
    (s := s) (E := E) (Φ := Phi)
  simp only [func3AllocationBody, func3AppendLocals, List.cons_append,
    List.nil_append]
    at HvaluesAlloc ⊢
  iapply HvaluesAlloc
  isplitl_exacts [Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams]
  iintro %valuesPtr %valuesFinish %valuesBytes %hvaluesClassify
    Hpages Hruntime Hsp Hreserve Hframe Hbump Hvalues Hstreams
  have hlineage : ScratchLineage original capacity inputPtr valuesPtr
      history.nextId valuesFinish.toNat (history.allocate valuesPtr layout) := by
    simpa only [layout, serialize_length] using
      BoundedDriverFacts.ScratchLineage.of_values_allocation hgeo hvaluesClassify
  have hvaluesFacts := classifyBump_success_reachable frontier layout
    valuesPtr valuesFinish hfrontier hlayoutValid (Or.inr rfl)
    (by simpa only [layout, serialize_length] using hvaluesClassify)
  have hvaluesEnd :
      valuesPtr.toNat + 4 * original.length ≤ valuesFinish.toNat := by
    rw [hvaluesFacts.2.2.2.2.2.1]
  have hvaluesFrontier : heapBase.toNat ≤ valuesFinish.toNat := Nat.le_trans hfrontier
      (Nat.le_trans hvaluesFacts.1 (by omega))
  unfold ResumeWP resumeExpr
  have Hdecode := twp_func3_decode_allocated heapId history.nextId capacity
    inputPtr valuesPtr original chunkBytes outputBytes valuesBytes frontier
    history 0 4 0 0 0 horiginal hgeo
    (afterDecode := [.call 7, .localGet 9, .const 2, .shl,
      .localTee 10, .const 4, .call 12] ++ func3ScratchSuccessTail)
    (arity := 0) (remainder := [])
    (controls := func3ScratchSuccessControls) (calls := calls)
    (s := s) (E := E) (Φ := Phi)
  simp only [func3AppendLocals, List.append_assoc, List.cons_append,
    List.nil_append]
    at Hdecode ⊢
  iapply_splitl_exact Hdecode with Hframe
  isplitl [Hvalues]
  · isimp only [serialize_length] at Hvalues
    iexact Hvalues
  iintro %final1 %final3 %final6 %final5 %final8 Hframe Hvalues
  have HscratchAlloc := ExactWorkAllocators.allocate_scratch heapId
    history.nextId capacity inputPtr valuesPtr original chunkBytes outputBytes
    reserveBytes valuesFinish valuesFinish.toNat
    (history.allocate valuesPtr layout) final1 final3 final6 final5 final8 0
    hpositive hbyteBoundSigned hvaluesFrontier hvaluesEnd hlineage hmode hfit
    (code := func3ScratchSuccessTail) (arity := 0) (remainder := [])
    (controls := func3ScratchSuccessControls) (calls := calls)
    (s := s) (E := E) (Φ := Phi)
  simp only [func3AppendLocals, List.cons_append, List.nil_append]
    at HscratchAlloc ⊢
  iapply HscratchAlloc
  isplitl_exacts [Hpages Hruntime Hsp Hreserve Hframe Hvalues]
  isplitl [Hbump]
  · isimp only [serialize_length] at Hbump
    iexact Hbump
  isplitl_exact Hstreams
  iintro %scratchPtr %scratchFinish %hscratchClassify
    Hpages Hruntime Hsp Hreserve Hframe Hvalues Hbump Hscratch Hstreams
    %hdisjoint
  have hfinalFrontier := BoundedDriverFacts.ScratchLineage.scratch_finish_le
    hlineage (by simpa only [serialize_length] using hscratchClassify)
  unfold ResumeWP resumeExpr
  have HscratchTail := twp_func3_scratch_success_tail heapId
    (history.allocate valuesPtr layout).nextId scratchPtr layout
    (List.replicate layout.size 0) original.length final1 final3 final6
    valuesPtr inputPtr final5 final8 hbyteBound
    func3_scratch_success_branch
    (arity := 0) (remainder := [])
    (controls := func3ScratchSuccessControls)
    (targetControls := [func3CleanupOuterFrame func3DriverBody])
    (targetCode := func3SortAndCleanup) (calls := calls)
    (s := s) (E := E) (Phi := Phi)
  simp only [func3AppendLocals, List.append_nil] at HscratchTail ⊢
  iapply_frame_intro HscratchTail as Hscratch
  have Hsort := twp_func3_sort heapId history.nextId
    (history.allocate valuesPtr layout).nextId valuesPtr scratchPtr inputPtr
    original (UInt32.ofNat original.length) final3 final6 0
    (UInt32.ofNat (4 * original.length)) hdisjoint hbyteBound
    (code := [.block 0 0 func3OutputBlockBody] ++ func3NonemptyCleanup)
    (arity := 0) (remainder := [])
    (controls := [func3CleanupOuterFrame func3DriverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3SortAndCleanup, func3AppendLocals, List.cons_append,
    List.nil_append] at Hsort ⊢
  iapply Hsort
  isplitl_exacts [Hruntime Hvalues Hscratch]
  iintro %sorted Hruntime Hvalues Hscratch %hsorted
  have hsortedLength : sorted.length = original.length :=
    hsorted.2.length_eq.symm
  have hsortedByteBound : 4 * sorted.length < UInt32.size := by
    simpa only [hsortedLength] using hbyteBound
  let scratchValues : List UInt32 :=
    if original.length ≤ 1 then List.replicate original.length 0
    else sorted
  have hscratchLength : scratchValues.length = sorted.length := by
    dsimp only [scratchValues]
    split <;> simp [hsortedLength]
  have Houtput := twp_func3_output heapId history.nextId capacity inputPtr
    valuesPtr (serialize original) chunkBytes outputBytes sorted
    (UInt32.ofNat original.length) final3 final6 inputPtr 0
    (UInt32.ofNat (4 * original.length)) scratchPtr
    (UInt32.ofNat (4 * original.length)) hsortedByteBound
    (afterOutput := func3NonemptyCleanup) (arity := 0) (remainder := [])
    (controls := [func3CleanupOuterFrame func3DriverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3AppendLocals, hsortedLength, List.cons_append,
    List.nil_append] at Houtput ⊢
  iapply Houtput
  isplitl_exacts [Hruntime Hframe Hvalues Hstreams]
  iintro %outputCursor %final6' %finalOutput Hruntime Hframe Hvalues
    Hstreams
  have Hfinish := twp_func3_finish_nonempty heapId original sorted
    scratchValues capacity inputPtr valuesPtr scratchPtr history.nextId
    (history.allocate valuesPtr layout).nextId chunkBytes finalOutput
    reserveBytes scratchFinish scratchFinish.toNat frontier history
    outputCursor final6' hsorted hpositive hscratchLength hgeo rfl
    (by simp [AllocationHistory.allocate]) hbyteBound hfinalFrontier func3DriverBody
    (calls := calls) (s := s) (E := E) (Phi := Phi)
  simp only [func3AppendLocals, hsortedLength] at Hfinish ⊢
  iapply Hfinish
  isplitl_exacts [Hruntime Hsp Hreserve Hframe Hvalues]
  isplitl [Hscratch]
  · isimp only [scratchValues]
    iexact Hscratch
  isplitl [Hbump]
  · isimp only [layout] at Hbump
    iexact Hbump
  isplitl_exact Hstreams
  iintro Hruntime Hsuccess
  iapply Hdone $$ Hpages Hruntime Hsuccess

/-- Enter the three generated allocation-error blocks after the completed
read, discharge the canonical whole-word/nonempty guards, and hand the exact
innermost continuation to `complete_nonempty`. -/
theorem completed_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32)
    (capacity inputPtr : UInt32)
    (chunkBytes outputBytes reserveBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hgeo : BoundedGeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity inputPtr frontier history)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(ProgramPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId capacity inputPtr (serialize original) chunkBytes
        outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      (∀ finalLocals : Locals,
        ProgramPages original -∗ RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3AppendLocals inputPtr 0
            (UInt32.ofNat (4 * original.length)) 4 0 0 0 0 0 0 [],
          func3CompletedPtrReload ++
            [.block 0 0 func3ScratchOuterBody] ++
            func3ScratchAllocationPanic,
          0, [],
          [func3ReadAndDispatchFrame,
            func3EmptyMiddleFrame func3MiddleBody,
            func3CleanupOuterFrame func3DriverBody],
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone⟩
  have Hreload := twp_func3_reload_completed_ptr heapId capacity inputPtr
    (serialize original) chunkBytes outputBytes 0 4 0 0 0 0 0 0
    (stack := [])
    (code := [.block 0 0 func3ScratchOuterBody] ++
      func3ScratchAllocationPanic)
    (arity := 0) (remainder := [])
    (controls := [func3ReadAndDispatchFrame,
      func3EmptyMiddleFrame func3MiddleBody,
      func3CleanupOuterFrame func3DriverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3CompletedPtrReload, func3AppendLocals, serialize_length,
    List.cons_append, List.nil_append] at Hreload ⊢
  iapply_frame_intro Hreload as Hframe
  wasm_twp_pures [twp_block] using [func3ScratchOuterBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block] using [func3ValuesOuterBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block] using [func3DecodeAllocationBody]
  have Hguards := twp_func3_enter_nonempty_decode original
    (serialize original) capacity inputPtr frontier history horiginal rfl hgeo
    0 4 inputPtr 0 0 0 0 0
    (stack := []) (afterBlock := func3AllocationBody)
    (arity := 0) (remainder := [])
    (controls := func3ScratchSuccessControls) (calls := calls)
    (s := s) (E := E) (Φ := Phi)
  simp only [func3CompletedLengthGuard, func3AppendLocals, serialize_length,
    func3ScratchSuccessControls, func3DecodeAllocationFrame,
    func3ValuesOuterFrame, func3ScratchOuterFrame, List.drop_zero,
    func3DecodeAllocationBody, func3ValuesOuterBody, func3ScratchOuterBody,
    List.cons_append, List.nil_append] at Hguards ⊢
  iapply Hguards
  have Hcomplete := complete_nonempty heapId original
    capacity inputPtr chunkBytes outputBytes reserveBytes storedCursor frontier
    history horiginal hgeo hmode hfit (calls := calls) (s := s) (E := E) (Phi := Phi)
  simp only [func3AppendLocals, func3ScratchSuccessControls,
    func3DecodeAllocationFrame, func3ValuesOuterFrame,
    func3ScratchOuterFrame, func3DecodeAllocationBody,
    func3ValuesOuterBody, func3ScratchOuterBody,
    func3CompletedLengthGuard, List.cons_append, List.nil_append]
    at Hcomplete ⊢
  iapply Hcomplete
  iframe

end Project.Mergesort.ExactCompleteDriver
