import Project.Mergesort.ExactCompleteDriver
import Project.Mergesort.ExactReadLoop

/-!
# Complete driver with a linear physical-page bound

The exact read loop and the normal post-EOF suffix compose over the generated
body, including its empty-input branch and stack restoration.
-/

namespace Project.Mergesort.ExactDriverBody

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Contracts Project.Mergesort.Representations
open Project.Mergesort.DriverProof Project.Mergesort.MemoryBounds
open Project.Mergesort.ExactReadLoop Project.Mergesort.ExactWorkAllocators
open scoped Wasm.SmallStep.Outcome

theorem read_dispatch_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32)
    (outputBytes reserveBytes : List UInt8)
    (horiginal : original ≠ [])
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(ReadPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      (∀ finalLocals : Locals,
        ProgramPages original -∗ RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3InitializedLocals, func3ReadAndDispatchBody, 0, [],
          [func3ReadAndDispatchFrame,
            func3EmptyMiddleFrame func3MiddleBody,
            func3CleanupOuterFrame func3DriverBody],
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone⟩
  have Hread := ExactReadLoop.initial_read_block_nonempty heapId original
    outputBytes reserveBytes horiginal hmode hfit
    (afterLoop := func3CompletedPtrReload ++
      [.block 0 0 func3ScratchOuterBody] ++
      func3ScratchAllocationPanic)
    (arity := 0) (remainder := [])
    (controls := [func3ReadAndDispatchFrame,
      func3EmptyMiddleFrame func3MiddleBody,
      func3CleanupOuterFrame func3DriverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3ReadAndDispatchBody, func3AfterInitialRead,
    func3InitializedLocals, List.cons_append, List.nil_append] at Hread ⊢
  iapply Hread
  isplitl_exacts [Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams]
  isimp only [ReadLoopContinuation]
  iintro %completed %chunkBytes %finalShadow %finalCapacity %finalPtr
    %finalStoredCursor %finalFrontier %finalHistory Hpages Hruntime Hsp Hreserve
    Hframe Hbump Hstreams %hfacts
  have hgeo : BoundedGeometricVecFacts (serialize original).length
      (serialize original).length 0 finalCapacity finalPtr finalFrontier
      finalHistory := by simpa only [← hfacts.1] using hfacts.2
  isimp only [← hfacts.1] at Hframe
  have Hcompleted := ExactCompleteDriver.completed_nonempty heapId
    original finalCapacity finalPtr chunkBytes outputBytes finalShadow
    finalStoredCursor finalFrontier finalHistory horiginal hgeo hmode hfit
    (calls := calls) (s := s) (E := E) (Phi := Phi)
  simp only [← hfacts.1, func3AppendLocals, serialize_length]
    at Hcompleted ⊢
  iapply Hcompleted
  ihave Hpages := readPages_to_programPages original $$ Hpages
  iframe

/-- Compose the exact nested driver blocks.  The public input is split once:
the empty arm takes the compiler's early branch, while the nonempty arm uses
the read-loop and allocation composition above. -/
theorem after_initialize
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32)
    (outputBytes reserveBytes : List UInt8)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(ReadPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      (∀ finalLocals : Locals,
        ProgramPages original -∗ RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3InitializedLocals, func3AfterInit, 0, [], [], calls⟩ :
          Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone⟩
  rw [func3_after_init_exact]
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block] using [func3DriverBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block] using [func3MiddleBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block] using [func3InitializedLocals, List.drop_zero]
  by_cases horiginal : original = []
  · subst original
    have Hread := twp_func3_initial_read_block_empty heapId outputBytes
      reserveBytes
      (func3CompletedPtrReload ++ [.block 0 0 func3ScratchOuterBody] ++
        func3ScratchAllocationPanic)
      func3ReadAndDispatchBody func3EmptyAfterReadSetup
      (arity := 0) (remainder := [])
      (controls := [func3EmptyMiddleFrame func3MiddleBody,
        func3CleanupOuterFrame func3DriverBody])
      (calls := calls) (s := s) (E := E) (Φ := Phi)
    simp only [func3ReadAndDispatchBody, func3AfterInitialRead,
      func3InitializedLocals, func3EnclosingDriverFrame,
      func3EmptyMiddleFrame, func3CleanupOuterFrame, func3MiddleBody,
      func3DriverBody, func3SortAndCleanup,
      List.cons_append, List.nil_append] at Hread ⊢
    iapply Hread
    isplitl_exacts [Hruntime Hsp Hreserve Hframe Hbump]
    isplitl [Hstreams]
    · isimp only [serialize, WordCodec.serialize, List.flatMap_nil] at Hstreams
      iexact Hstreams
    iintro Hruntime Hsp Hreserve Hframe Hbump Hstreams
    have Hempty := twp_func3_finish_empty heapId
      (List.replicate 256 0) outputBytes reserveBytes func3MiddleBody
      func3DriverBody (calls := calls) (s := s) (E := E) (Phi := Phi)
    simp only [func3EmptyLocals, func3AppendLocals,
      func3EmptyMiddleFrame, func3CleanupOuterFrame, func3MiddleBody,
      func3DriverBody, func3ReadAndDispatchBody, func3AfterInitialRead,
      func3SortAndCleanup, List.cons_append, List.nil_append] at Hempty ⊢
    iapply Hempty
    isplitl_exacts [Hruntime Hsp Hreserve Hframe Hbump Hstreams]
    iintro Hruntime Hsuccess
    ihave Hpages := readPages_to_programPages [] $$ Hpages
    iapply Hdone $$ Hpages Hruntime Hsuccess
  · have Hnonempty := read_dispatch_nonempty heapId original outputBytes reserveBytes horiginal hmode hfit
      (calls := calls) (s := s) (E := E) (Phi := Phi)
    simp only [func3InitializedLocals, func3ReadAndDispatchFrame,
      func3EnclosingDriverFrame, func3EmptyMiddleFrame,
      func3CleanupOuterFrame, func3MiddleBody, func3DriverBody,
      func3SortAndCleanup, List.cons_append,
      List.nil_append] at Hnonempty ⊢
    iapply Hnonempty
    iframe

/-- Execute the generated prologue and the complete reviewed driver body,
stopping at the administrative return boundary. -/
theorem body
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (entryBytes : List UInt8)
    (hentryLength : entryBytes.length = 288)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(ReadPages original ∗
      RuntimeContext ∗
      StackPointer entryStackTop ∗
      StackRegion entryStackLow entryBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      (∀ finalLocals : Locals,
        ProgramPages original -∗ RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
          0, [], [], calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hpages, Hruntime, Hsp, Hstack, Hbump, Hstreams, Hdone⟩
  have Hinitialize := twp_func3_initialize heapId entryBytes
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  iapply Hinitialize
  isplitl_exacts [Hsp Hstack]
  isplitl_pureexact hentryLength
  iintro %reserveBytes %outputBytes Hsp Hreserve Hframe
  have Hbody := after_initialize heapId
    original outputBytes reserveBytes hmode hfit (calls := calls) (s := s) (E := E)
    (Phi := Phi)
  iapply Hbody
  iframe

end Project.Mergesort.ExactDriverBody
