import Project.Mergesort.MemoryBounds

/-!
# Bounded bookkeeping at the merge-sort driver's existing interfaces

These lemmas preserve the input-capacity fact through the byte-list updates
used by `twp_func3_read_loop`. The driver carries these facts through its
continuations, including the first work allocation's classification and history
at the values-to-scratch boundary. These arithmetic helpers do not establish
physical grow success or a page bound.
-/

namespace Project.Mergesort.BoundedDriverFacts

open Wasm Wasm.SmallStep Iris
open Std
open Project.Mergesort.Representations Project.Mergesort.MemoryBounds

/-- The pure part of an active canonical driver iteration.  Each field
corresponds to an existing `Func3ReadLoopInv` clause, with bounded lineage. -/
structure ReadFacts (original : List UInt32)
    (initialized current remaining : List UInt8)
    (capacity dataPtr : UInt32) (frontier : Nat)
    (history : AllocationHistory) : Prop where
  partition : serialize original = initialized ++ current ++ remaining
  chunk_shape : current.length = min 256 (current.length + remaining.length)
  chunk_positive : 0 < current.length
  chunk_mod : current.length % 4 = 0
  remaining_mod : remaining.length % 4 = 0
  bounded : BoundedGeometricVecFacts (serialize original).length
    initialized.length (current.length + remaining.length)
    capacity dataPtr frontier history

/-- Pure facts after the current chunk has been appended and before the next
read.  The remaining bytes are exactly the concrete stdio host's input. -/
structure AppendFacts (original : List UInt32)
    (initialized remaining : List UInt8)
    (capacity dataPtr : UInt32) (frontier : Nat)
    (history : AllocationHistory) : Prop where
  partition : serialize original = initialized ++ remaining
  remaining_mod : remaining.length % 4 = 0
  bounded : BoundedGeometricVecFacts (serialize original).length
    initialized.length remaining.length capacity dataPtr frontier history

/-- Compatibility with the exact old loop-invariant payload. -/
theorem ReadFacts.forget
    {original : List UInt32} {initialized current remaining : List UInt8}
    {capacity dataPtr : UInt32} {frontier : Nat} {history : AllocationHistory}
    (h : ReadFacts original initialized current remaining
      capacity dataPtr frontier history) :
    serialize original = initialized ++ current ++ remaining ∧
      current.length = min 256 (current.length + remaining.length) ∧
      0 < current.length ∧ current.length ≤ 256 ∧
      current.length % 4 = 0 ∧ remaining.length % 4 = 0 ∧
      GeometricVecFacts (serialize original).length initialized.length
        (current.length + remaining.length) capacity dataPtr frontier history :=
  ⟨h.partition, h.chunk_shape, h.chunk_positive,
    h.chunk_shape ▸ min_le_left _ _, h.chunk_mod, h.remaining_mod, h.bounded.1⟩

/-- The total byte count needed by the reserve call follows from the actual
serialized-input partition, including bytes already consumed by the host. -/
theorem ReadFacts.total_length
    {original : List UInt32} {initialized current remaining : List UInt8}
    {capacity dataPtr : UInt32} {frontier : Nat} {history : AllocationHistory}
    (h : ReadFacts original initialized current remaining
      capacity dataPtr frontier history) :
    4 * original.length = initialized.length + current.length + remaining.length := by
  have hlength := congrArg List.length h.partition
  simpa only [serialize_length, List.length_append] using hlength

/-- After appending, the next concrete 256-byte read reconstructs the active
loop invariant while preserving the same bounded allocation lineage. -/
theorem AppendFacts.next
    {original : List UInt32} {initialized remaining : List UInt8}
    {capacity dataPtr : UInt32} {frontier : Nat} {history : AllocationHistory}
    (h : AppendFacts original initialized remaining capacity dataPtr frontier history)
    (hne : remaining ≠ []) :
    ReadFacts original initialized
      (remaining.take (min 256 remaining.length))
      (remaining.drop (min 256 remaining.length))
      capacity dataPtr frontier history := by
  have hpositive : 0 < remaining.length := List.length_pos_iff_ne_nil.mpr hne
  have hsplitLength :
      (remaining.take (min 256 remaining.length)).length +
        (remaining.drop (min 256 remaining.length)).length = remaining.length := by
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc, List.take_append_drop] using h.partition
  · rw [hsplitLength]
    simp
  · simp only [List.length_take]
    omega
  · simp only [List.length_take]
    have hmod := h.remaining_mod
    omega
  · simp only [List.length_drop]
    have hmod := h.remaining_mod
    omega
  · simpa only [hsplitLength] using h.bounded

/-- Initial bookkeeping after the canonical nonempty input's first read.
The allocator history is still empty; no allocation success is assumed. -/
theorem ReadFacts.initial (original : List UInt32) (hne : original ≠ []) :
    ReadFacts original []
      ((serialize original).take (min 256 (serialize original).length))
      ((serialize original).drop (min 256 (serialize original).length))
      0 1 heapBase.toNat AllocationHistory.empty := by
  have hinput : serialize original ≠ [] := by
    intro heq
    have hlen := congrArg List.length heq
    simp only [serialize_length, List.length_nil] at hlen
    exact hne (List.eq_nil_of_length_eq_zero (by omega))
  apply AppendFacts.next (hne := hinput)
  refine ⟨by simp, by rw [serialize_length]; omega, ?_⟩
  exact BoundedGeometricVecFacts.initial _

/-- The no-reserve capacity branch updates only the initialized byte list. -/
theorem ReadFacts.append_without_reserve
    {original : List UInt32} {initialized current remaining : List UInt8}
    {capacity dataPtr : UInt32} {frontier : Nat} {history : AllocationHistory}
    (h : ReadFacts original initialized current remaining
      capacity dataPtr frontier history)
    (hfits : current.length ≤ capacity.toNat - initialized.length) :
    AppendFacts original (initialized ++ current) remaining
      capacity dataPtr frontier history := by
  refine ⟨h.partition, h.remaining_mod, ?_⟩
  simpa only [List.length_append] using
    BoundedGeometricVecFacts.appendWithoutReserve
      (serialize original).length initialized.length current.length remaining.length
      capacity dataPtr frontier history h.bounded h.chunk_positive hfits

/-- The reserve branch keeps its selected-capacity relationship.  These are
the exact classification and history outputs of `Func3ReserveContinuation`;
no new assumption about allocator execution is introduced. -/
theorem ReadFacts.append_after_reserve
    {original : List UInt32} {initialized current remaining : List UInt8}
    {capacity dataPtr newPtr finish : UInt32} {frontier : Nat}
    {history finalHistory : AllocationHistory}
    (h : ReadFacts original initialized current remaining
      capacity dataPtr frontier history)
    (hreserve : capacity.toNat - initialized.length < current.length)
    (hclassify : classifyBump frontier
      { size := selectedCapacity initialized.length current.length capacity.toNat,
        alignment := 1 } = .success newPtr finish)
    (hhistory : VecReserveHistory history finalHistory capacity dataPtr newPtr
      { size := selectedCapacity initialized.length current.length capacity.toNat,
        alignment := 1 }) :
    AppendFacts original (initialized ++ current) remaining
      (UInt32.ofNat (selectedCapacity initialized.length current.length capacity.toNat))
      newPtr finish.toNat finalHistory := by
  refine ⟨h.partition, h.remaining_mod, ?_⟩
  simpa only [List.length_append] using
    BoundedGeometricVecFacts.reserveSuccess (serialize original).length
      initialized.length current.length remaining.length capacity dataPtr newPtr finish
      frontier history finalHistory h.bounded h.chunk_shape h.chunk_positive
      (by omega) hclassify hhistory

/-- At EOF the very same input-dependent bound becomes the values-allocation
precondition, retaining the completed input's actual allocation history. -/
theorem AppendFacts.completed
    {original : List UInt32} {initialized : List UInt8}
    {capacity dataPtr : UInt32} {frontier : Nat} {history : AllocationHistory}
    (h : AppendFacts original initialized [] capacity dataPtr frontier history) :
    serialize original = initialized ∧
      BoundedGeometricVecFacts (serialize original).length
        (serialize original).length 0 capacity dataPtr frontier history := by
  have heq : serialize original = initialized := by simpa using h.partition
  exact ⟨heq, by simpa only [heq, List.length_nil] using h.bounded⟩

/-- The existing loop's well-founded measure still decreases under the exact
next-read bookkeeping; adding the memory bound changes no termination metric. -/
theorem ReadFacts.next_measure_lt
    {original : List UInt32} {initialized current remaining : List UInt8}
    {capacity dataPtr : UInt32} {frontier : Nat} {history : AllocationHistory}
    (h : ReadFacts original initialized current remaining
      capacity dataPtr frontier history) :
    (remaining.take (min 256 remaining.length)).length +
        (remaining.drop (min 256 remaining.length)).length <
      current.length + remaining.length := by
  simp
  exact h.chunk_positive

/-- Direct packaging of the existing values-allocation success continuation.
The matching `BumpHeap` and `LiveBlock` resources already carry these indices. -/
theorem ScratchLineage.of_values_allocation
    {original : List UInt32} {capacity dataPtr valuesPtr valuesFinish : UInt32}
    {inputFrontier : Nat} {inputHistory : AllocationHistory}
    (hbounded : BoundedGeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity dataPtr inputFrontier inputHistory)
    (hclassify : classifyBump inputFrontier
        { size := (serialize original).length, alignment := 4 } =
      .success valuesPtr valuesFinish) :
    ScratchLineage original capacity dataPtr valuesPtr inputHistory.nextId
      valuesFinish.toNat (inputHistory.allocate valuesPtr
        { size := (serialize original).length, alignment := 4 }) :=
  ⟨inputFrontier, inputHistory, valuesFinish, hbounded, hclassify, rfl, rfl, rfl⟩

/-- The retained lineage pins the actual live values record, not an unrelated
existential allocation history. -/
theorem ScratchLineage.values_metadata
    {original : List UInt32} {capacity dataPtr valuesPtr : UInt32}
    {valuesId frontier : Nat} {history : AllocationHistory}
    (h : ScratchLineage original capacity dataPtr valuesPtr valuesId frontier history) :
    get? history.records valuesId = some
      (liveMeta valuesPtr { size := (serialize original).length, alignment := 4 }) := by
  obtain ⟨inputFrontier, inputHistory, finish, _, _, hid, _, hhistory⟩ := h
  subst history
  subst valuesId
  exact get?_insert_eq rfl

/-- The actual values-allocation frontier stays within the two-array bound,
including when the subsequent scratch allocation fails. No fit or success
premise is imposed on that subsequent allocation. -/
theorem ScratchLineage.frontier_le
    {original : List UInt32} {capacity dataPtr valuesPtr : UInt32}
    {valuesId frontier : Nat} {history : AllocationHistory}
    (h : ScratchLineage original capacity dataPtr valuesPtr valuesId frontier history) :
    frontier ≤ workArraysFrontierBound (serialize original).length := by
  obtain ⟨inputFrontier, inputHistory, finish, hbounded, hvalues,
    _hid, hfrontier, _hhistory⟩ := h
  have hinput := BoundedGeometricVecFacts.frontier_le _ _ _ _ _ _ _ hbounded
  have hvaluesBound := classifyBump_success_finish_le _ _ _ _ hvalues
  simp only at hvaluesBound
  unfold workArraysFrontierBound
  omega

/-- Two actual successful classifications bound the final allocation frontier.
The conclusion remains valid without assuming the closed arithmetic budget. -/
theorem ScratchLineage.scratch_finish_le
    {original : List UInt32} {capacity dataPtr valuesPtr scratchPtr finish : UInt32}
    {valuesId frontier : Nat} {history : AllocationHistory}
    (h : ScratchLineage original capacity dataPtr valuesPtr valuesId frontier history)
    (hscratch : classifyBump frontier
      { size := (serialize original).length, alignment := 4 } =
        .success scratchPtr finish) :
    finish.toNat ≤ workArraysFrontierBound (serialize original).length := by
  obtain ⟨inputFrontier, inputHistory, valuesFinish, hbounded, hvalues,
    _hid, hfrontier, _hhistory⟩ := h
  have hinput := BoundedGeometricVecFacts.frontier_le _ _ _ _ _ _ _ hbounded
  have hvaluesBound := classifyBump_success_finish_le _ _ _ _ hvalues
  have hscratchBound := classifyBump_success_finish_le _ _ _ _ hscratch
  simp only at hvaluesBound hscratchBound
  unfold workArraysFrontierBound
  omega

/-- The candidate values allocation from the two-array bound is forced to
equal the actual first allocation.  Thus the same bound applies at the exact
scratch call frontier retained by the driver, with no assumed scratch success. -/
theorem ScratchLineage.scratch_classify_success
    {original : List UInt32} {capacity dataPtr valuesPtr : UInt32}
    {valuesId frontier : Nat} {history : AllocationHistory}
    (h : ScratchLineage original capacity dataPtr valuesPtr valuesId frontier history)
    (hfit : WorkArraysFit (serialize original).length) :
    ∃ scratchPtr scratchFinish : UInt32,
      classifyBump frontier
          { size := (serialize original).length, alignment := 4 } =
        .success scratchPtr scratchFinish ∧
      scratchFinish.toNat ≤ workArraysFrontierBound (serialize original).length := by
  obtain ⟨inputFrontier, inputHistory, valuesFinish, hbounded, hvalues,
    _hid, hfrontier, _hhistory⟩ := h
  obtain ⟨candidatePtr, candidateFinish, scratchPtr, scratchFinish,
    hcandidate, hscratch, hbound⟩ :=
    BoundedGeometricVecFacts.workArrays_classify_success
      (serialize original).length capacity dataPtr inputFrontier inputHistory hbounded hfit
  have heq := BumpDecision.success.inj (hvalues.symm.trans hcandidate)
  rw [← heq.2] at hscratch
  exact ⟨scratchPtr, scratchFinish, hfrontier ▸ hscratch, hbound⟩

end Project.Mergesort.BoundedDriverFacts
