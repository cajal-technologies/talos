import Project.Mergesort.Representations
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Memory-bound interfaces for the compiled merge-sort allocator

The resource bounds concern the driver's allocation lineage. The small-step
lemma verifies the actual compiled growth suffix under explicit current-page
and physical-cap premises. The general allocator contracts retain the physical
OOM alternative; exact-page clients supply the stronger growth premises.
`GrowingTotalProof.export_returns_normally` discharges them for the complete
canonical export under its input-size bound.
-/

namespace Project.Mergesort.MemoryBounds

open Wasm Wasm.SmallStep Wasm.SepLogic Iris
open Project.Mergesort.Representations

/-- The compiled `func5` instructions following the branch that decides growth
is needed.  They compute the delta and distinguish success from `-1`. -/
def allocatorGrowSuffix : Program :=
  [.localGet 3, .localGet 0, .sub, .memoryGrow,
    .const 0xFFFFFFFF, .ne, .br_if 1]

/-- This suffix is part of the frozen compiled function, not a replacement
allocator. -/
theorem allocatorGrowSuffix_in_func5 :
    ∃ earlier : Program,
      func5Def.body =
        [.block 0 0
          [.block 0 0 (earlier ++ allocatorGrowSuffix),
            .call 9, .unreachable],
          .const 0, .localGet 1, .store32 allocatorCursor, .localGet 2] := by
  refine ⟨[.localGet 1, .const 0xFFFFFFFF, .add, .localTee 2,
    .const 0, .load32 allocatorCursor, .localTee 3,
    .const heapBase, .localGet 3, .select, .add, .localTee 3,
    .localGet 2, .ltU, .br_if 0,
    .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 2,
    .localGet 0, .add, .localTee 1,
    .localGet 2, .ltU, .br_if 0,
    .localGet 1, .const 0, .ltS, .br_if 0,
    .localGet 1, .const 65535, .add, .const 16, .shrU,
    .localTee 3, .memorySize, .localTee 0, .leU, .br_if 1], rfl⟩

/-- Actual execution of the growth suffix reaches its success branch with
exactly the requested number of pages.  The caller's stack and control frames
are arbitrary, and the physical memory bytes are preserved by growth.

The explicit store cap and exact current page count determine the physical
growth outcome; a persistent lower-bound snapshot alone cannot do so. -/
theorem allocatorGrowSuffix_steps
    {α : Type} (store : MachineStore α) (finish base : UInt32)
    (values remainder : List Value) (arity : Nat)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 =
      Module.memoryHardCap)
    (hfinish : finish.toNat < 2147483648)
    (hneed : store.wasm.mem.pages < (allocatorRequiredPages finish).toNat) :
    Steps
      ⟨.running
        ⟨⟨[.i32 store.wasm.mem.pages.toUInt32, .i32 finish],
          [.i32 base, .i32 (allocatorRequiredPages finish)], values⟩,
          allocatorGrowSuffix, arity, remainder, controls, calls⟩, store⟩
      [.instruction (.localGet 3), .instruction (.localGet 0),
        .instruction .sub, .instruction .memoryGrow,
        .instruction (.const 0xFFFFFFFF), .instruction .ne]
      ⟨.running
        ⟨⟨[.i32 store.wasm.mem.pages.toUInt32, .i32 finish],
          [.i32 base, .i32 (allocatorRequiredPages finish)], .i32 1 :: values⟩,
          [.br_if 1], arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem :=
          { store.wasm.mem with pages :=
            (allocatorRequiredPages finish).toNat } } }⟩ := by
  have hg := allocatorMemoryGrow_succeeds store.wasm.mem finish hfinish hneed
  rw [← hcap] at hg
  have hpages : store.wasm.mem.pages < UInt32.size := by
    have ht := allocatorRequiredPages_le_signedLimit finish hfinish
    norm_num [UInt32.size] at *
    omega
  have hnotFailure : store.wasm.mem.pages.toUInt32 ≠ (0xFFFFFFFF : UInt32) := by
    intro heq
    have heqNat := congrArg UInt32.toNat heq
    have hpagesNat : store.wasm.mem.pages.toUInt32.toNat = store.wasm.mem.pages :=
      UInt32.toNat_ofNat_of_lt' hpages
    have ht := allocatorRequiredPages_le_signedLimit finish hfinish
    change store.wasm.mem.pages.toUInt32.toNat = 4294967295 at heqNat
    rw [hpagesNat] at heqNat
    omega
  unfold allocatorGrowSuffix
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons Step.sub
  apply Steps.cons (by
    simpa only [setMemory_eq] using Step.memoryGrowSuccess hg)
  apply Steps.cons Step.const
  apply Steps.cons (Step.ne (result := 1) (by simp [hnotFailure]))
  exact Steps.refl _

/-- The successful branch exits the two nested allocator blocks and reaches
the actual cursor-commit instructions, bypassing the OOM wrapper at `call 9`. -/
theorem allocatorGrowSuffix_to_commit_steps
    {α : Type} (store : MachineStore α) (finish base : UInt32)
    (remainder : List Value) (arity : Nat)
    (inner : ControlFrame) (outerBody : Program)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 =
      Module.memoryHardCap)
    (hfinish : finish.toNat < 2147483648)
    (hneed : store.wasm.mem.pages < (allocatorRequiredPages finish).toNat) :
    Steps
      ⟨.running
        ⟨⟨[.i32 store.wasm.mem.pages.toUInt32, .i32 finish],
          [.i32 base, .i32 (allocatorRequiredPages finish)], []⟩,
          allocatorGrowSuffix, arity, remainder,
          inner ::
            { kind := .block
              paramArity := 0
              resultArity := 0
              body := outerBody
              continuation :=
                [.const 0, .localGet 1, .store32 allocatorCursor, .localGet 2]
              belowStack := [] } :: controls, calls⟩, store⟩
      (allocatorGrowSuffix.map StepKind.instruction)
      ⟨.running
        ⟨⟨[.i32 store.wasm.mem.pages.toUInt32, .i32 finish],
          [.i32 base, .i32 (allocatorRequiredPages finish)], []⟩,
          [.const 0, .localGet 1, .store32 allocatorCursor, .localGet 2],
          arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem :=
          { store.wasm.mem with pages :=
            (allocatorRequiredPages finish).toNat } } }⟩ := by
  exact (allocatorGrowSuffix_steps store finish base [] remainder arity
    (inner ::
      { kind := .block
        paramArity := 0
        resultArity := 0
        body := outerBody
        continuation :=
          [.const 0, .localGet 1, .store32 allocatorCursor, .localGet 2]
        belowStack := [] } :: controls) calls hcap hfinish hneed).trans
    (Steps.single (Step.brIf (by decide) (by rfl)))

/-- The state interpretation ties an owned physical-cap slot to the actual
runtime table. -/
theorem stateInterp_owned_memoryCap
    {α : Type} [WasmSmallStepGS hlc α]
    (store : MachineStore α) (cap : Nat)
    (steps : Nat) (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      memoryCapOwn 0 cap ⊢ ⌜store.wasm.memoryCaps[0]? = some cap⌝ := by
  exact stateInterp_memoryCap_lookup store steps observations threads 0 cap

/-- The pure `GeometricVecFacts` lineage alone admits a 512-byte live capacity
for a four-byte completed input. This refutes an inference from that invariant;
it does not claim that the canonical driver reaches this state. -/
theorem geometricFacts_allow_excess_capacity :
    GeometricVecFacts 4 4 0 512
        (UInt32.ofNat (vectorBlockBase 9)) (vectorBlockBase 9 + 512)
        (geometricHistory 9) ∧
      ¬ (512 : UInt32).toNat ≤ max (2 * 4) 8 := by
  constructor
  · right; right
    exact ⟨9, by decide, by decide, rfl, by decide, rfl,
      rfl, rfl, rfl⟩
  · decide

theorem BoundedGeometricVecFacts.initial (total : Nat) :
    BoundedGeometricVecFacts total 0 total 0 1 heapBase.toNat
      AllocationHistory.empty := by
  exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp⟩

theorem BoundedGeometricVecFacts.appendWithoutReserve
    (total length current remaining : Nat)
    (capacity ptr : UInt32) (frontier : Nat) (history : AllocationHistory)
    (h : BoundedGeometricVecFacts total length (current + remaining)
      capacity ptr frontier history)
    (hcurrent : 0 < current)
    (hfits : current ≤ capacity.toNat - length) :
    BoundedGeometricVecFacts total (length + current) remaining
      capacity ptr frontier history :=
  ⟨h.1.appendWithoutReserve _ _ _ _ _ _ _ _ hcurrent hfits, h.2⟩

/-- A reserve is reached only when the chunk exceeds the spare capacity.
This branch condition bounds the selected capacity by the total input size. -/
theorem selectedCapacity_le_input_bound
    (total length current remaining capacity : Nat)
    (htotal : total = length + current + remaining)
    (hreserve : capacity < length + current) :
    selectedCapacity length current capacity ≤ max (2 * total) 8 := by
  unfold selectedCapacity
  omega

theorem BoundedGeometricVecFacts.reserveSuccess
    (total length current remaining : Nat)
    (capacity ptr newPtr finish : UInt32)
    (frontier : Nat) (history finalHistory : AllocationHistory)
    (h : BoundedGeometricVecFacts total length (current + remaining)
      capacity ptr frontier history)
    (hread : current = min 256 (current + remaining))
    (hcurrent : 0 < current)
    (hreserve : capacity.toNat < length + current)
    (hclassify : classifyBump frontier
        { size := selectedCapacity length current capacity.toNat,
          alignment := 1 } = .success newPtr finish)
    (hhistory : VecReserveHistory history finalHistory capacity ptr newPtr
        { size := selectedCapacity length current capacity.toNat,
          alignment := 1 }) :
    BoundedGeometricVecFacts total (length + current) remaining
      (UInt32.ofNat (selectedCapacity length current capacity.toNat))
      newPtr finish.toNat finalHistory := by
  refine ⟨GeometricVecFacts.reserveSuccess total length current remaining
    capacity ptr newPtr finish frontier history finalHistory h.1 hread hcurrent
    hclassify hhistory, ?_⟩
  have htotal : total = length + current + remaining := by
    rcases h.1 with hempty | hshort | hlarge
    · omega
    · omega
    · obtain ⟨_, _, _, _, _, htotal, _⟩ := hlarge
      omega
  have hbound := selectedCapacity_le_input_bound total length current remaining
    capacity.toNat htotal hreserve
  have hmod : (UInt32.ofNat
      (selectedCapacity length current capacity.toNat)).toNat ≤
      selectedCapacity length current capacity.toNat := by
    change (selectedCapacity length current capacity.toNat) % UInt32.size ≤ _
    exact Nat.mod_le _ _
  exact hmod.trans hbound

/-- The allocation frontier includes both the live input buffer and every
retired buffer.  This bound uses the existing exact allocation lineage. -/
theorem GeometricVecFacts.frontier_le_twice_capacity
    (total length remaining : Nat) (capacity ptr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (h : GeometricVecFacts total length remaining capacity ptr frontier history) :
    frontier ≤ heapBase.toNat + 2 * capacity.toNat := by
  rcases h with hempty | hshort | hlarge
  · omega
  · omega
  · obtain ⟨e, _, _, hcap, _, _, _, hfrontier, _⟩ := hlarge
    rw [hfrontier, vectorBlockBase, hcap]
    omega

theorem BoundedGeometricVecFacts.frontier_le
    (total length remaining : Nat) (capacity ptr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (h : BoundedGeometricVecFacts total length remaining capacity ptr frontier history) :
    frontier ≤ inputFrontierBound total := by
  have hfrontier := GeometricVecFacts.frontier_le_twice_capacity
    total length remaining capacity ptr frontier history h.1
  have hcap := h.2
  unfold inputFrontierBound
  omega

/-- A closed arithmetic allocator-budget predicate for the bounded allocation
lineage. Physical growth success additionally requires the exact page count
and cap; `GrowingTotalProof.export_returns_normally` supplies the complete
normal-return guarantee. -/
def WorkArraysFit (total : Nat) : Prop :=
  workArraysFrontierBound total < 2147483648

/-- Alignment-one requests introduce no padding. -/
theorem classifyBump_align1_success
    (frontier size : Nat) (hbound : frontier + size < 2147483648) :
    classifyBump frontier { size := size, alignment := 1 } =
      .success (UInt32.ofNat frontier) (UInt32.ofNat (frontier + size)) := by
  have hfrontier : frontier < UInt32.size := by
    norm_num [UInt32.size]
    omega
  have hend : frontier + size < UInt32.size := by
    norm_num [UInt32.size]
    omega
  simp [classifyBump, hfrontier, UInt32.toNat_ofNat_of_lt' hfrontier,
    hend, hbound]

/-- Under the same budget, every reserve request selected by the driver's
actual spare-capacity branch passes the allocator's arithmetic checks. -/
theorem BoundedGeometricVecFacts.reserve_classify_success
    (total length current remaining : Nat)
    (capacity ptr : UInt32) (frontier : Nat) (history : AllocationHistory)
    (h : BoundedGeometricVecFacts total length (current + remaining)
      capacity ptr frontier history)
    (hcurrent : 0 < current)
    (hreserve : capacity.toNat < length + current)
    (hfit : WorkArraysFit total) :
    classifyBump frontier
        { size := selectedCapacity length current capacity.toNat,
          alignment := 1 } =
      .success (UInt32.ofNat frontier)
        (UInt32.ofNat (frontier +
          selectedCapacity length current capacity.toNat)) := by
  have htotal : total = length + current + remaining := by
    rcases h.1 with hempty | hshort | hlarge
    · omega
    · omega
    · obtain ⟨_, _, _, _, _, htotal, _⟩ := hlarge
      omega
  have hselected := selectedCapacity_le_input_bound total length current
    remaining capacity.toNat htotal hreserve
  have hfrontier := BoundedGeometricVecFacts.frontier_le
    total length (current + remaining) capacity ptr frontier history h
  apply classifyBump_align1_success
  unfold WorkArraysFit workArraysFrontierBound at hfit
  omega

/-- A successful classifier bounds its end by the requested size and at most
alignment-minus-one padding. No separate arithmetic fit premise is required. -/
theorem classifyBump_success_finish_le
    (frontier : Nat) (layout : AllocLayout) (base finish : UInt32)
    (hclassify : classifyBump frontier layout = .success base finish) :
    finish.toNat ≤ frontier + (layout.alignment - 1) + layout.size := by
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  have hbase : base.toNat ≤ frontier + (layout.alignment - 1) := by
    rw [hfacts.2.1]
    have h := UInt32.le_iff_toNat_le_toNat.mp
      (UInt32.and_le_left (a := UInt32.ofNat (frontier + (layout.alignment - 1)))
        (b := 0 - UInt32.ofNat layout.alignment))
    rwa [UInt32.toNat_ofNat_of_lt' hfacts.1] at h
  rw [hfacts.2.2.2.2]
  omega

/-- Sufficient room for a four-aligned request forces the allocator's exact
classification to take its success branch.  The bound includes alignment
padding, so no undocumented alignment premise is required. -/
theorem classifyBump_align4_success
    (frontier size : Nat) (hbound : frontier + 3 + size < 2147483648) :
    ∃ base finish : UInt32,
      classifyBump frontier { size := size, alignment := 4 } =
        .success base finish ∧
      finish.toNat ≤ frontier + 3 + size := by
  have hsum : frontier + 3 < UInt32.size := by
    norm_num [UInt32.size]
    omega
  let base := UInt32.ofNat (frontier + 3) &&& (0 - (4 : UInt32))
  have hbase : base.toNat ≤ frontier + 3 := by
    have h := UInt32.le_iff_toNat_le_toNat.mp
      (UInt32.and_le_left (a := UInt32.ofNat (frontier + 3))
        (b := 0 - (4 : UInt32)))
    simpa only [UInt32.toNat_ofNat_of_lt' hsum] using h
  have hend : base.toNat + size < UInt32.size ∧
      base.toNat + size < 2147483648 := by
    norm_num [UInt32.size]
    omega
  refine ⟨base, UInt32.ofNat (base.toNat + size), ?_, ?_⟩
  · simp only [classifyBump, show (4 : Nat) - 1 = 3 by decide,
      dif_pos hsum]
    change (if base.toNat + size < UInt32.size ∧
        base.toNat + size < 2147483648 then
      BumpDecision.success base (UInt32.ofNat (base.toNat + size))
      else BumpDecision.oom) = _
    rw [if_pos hend]
  · rw [UInt32.toNat_ofNat_of_lt' hend.1]
    omega

/-- The existing exact Vec history plus the strengthened input bound leaves
enough arithmetic room for both actual driver work-array layouts.  This
rules out the signed-end OOM branches, but not physical growth failure. -/
theorem BoundedGeometricVecFacts.workArrays_classify_success
    (total : Nat) (capacity ptr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (h : BoundedGeometricVecFacts total total 0 capacity ptr frontier history)
    (hfit : WorkArraysFit total) :
    ∃ valuesPtr valuesFinish scratchPtr scratchFinish : UInt32,
      classifyBump frontier { size := total, alignment := 4 } =
        .success valuesPtr valuesFinish ∧
      classifyBump valuesFinish.toNat { size := total, alignment := 4 } =
        .success scratchPtr scratchFinish ∧
      scratchFinish.toNat ≤ workArraysFrontierBound total := by
  have hfrontier := BoundedGeometricVecFacts.frontier_le
    total total 0 capacity ptr frontier history h
  unfold WorkArraysFit workArraysFrontierBound at hfit
  obtain ⟨valuesPtr, valuesFinish, hvalues, hvaluesEnd⟩ :=
    classifyBump_align4_success frontier total (by omega)
  obtain ⟨scratchPtr, scratchFinish, hscratch, hscratchEnd⟩ :=
    classifyBump_align4_success valuesFinish.toNat total (by omega)
  refine ⟨valuesPtr, valuesFinish, scratchPtr, scratchFinish,
    hvalues, hscratch, ?_⟩
  unfold workArraysFrontierBound
  omega

/-- An explicit, useful arithmetic range for canonical word inputs.  It
includes allocations that cross linear-memory page boundaries.  The theorem
certifies `WorkArraysFit`, not successful export execution. -/
theorem workArraysFit_word_range (n : Nat) (hn : n ≤ 89434754) :
    WorkArraysFit (4 * n) := by
  unfold WorkArraysFit workArraysFrontierBound inputFrontierBound heapBase
  change 1049536 + 2 * max (2 * (4 * n)) 8 + 2 * (4 * n) + 6 < 2147483648
  omega

/-- The stated conservative word range ends at the last admitted integer. -/
theorem workArraysFit_word_range_boundary :
    WorkArraysFit (4 * 89434754) ∧ ¬ WorkArraysFit (4 * 89434755) := by
  unfold WorkArraysFit workArraysFrontierBound inputFrontierBound heapBase
  decide

/-- Equality at the allocator's signed-end limit is rejected by the exact
compiled arithmetic classifier. -/
theorem classifyBump_signed_boundary :
    classifyBump 2147483644 { size := 3, alignment := 4 } =
        .success 2147483644 2147483647 ∧
      classifyBump 2147483644 { size := 4, alignment := 4 } = .oom := by
  decide

end Project.Mergesort.MemoryBounds
