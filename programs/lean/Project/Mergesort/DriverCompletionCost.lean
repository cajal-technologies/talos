import Project.Mergesort.DriverControlCost
import Project.Mergesort.DecodeCost
import Project.Mergesort.ZeroedAllocatorExecution

/-! # Numerical work of the complete nonempty post-read driver

The actual values allocation, decoding, scratch allocation, sorting, output
and cleanup execute consecutively. Growth is charged by the added physical
bytes. Initial allocator and physical-range facts discharge the calls.
-/

namespace Project.Mergesort.DriverCompletionCost

open Wasm Wasm.SmallStep Project.Mergesort.DriverProof
open Project.Mergesort.Representations Project.Mergesort.MemoryBounds

def afterValues : Program := [.localTee 2,.eqz,.br_if 1] ++ func3DecodeSetup ++
  [.block 0 0 func3DecodeOuterBlockBody,.call 7,.localGet 9,.const 2,.shl,
    .localTee 10,.const 4,.call 12] ++ func3ScratchSuccessTail

def beforeScratch : Program := [.call 7,.localGet 9,.const 2,.shl,
  .localTee 10,.const 4,.call 12] ++ func3ScratchSuccessTail

/-- The real marker, argument setup and values-allocation call. -/
theorem values_cost (store : MachineStore α) (source : UInt32) (n frontier : Nat)
    (storedCursor base finish : UInt32) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hclassify : classifyBump frontier { size := 4*n,alignment := 4 } = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor=storedCursor)
    (heffective : (if storedCursor≠0 then storedCursor else heapBase)=UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat+4≤store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace amount, CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3AppendLocals source 0 (UInt32.ofNat (4*n)) 4 source 0
        (UInt32.ofNat (4*n)) 0 0 0 [],func3AllocationBody,0,[],func3ScratchSuccessControls,calls⟩,
        store⟩ trace
      ⟨.running ⟨func3AppendLocals source 0 (UInt32.ofNat (4*n)) 4 source 0
        (UInt32.ofNat (4*n)) 0 0 0 [.i32 base],afterValues,0,[],func3ScratchSuccessControls,calls⟩,
        AllocatorExecution.finalStore store finish⟩ amount ∧
      amount ≤ 60+65536*((allocatorRequiredPages finish).toNat-store.wasm.mem.pages) := by
  let locals := func3AppendLocals source 0 (UInt32.ofNat (4*n)) 4 source 0
    (UInt32.ofNat (4*n)) 0 0 0 []
  let caller : ThreadState α := ⟨locals,[.localGet 7,.const 4,.call 8]++afterValues,
    0,[],func3ScratchSuccessControls,calls⟩
  have marker := DriverControlCost.marker_call_cost store caller hmodule hostBytes
  have setup : CostedSteps (byteWork hostBytes)
      ⟨.running caller,store⟩ [.instruction (.localGet 7),.instruction (.const 4)]
      ⟨.running ⟨{ locals with values := [.i32 4,.i32 (UInt32.ofNat (4*n))] },
        .call 8 :: afterValues,0,[],func3ScratchSuccessControls,calls⟩,store⟩ 2 := by
    apply Steps.with_unit_cost
    · apply Steps.cons (.localGet rfl)
      exact Steps.single Step.const
    · intro before kind after member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl <;> rfl
  obtain ⟨trace,bound,run⟩ := AllocatorExecution.func5_call_byteWork store
    { size := 4*n,alignment := 4 } frontier storedCursor base finish locals [] afterValues
    0 [] func3ScratchSuccessControls calls hmodule hcap hpages (Or.inr rfl)
    hclassify hcursor heffective hcursorBounds hostBytes
  refine ⟨_,_,(marker.trans setup).trans run,?_⟩
  omega

/-- The real second marker, byte-count setup and zeroed scratch call. -/
theorem scratch_cost (store : MachineStore α) (source values : UInt32) (n frontier : Nat)
    (f1 f3 f6 f5 f8 aux10 storedCursor base finish : UInt32) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hfrontier : heapBase.toNat≤frontier)
    (hvalid : (AllocLayout.mk (4*n) 4).Valid)
    (hclassify : classifyBump frontier { size := 4*n,alignment := 4 } = .success base finish)
    (hcursor : store.wasm.mem.read32 allocatorCursor=storedCursor)
    (heffective : (if storedCursor≠0 then storedCursor else heapBase)=UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat+4≤store.wasm.mem.pages*65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace amount, CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3AppendLocals f1 f3 f6 values source f5 (UInt32.ofNat (4*n)) f8
        (UInt32.ofNat n) aux10 [],beforeScratch,0,[],func3ScratchSuccessControls,calls⟩,store⟩ trace
      ⟨.running ⟨func3AppendLocals f1 f3 f6 values source f5 (UInt32.ofNat (4*n)) f8
        (UInt32.ofNat n) (UInt32.ofNat (4*n)) [.i32 base],func3ScratchSuccessTail,
        0,[],func3ScratchSuccessControls,calls⟩,
        ZeroedAllocatorExecution.finalStore store (UInt32.ofNat (4*n)) base finish⟩ amount ∧
      amount ≤ 76+4*n+65536*((allocatorRequiredPages finish).toNat-store.wasm.mem.pages) := by
  let locals := func3AppendLocals f1 f3 f6 values source f5 (UInt32.ofNat (4*n)) f8
    (UInt32.ofNat n) aux10 []
  let ready := func3AppendLocals f1 f3 f6 values source f5 (UInt32.ofNat (4*n)) f8
    (UInt32.ofNat n) (UInt32.ofNat (4*n)) []
  let caller : ThreadState α := ⟨locals,[.localGet 9,.const 2,.shl,.localTee 10,.const 4,.call 12]++
    func3ScratchSuccessTail,0,[],func3ScratchSuccessControls,calls⟩
  have marker := DriverControlCost.marker_call_cost store caller hmodule hostBytes
  have setup : CostedSteps (byteWork hostBytes)
      ⟨.running caller,store⟩ [.instruction (.localGet 9),.instruction (.const 2),
        .instruction .shl,.instruction (.localTee 10),.instruction (.const 4)]
      ⟨.running ⟨{ ready with values := [.i32 4,.i32 (UInt32.ofNat (4*n))] },
        .call 12 :: func3ScratchSuccessTail,0,[],func3ScratchSuccessControls,calls⟩,store⟩ 5 := by
    apply Steps.with_unit_cost
    · wasm_steps [(.localGet rfl),.const,.shl]
      rw [MemRegion.shl2_eq_mul4]
      have hmul : 4*UInt32.ofNat n=UInt32.ofNat (4*n) := by rw [UInt32.ofNat_mul]; rfl
      rw [hmul]
      apply Steps.cons (.localTee rfl)
      exact Steps.single Step.const
    · intro before kind after member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl <;> rfl
  obtain ⟨trace,bound,run,_⟩ := ZeroedAllocatorExecution.func9_call_byteWork store
    { size := 4*n,alignment := 4 } frontier storedCursor base finish ready [] func3ScratchSuccessTail
    0 [] func3ScratchSuccessControls calls hmodule hcap hpages hfrontier hvalid rfl
    hclassify hcursor heffective hcursorBounds hostBytes
  refine ⟨_,_,(marker.trans setup).trans run,?_⟩
  change 2+5+(trace.length+4*n+_)≤_
  omega

/-- A numerical certificate for the entire nonempty post-read path. Both
allocation decisions follow from the bounded input lineage and size bound;
there is no supplied future execution or successful-call premise. -/
theorem complete_cost (store : MachineStore Universal.State) (n : Nat)
    (source capacity storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (calls : List CallFrame) (hpositive : 0<n)
    (hgeo : BoundedGeometricVecFacts (4*n) (4*n) 0 capacity source frontier history)
    (hfit : WorkArraysFit (4*n))
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hpages : store.wasm.mem.pages≤Module.memoryHardCap)
    (hsourceWrap : source.toNat+4*n<UInt32.size)
    (hsource : source.toNat+4*n≤store.wasm.mem.pages*65536)
    (hcursor : store.wasm.mem.read32 allocatorCursor=storedCursor)
    (heffective : (if storedCursor≠0 then storedCursor else heapBase)=UInt32.ofNat frontier)
    (hcursorBounds : allocatorCursor.toNat+4≤store.wasm.mem.pages*65536)
    (hframe : 1048576≤store.wasm.mem.pages*65536)
    (hglobal : (globalAt? store 0).isSome=true) :
    ∃ trace finalStore finalLocals amount,
      CostedSteps CostedStdIO.work
        ⟨.running ⟨func3AppendLocals source 0 (UInt32.ofNat (4*n)) 4 source 0
          (UInt32.ofNat (4*n)) 0 0 0 [],func3AllocationBody,0,[],func3ScratchSuccessControls,calls⟩,
          store⟩ trace
        ⟨.running ⟨finalLocals,[],0,[],[],calls⟩,finalStore⟩ amount ∧
      store.wasm.mem.pages≤finalStore.wasm.mem.pages ∧
      finalStore.wasm.mem.pages≤max store.wasm.mem.pages
        ((workArraysFrontierBound (4*n)+65535)/65536) ∧
      amount≤SortWorkBudget.budget n+47*n+257+
        65536*(finalStore.wasm.mem.pages-store.wasm.mem.pages) := by
  have hfrontier := geometricVec_frontier_ge_heapBase _ _ _ _ _ _ _ hgeo
  have hsize : 4*n<2147483648 := by
    unfold WorkArraysFit workArraysFrontierBound at hfit
    omega
  have hvalid := align4Layout_valid_of_bounds (4*n) (by omega) hsize (by omega)
  obtain ⟨values,valuesFinish,scratch,scratchFinish,hv,hs,hend⟩ :=
    BoundedGeometricVecFacts.workArrays_classify_success _ _ _ _ _ hgeo hfit
  obtain ⟨hvFresh,hvNonnull,_hvAlign,hvWrap,hvSigned,hvEnd,_⟩ :=
    classifyBump_success_reachable frontier { size := 4*n,alignment := 4 }
      values valuesFinish hfrontier hvalid (Or.inr rfl) hv
  have hvFinishSigned : valuesFinish.toNat<2147483648 := by omega
  have hvFrontier : heapBase.toNat≤valuesFinish.toNat := by omega
  obtain ⟨hsFresh,hsNonnull,_hsAlign,hsWrap,hsSigned,hsEnd,_⟩ :=
    classifyBump_success_reachable valuesFinish.toNat { size := 4*n,alignment := 4 }
      scratch scratchFinish hvFrontier hvalid (Or.inr rfl) hs
  have hsFinishSigned : scratchFinish.toNat<2147483648 := by omega
  obtain ⟨valuesTrace,valuesAmount,valuesRun,valuesBound⟩ := values_cost store source n
    frontier storedCursor values valuesFinish calls hmodule hcap hpages hv hcursor
    heffective hcursorBounds CostedStdIO.hostBytes
  let allocated := AllocatorExecution.finalStore store valuesFinish
  have allocatedPages : allocated.wasm.mem.pages=max store.wasm.mem.pages
      (allocatorRequiredPages valuesFinish).toNat := rfl
  have pagesGrow : store.wasm.mem.pages≤allocated.wasm.mem.pages := Nat.le_max_left _ _
  have hvBounds : values.toNat+4*n≤allocated.wasm.mem.pages*65536 := by
    rw [← hvEnd]
    exact AllocatorExecution.finalStore_covers_finish store valuesFinish hvFinishSigned
  let ctx : DecodeLoopCost.Context :=
    { code := beforeScratch,controls := func3ScratchSuccessControls,calls := calls }
  obtain ⟨decodeTrace,memory,f1,f3,f6,f5,f8,decodeAmount,decodeRun,decodePages,decodeBound,decodePrefix⟩ :=
    DecodeCost.decode_allocated_cost allocated source values n 0 4 0 0 0 ctx
      hpositive hvNonnull hsourceWrap hvWrap
      (hsource.trans (Nat.mul_le_mul_right 65536 pagesGrow)) hvBounds CostedStdIO.hostBytes
  let decoded := { allocated with wasm := { allocated.wasm with mem := memory } }
  have decodedPages : decoded.wasm.mem.pages=allocated.wasm.mem.pages := decodePages
  have decodedCursor : decoded.wasm.mem.read32 allocatorCursor=valuesFinish := by
    change memory.read32 allocatorCursor=valuesFinish
    rw [decodePrefix allocatorCursor (by
      have : allocatorCursor.toNat+4≤heapBase.toNat := by decide
      omega)]
    exact AllocatorExecution.finalStore_cursor _ _
  have hvFinishNonnull : valuesFinish≠0 := by
    intro hz
    have : valuesFinish.toNat=0 := by rw [hz]; rfl
    have : 0<heapBase.toNat := by decide
    omega
  have decodedCap : decoded.wasm.memoryCap decoded.runtime.currentModule 0=Module.memoryHardCap := hcap
  obtain ⟨scratchTrace,scratchAmount,scratchRun,scratchBound⟩ := scratch_cost decoded source values n
    valuesFinish.toNat f1 f3 f6 f5 f8 0 valuesFinish scratch scratchFinish calls hmodule
    decodedCap (by rw [decodedPages]; exact AllocatorExecution.finalStore_pages_le_cap _ _ hpages hvFinishSigned)
    hvFrontier hvalid hs decodedCursor (by simp [hvFinishNonnull])
    (by rw [decodedPages]; exact hcursorBounds.trans (Nat.mul_le_mul_right 65536 pagesGrow))
    CostedStdIO.hostBytes
  let zeroed := ZeroedAllocatorExecution.finalStore decoded (UInt32.ofNat (4*n)) scratch scratchFinish
  have zeroedPages : zeroed.wasm.mem.pages=max decoded.wasm.mem.pages
      (allocatorRequiredPages scratchFinish).toNat := rfl
  have scratchPagesGrow : decoded.wasm.mem.pages≤zeroed.wasm.mem.pages := Nat.le_max_left _ _
  have fullPagesGrow : store.wasm.mem.pages≤zeroed.wasm.mem.pages := by
    rw [decodedPages] at scratchPagesGrow
    omega
  have hsBounds : scratch.toNat+4*n≤zeroed.wasm.mem.pages*65536 := by
    rw [← hsEnd,zeroedPages]
    exact (allocatorRequiredPages_covers scratchFinish hsFinishSigned).trans
      (Nat.mul_le_mul_right 65536 (Nat.le_max_right _ _))
  obtain ⟨tailTrace,finalStore,finalLocals,tailAmount,tailRun,tailPages,tailBound⟩ :=
    DriverControlCost.after_scratch_cost zeroed n f1 f3 f6 values source f5 f8 scratch calls
      hpositive hsNonnull hmodule hhost hvWrap hsWrap
      (hvBounds.trans (Nat.mul_le_mul_right 65536 (by rw [← decodedPages]; exact scratchPagesGrow)))
      hsBounds (hframe.trans (Nat.mul_le_mul_right 65536 fullPagesGrow)) hglobal
  have hvFinishLe : valuesFinish.toNat≤scratchFinish.toNat := by omega
  have hvReq := allocatorRequiredPages_toNat valuesFinish hvFinishSigned
  have hsReq := allocatorRequiredPages_toNat scratchFinish hsFinishSigned
  have hvLimit : (allocatorRequiredPages valuesFinish).toNat≤
      (workArraysFrontierBound (4*n)+65535)/65536 := by
    rw [hvReq]
    exact Nat.div_le_div_right (by omega)
  have hsLimit : (allocatorRequiredPages scratchFinish).toNat≤
      (workArraysFrontierBound (4*n)+65535)/65536 := by
    rw [hsReq]
    exact Nat.div_le_div_right (by omega)
  have joined := ((valuesRun.trans decodeRun).trans scratchRun).trans tailRun
  refine ⟨_,finalStore,finalLocals,_,joined,by omega,?_,?_⟩
  · rw [tailPages,zeroedPages,decodedPages,allocatedPages]
    exact max_le (max_le (Nat.le_max_left _ _) (hvLimit.trans (Nat.le_max_right _ _)))
      (hsLimit.trans (Nat.le_max_right _ _))
  · have telescope :
        (allocatorRequiredPages valuesFinish).toNat-store.wasm.mem.pages+
          ((allocatorRequiredPages scratchFinish).toNat-decoded.wasm.mem.pages)=
        finalStore.wasm.mem.pages-store.wasm.mem.pages := by
      rw [tailPages,zeroedPages,decodedPages,allocatedPages]
      omega
    have arithmetic := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add valuesBound decodeBound)
      scratchBound) tailBound
    rw [← telescope,Nat.mul_add]
    omega

end Project.Mergesort.DriverCompletionCost
