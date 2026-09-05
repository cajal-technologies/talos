import CodeLib.Examples.MergeSort.TotalProof
import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.Examples.MergeSort

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep

set_option maxHeartbeats 800000

def mergeSortConfig
    (source temporary : UInt32) (input scratch : List UInt32) : Config Unit :=
  { expr := .running
      ⟨({ values := mergeSortArguments source temporary input.length [] } : Locals),
        [.call 0], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := mergeSortModule, host := {} }], entry := ⟨0⟩ }
        wasm := mergeSortExampleStore source temporary input scratch } }

-- heap map mirroring writeWordArray writes
def mergeSortHeapAux
    (σ : WasmHeapMap (Option UInt8)) (base : UInt32) :
    List UInt32 → WasmHeapMap (Option UInt8)
  | [] => σ
  | x :: rest => mergeSortHeapAux (store32Heap σ 0 base x) (base + 4) rest

def mergeSortHeap
    (source temporary : UInt32) (input scratch : List UInt32) :
    WasmHeapMap (Option UInt8) :=
  mergeSortHeapAux (mergeSortHeapAux ∅ source input) temporary scratch

private theorem writeWordArray_pages
    (mem : Mem) (base : UInt32) (xs : List UInt32) :
    (writeWordArray mem base xs).pages = mem.pages := by
  induction xs generalizing mem base with
  | nil => rfl
  | cons x rest ih => exact ih (mem.write32 base x) (base + 4)

private theorem mergeSortHeapAux_agrees
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32)
    (xs : List UInt32)
    (hnoWrap : base.toNat + 4 * xs.length + 4 ≤ 4294967296)
    (h_agree : heapAgreesWithMem σ (fun id => if id = 0 then some mem else none)) :
    heapAgreesWithMem (mergeSortHeapAux σ base xs)
      (fun id => if id = 0 then some (writeWordArray mem base xs) else none) := by
  induction xs generalizing σ mem base with
  | nil => exact h_agree
  | cons x rest ih =>
    simp only [mergeSortHeapAux, writeWordArray, List.length_cons] at *
    have h4 : (base + 4).toNat = base.toNat + 4 :=
      UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    apply ih (store32Heap σ 0 base x) (mem.write32 base x) (base + 4)
    · rw [h4]; omega
    · exact store32_sound0 σ mem base x h1 h2 h3 h_agree

private theorem mergeSortHeapAux_inBounds
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32)
    (xs : List UInt32)
    (hnoWrap : base.toNat + 4 * xs.length + 4 ≤ 4294967296)
    (hbound : base.toNat + 4 * xs.length ≤ mem.pages * 65536)
    (h_inBounds : heapAddressesInBounds σ (fun id => if id = 0 then some mem else none)) :
    heapAddressesInBounds (mergeSortHeapAux σ base xs)
      (fun id => if id = 0 then some (writeWordArray mem base xs) else none) := by
  induction xs generalizing σ mem base with
  | nil => exact h_inBounds
  | cons x rest ih =>
    simp only [mergeSortHeapAux, writeWordArray, List.length_cons] at *
    have h4 : (base + 4).toNat = base.toNat + 4 :=
      UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    apply ih (store32Heap σ 0 base x) (mem.write32 base x) (base + 4)
    · rw [h4]; omega
    · have : (mem.write32 base x).pages = mem.pages := rfl
      rw [this, h4]; omega
    · exact store32_inBounds0 σ mem base x h1 h2 h3 (by omega) h_inBounds

private theorem mergeSortHeapAux_get?_none
    (σ : WasmHeapMap (Option UInt8)) (base : UInt32) (xs : List UInt32)
    (addr : UInt32)
    (hnoWrap : base.toNat + 4 * xs.length + 4 ≤ 4294967296)
    (hout : addr.toNat < base.toNat ∨ base.toNat + 4 * xs.length ≤ addr.toNat)
    (hσ : get? σ (⟨0, addr⟩ : MemoryKey) = none) :
    get? (mergeSortHeapAux σ base xs) (⟨0, addr⟩ : MemoryKey) = none := by
  induction xs generalizing σ base with
  | nil => exact hσ
  | cons x rest ih =>
    simp only [mergeSortHeapAux, List.length_cons] at *
    have h4 : (base + 4).toNat = base.toNat + 4 :=
      UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    have hne0 : addr ≠ base := by
      intro heq; have := congrArg UInt32.toNat heq; rcases hout with h | h <;> omega
    have hne1 : addr ≠ base + 1 := by
      intro heq; have := congrArg UInt32.toNat heq; rw [h1] at this
      rcases hout with h | h <;> omega
    have hne2 : addr ≠ base + 2 := by
      intro heq; have := congrArg UInt32.toNat heq; rw [h2] at this
      rcases hout with h | h <;> omega
    have hne3 : addr ≠ base + 3 := by
      intro heq; have := congrArg UInt32.toNat heq; rw [h3] at this
      rcases hout with h | h <;> omega
    have keyNe : ∀ {a b : UInt32}, a ≠ b → ((⟨0, b⟩ : MemoryKey) ≠ ⟨0, a⟩) :=
      fun hne h => hne (congrArg MemoryKey.addr h).symm
    have hσ' : get? (store32Heap σ 0 base x) (⟨0, addr⟩ : MemoryKey) = none := by
      unfold store32Heap
      rw [get?_insert_ne (keyNe hne3), get?_insert_ne (keyNe hne2),
          get?_insert_ne (keyNe hne1), get?_insert_ne (keyNe hne0)]
      exact hσ
    apply ih (store32Heap σ 0 base x) (base + 4)
    · rw [h4]; omega
    · rcases hout with h | h
      · left; rw [h4]; omega
      · right; rw [h4]; omega
    · exact hσ'

private theorem mergeSortHeapAux_pointsTo [WasmHeapGS Unit]
    (σ : WasmHeapMap (Option UInt8)) (base : UInt32) (xs : List UInt32)
    (hnoWrap : base.toNat + 4 * xs.length + 4 ≤ 4294967296)
    (hfresh : ∀ addr : UInt32,
        base.toNat ≤ addr.toNat → addr.toNat < base.toNat + 4 * xs.length →
        get? σ (⟨0, addr⟩ : MemoryKey) = none) :
    ([∗map] address ↦ byte ∈ mergeSortHeapAux σ base xs,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap) address (DFrac.own 1) byte) ⊢
      arrayAt 0 base xs ∗
        ([∗map] address ↦ byte ∈ σ,
          pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap) address (DFrac.own 1) byte) := by
  induction xs generalizing σ base with
  | nil =>
    simp only [mergeSortHeapAux, arrayAt]; exact BI.emp_sep.mpr
  | cons x rest ih =>
    simp only [mergeSortHeapAux, arrayAt, List.length_cons] at *
    have h4 : (base + 4).toNat = base.toNat + 4 :=
      UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    have hf0 : get? σ (⟨0, base⟩ : MemoryKey) = none :=
      hfresh base (Nat.le_refl _) (by omega)
    have hf1 : get? σ (⟨0, base + 1⟩ : MemoryKey) = none :=
      hfresh (base + 1) (by rw [h1]; omega) (by rw [h1]; omega)
    have hf2 : get? σ (⟨0, base + 2⟩ : MemoryKey) = none :=
      hfresh (base + 2) (by rw [h2]; omega) (by rw [h2]; omega)
    have hf3 : get? σ (⟨0, base + 3⟩ : MemoryKey) = none :=
      hfresh (base + 3) (by rw [h3]; omega) (by rw [h3]; omega)
    have hnoWrap' : (base + 4).toNat + 4 * rest.length + 4 ≤ 4294967296 := by
      rw [h4]; omega
    have hfresh' : ∀ addr : UInt32,
        (base + 4).toNat ≤ addr.toNat → addr.toNat < (base + 4).toNat + 4 * rest.length →
        get? (store32Heap σ 0 base x) (⟨0, addr⟩ : MemoryKey) = none := by
      intro addr hlo hhi
      have keyNe : ∀ {a b : UInt32}, a ≠ b → ((⟨0, b⟩ : MemoryKey) ≠ ⟨0, a⟩) :=
        fun hne h => hne (congrArg MemoryKey.addr h).symm
      have hne0 : addr ≠ base := by
        intro heq; have := congrArg UInt32.toNat heq; rw [h4] at hlo; omega
      have hne1 : addr ≠ base + 1 := by
        intro heq; have := congrArg UInt32.toNat heq; rw [h1] at this; rw [h4] at hlo; omega
      have hne2 : addr ≠ base + 2 := by
        intro heq; have := congrArg UInt32.toNat heq; rw [h2] at this; rw [h4] at hlo; omega
      have hne3 : addr ≠ base + 3 := by
        intro heq; have := congrArg UInt32.toNat heq; rw [h3] at this; rw [h4] at hlo; omega
      unfold store32Heap
      rw [get?_insert_ne (keyNe hne3), get?_insert_ne (keyNe hne2),
          get?_insert_ne (keyNe hne1), get?_insert_ne (keyNe hne0)]
      exact hfresh addr (by rw [h4] at hlo; omega) (by rw [h4] at hhi; omega)
    iintro Hbytes
    ihave ⟨Hrest, Hstore⟩ := ih (store32Heap σ 0 base x) (base + 4) hnoWrap' hfresh' $$ Hbytes
    ihave ⟨Hhead, Horig⟩ := store32Heap_pointsTo σ 0 base x hf0 hf1 hf2 hf3 h1 h2 h3 $$ Hstore
    iframe

/-- `mergeSortConfig` runs a single instance with a single linear memory, so
memory resolution collapses to "memory 0 is the machine memory". -/
private theorem mergeSortConfig_storeResolve
    (source temporary : UInt32) (input scratch : List UInt32) :
    storeResolve (mergeSortConfig source temporary input scratch).store =
      (fun id : Nat => if id = 0 then
        some (writeWordArray (writeWordArray
          (mergeSortModule.initialStore (α := Unit)).mem source input)
          temporary scratch)
        else none) :=
  (singleMemoryResolve_eq_storeResolve
    (mergeSortConfig source temporary input scratch).store
    (writeWordArray (writeWordArray
      (mergeSortModule.initialStore (α := Unit)).mem source input) temporary scratch)
    rfl (show (mergeSortModule.initialStore (α := Unit)).extraMems = [] from by
      decide +kernel)).symm

private theorem mergeSortHeap_agrees
    (source temporary : UInt32) (input scratch : List UInt32)
    (hbound_s : source.toNat + 4 * input.length ≤ 65536)
    (hbound_t : temporary.toNat + 4 * scratch.length ≤ 65536) :
    heapAgreesWithMem (mergeSortHeap source temporary input scratch)
      (storeResolve (mergeSortConfig source temporary input scratch).store) := by
  simp only [mergeSortHeap]
  have hUSize : UInt32.size = 4294967296 := by decide
  rw [mergeSortConfig_storeResolve source temporary input scratch]
  apply mergeSortHeapAux_agrees _ _ temporary scratch
  · omega
  apply mergeSortHeapAux_agrees _ _ source input
  · omega
  · exact heapAgreesWithMem_empty _

private theorem mergeSortHeap_inBounds
    (source temporary : UInt32) (input scratch : List UInt32)
    (hbound_s : source.toNat + 4 * input.length ≤ 65536)
    (hbound_t : temporary.toNat + 4 * scratch.length ≤ 65536) :
    heapAddressesInBounds (mergeSortHeap source temporary input scratch)
      (storeResolve (mergeSortConfig source temporary input scratch).store) := by
  simp only [mergeSortHeap]
  have hUSize : UInt32.size = 4294967296 := by decide
  have hpages : (mergeSortModule.initialStore (α := Unit)).mem.pages = 1 := rfl
  rw [mergeSortConfig_storeResolve source temporary input scratch]
  apply mergeSortHeapAux_inBounds _ _ temporary scratch
  · omega
  · rw [writeWordArray_pages, hpages]; omega
  apply mergeSortHeapAux_inBounds _ _ source input
  · omega
  · rw [hpages]; omega
  · exact heapAddressesInBounds_empty _

private theorem mergeSortHeap_pointsTo [WasmHeapGS Unit]
    (source temporary : UInt32) (input scratch : List UInt32)
    (hvalid : ValidLayout source temporary input.length)
    (hscr : scratch.length = input.length)
    (hbound_s : source.toNat + 4 * input.length ≤ 65536)
    (hbound_t : temporary.toNat + 4 * scratch.length ≤ 65536) :
    ([∗map] address ↦ byte ∈ mergeSortHeap source temporary input scratch,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap) address (DFrac.own 1) byte) ⊢
      arrayAt 0 source input ∗ arrayAt 0 temporary scratch := by
  simp only [mergeSortHeap]
  have hnoWrap_s : source.toNat + 4 * input.length + 4 ≤ 4294967296 := by omega
  have hnoWrap_t : temporary.toNat + 4 * scratch.length + 4 ≤ 4294967296 := by omega
  -- unfold arrayByteRange so omega can reason about the disjunction
  have hvalidDisj : source.toNat + 4 * input.length ≤ temporary.toNat ∨
      temporary.toNat + 4 * input.length ≤ source.toNat := by
    have h := hvalid.2.2; simp only [arrayByteRange] at h; exact h
  have hfresh_s : ∀ addr : UInt32,
      source.toNat ≤ addr.toNat → addr.toNat < source.toNat + 4 * input.length →
      get? (∅ : WasmHeapMap (Option UInt8)) (⟨0, addr⟩ : MemoryKey) = none := by
    intro addr _ _; exact LawfulPartialMap.get?_empty _
  have hfresh_t : ∀ addr : UInt32,
      temporary.toNat ≤ addr.toNat → addr.toNat < temporary.toNat + 4 * scratch.length →
      get? (mergeSortHeapAux ∅ source input) (⟨0, addr⟩ : MemoryKey) = none := by
    intro addr hlo hhi
    rw [hscr] at hhi
    rcases hvalidDisj with hdisj | hdisj
    · apply mergeSortHeapAux_get?_none ∅ source input addr hnoWrap_s (Or.inr (by omega))
      exact LawfulPartialMap.get?_empty _
    · apply mergeSortHeapAux_get?_none ∅ source input addr hnoWrap_s (Or.inl (by omega))
      exact LawfulPartialMap.get?_empty _
  iintro Hbytes
  ihave ⟨Htmp, Hsource_heap⟩ :=
    mergeSortHeapAux_pointsTo (mergeSortHeapAux ∅ source input) temporary scratch
      hnoWrap_t hfresh_t $$ Hbytes
  ihave ⟨Hsrc, _Hemp⟩ :=
    mergeSortHeapAux_pointsTo ∅ source input hnoWrap_s hfresh_s $$ Hsource_heap
  iframe

-- post conversion: mergeSortPost pins the physical `source` array in every
-- terminal store to a sorted permutation of the input.
private theorem mergeSortPost_to_store {hlc : HasLC} [WasmSmallStepGS hlc Unit]
    (source temporary : UInt32) (input : List UInt32)
    (hbound_s : source.toNat + 4 * input.length ≤ 65536)
    (_values : List Value) :
    mergeSortPost source temporary input ⊢
    (iprop% ∀ (store : MachineStore Unit) (_observations : List StepKind),
      stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
      ⌜∃ output, SortedPermutation input output ∧
        readWordArray store.wasm.mem source input.length = output⌝) := by
  unfold mergeSortPost
  iintro ⟨%output, %_sc, %hsp, %_hscr', Hout, _Htmp'⟩ %store %_obs Hstate
  have hlen : output.length = input.length := hsp.length_eq
  imod arrayAt_readWords32 store 0 [] 0 source output
    (by rw [hlen]; simp only [UInt32.size]; omega) $$
      [$Hstate $Hout] with ⟨_Hstate, _Hout, %hread⟩
  ipureexact ⟨output, hsp, by rw [← hlen]; exact hread⟩

theorem mergesort_partiallyMeets
    (source temporary : UInt32) (input scratch : List UInt32)
    (hvalid : ValidLayout source temporary input.length)
    (hscr : scratch.length = input.length)
    (hbound_s : source.toNat + 4 * input.length ≤ 65536)
    (hbound_t : temporary.toNat + 4 * scratch.length ≤ 65536) :
    SmallStep.PartiallyMeets (mergeSortConfig source temporary input scratch)
      (fun _values store => ∃ output, SortedPermutation input output ∧
        readWordArray store.wasm.mem source input.length = output) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := mergeSortHeap source temporary input scratch)
    (globalσ := (∅ : WasmGlobalMap Value))
  · exact mergeSortHeap_agrees source temporary input scratch hbound_s hbound_t
  · exact mergeSortHeap_inBounds source temporary input scratch hbound_s hbound_t
  · intro index value hget
    rw [LawfulPartialMap.get?_empty] at hget; contradiction
  · simp [mergeSortConfig]
  · intro _gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, Hruntime, _HhostEnv⟩
    ihave ⟨Hsrc, Htmp⟩ :=
      mergeSortHeap_pointsTo source temporary input scratch hvalid hscr hbound_s hbound_t $$ Hbytes
    rw [show (mergeSortConfig source temporary input scratch).store.runtime.currentModule
        = mergeSortModule from rfl]
    simp only [mergeSortConfig]
    iapply wp_mono (mergeSortPost_to_store source temporary input hbound_s)
    iapply twp.to_wp
    iapply_splitl_exact twp_mergeSort_total source temporary input scratch with Hruntime
    unfold mergeSortPre
    isplitl_exacts [Hsrc Htmp]
    isplitl_pureexact hscr
    · ipureintro; exact hvalid

theorem mergesort_terminatesWith
    (source temporary : UInt32) (input scratch : List UInt32)
    (hvalid : ValidLayout source temporary input.length)
    (hscr : scratch.length = input.length)
    (hbound_s : source.toNat + 4 * input.length ≤ 65536)
    (hbound_t : temporary.toNat + 4 * scratch.length ≤ 65536) :
    SmallStep.TerminatesWith (mergeSortConfig source temporary input scratch)
      (fun _values store => ∃ output, SortedPermutation input output ∧
        readWordArray store.wasm.mem source input.length = output) := by
  apply wasm_smallStep_heap_store_terminates
    (α := Unit)
    (σ := mergeSortHeap source temporary input scratch)
  · exact mergeSortHeap_agrees source temporary input scratch hbound_s hbound_t
  · exact mergeSortHeap_inBounds source temporary input scratch hbound_s hbound_t
  · simp [mergeSortConfig]
  · intro _hlc _gs
    iintro ⟨Hbytes, Hruntime⟩
    ihave ⟨Hsrc, Htmp⟩ :=
      mergeSortHeap_pointsTo source temporary input scratch hvalid hscr hbound_s hbound_t $$ Hbytes
    rw [show (mergeSortConfig source temporary input scratch).store.runtime.currentModule
        = mergeSortModule from rfl]
    simp only [mergeSortConfig]
    iapply twp.mono (mergeSortPost_to_store source temporary input hbound_s)
    iapply_splitl_exact twp_mergeSort_total source temporary input scratch with Hruntime
    unfold mergeSortPre
    isplitl_exacts [Hsrc Htmp]
    isplitl_pureexact hscr
    · ipureintro; exact hvalid

end Wasm.Examples.MergeSort
