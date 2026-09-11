import Project.RustHashMap.Contracts
import CodeLib.RustStd.Region
import CodeLib.SepLogic.SmallStepState

/-!
# The bump allocator of the hash map program as owned resources

This module ports the allocator layer of
`Project.Mergesort.Representations` to the hash map program.  The compiled
allocator bodies of the two programs are the same code.  Only the cursor
address and the heap base differ, and both constants come from
`Project.RustHashMap.Contracts`.

The byte ownership is the codelib `Slices.ByteSlice 0` in place of the
mergesort local `ByteSlice`.  The word block views of mergesort are not
ported; the map proofs take them from `Wasm.SepLogic.Slices` when they
need them.

The allocator predicates are tied to the authoritative sparse heap frontier
in `stateInterp`.  Allocation history is not a substitute for freshness:
fresh byte ownership is created only by `stateInterp_alloc_freshRange`.
-/

namespace Project.RustHashMap.Allocator

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open scoped Wasm.SmallStep.Outcome

/-! ## Allocator arithmetic and history -/

structure AllocLayout where
  size : Nat
  alignment : Nat
  deriving Repr, DecidableEq

def AllocLayout.Valid (layout : AllocLayout) : Prop :=
  0 < layout.size ∧
  0 < layout.alignment ∧
  (∃ exponent, layout.alignment = 2 ^ exponent) ∧
  layout.alignment ≤ 2147483648 ∧
  layout.size ≤ 2147483648 - layout.alignment ∧
  layout.size < UInt32.size ∧
  layout.alignment < UInt32.size

def AllocLayout.Matches (layout : AllocLayout)
    (wasmSize wasmAlignment : UInt32) : Prop :=
  wasmSize.toNat = layout.size ∧
  wasmAlignment.toNat = layout.alignment

inductive BumpDecision where
  | success (base finish : UInt32)
  | oom
  deriving Repr, DecidableEq

/-- Exact classification of the allocator's two checked additions, alignment
mask, and signed-end guard. -/
def classifyBump (frontier : Nat) (layout : AllocLayout) : BumpDecision :=
  let sum := frontier + (layout.alignment - 1)
  if _hsum : sum < UInt32.size then
    let sumWord := UInt32.ofNat sum
    let alignmentWord := UInt32.ofNat layout.alignment
    let base := sumWord &&& (0 - alignmentWord)
    let finish := base.toNat + layout.size
    if finish < UInt32.size ∧ finish < 2147483648 then
      .success base (UInt32.ofNat finish)
    else
      .oom
  else
    .oom

private theorem align1_mask (x : UInt32) :
    x &&& (0 - 1) = x := by simp

private theorem align4_mask_toNat (x : UInt32) :
    (x &&& (0 - 4)).toNat = x.toNat - x.toNat % 4 := by
  change (x.toBitVec &&& ((0 - 4 : UInt32).toBitVec)).toNat =
    x.toBitVec.toNat - x.toBitVec.toNat % 4
  have hmask :
      ((0 - 4 : UInt32).toBitVec) = BitVec.allOnes 32 <<< 2 := by decide
  rw [hmask, ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]
  have hdiv : x.toBitVec.toNat / 4 * 4 =
      x.toBitVec.toNat - x.toBitVec.toNat % 4 := by omega
  have hbound : x.toBitVec.toNat / 4 * 4 < 4294967296 := by
    have hx := x.toBitVec.isLt
    omega
  change (x.toBitVec.toNat / 4 * 4) % 4294967296 =
    x.toBitVec.toNat - x.toBitVec.toNat % 4
  simpa only [Nat.mod_eq_of_lt hbound] using hdiv

/-- The exact arithmetic facts exposed by a successful bump classification. -/
theorem classifyBump_success_facts
    (frontier : Nat) (layout : AllocLayout) (base finish : UInt32)
    (h : classifyBump frontier layout = .success base finish) :
    let sum := frontier + (layout.alignment - 1)
    sum < UInt32.size ∧
    base = (UInt32.ofNat sum &&&
      (0 - UInt32.ofNat layout.alignment)) ∧
    base.toNat + layout.size < UInt32.size ∧
    base.toNat + layout.size < 2147483648 ∧
    finish.toNat = base.toNat + layout.size := by
  let sum := frontier + (layout.alignment - 1)
  change (if _hsum : sum < UInt32.size then
      let sumWord := UInt32.ofNat sum
      let alignmentWord := UInt32.ofNat layout.alignment
      let base := sumWord &&& (0 - alignmentWord)
      let finish := base.toNat + layout.size
      if finish < UInt32.size ∧ finish < 2147483648 then
        BumpDecision.success base (UInt32.ofNat finish)
      else BumpDecision.oom
    else BumpDecision.oom) = BumpDecision.success base finish at h
  split at h
  · rename_i hsum
    dsimp only at h
    split at h
    · rename_i hend
      injection h with hbase hfinish
      subst base
      subst finish
      dsimp only at hend ⊢; exact ⟨hsum, rfl, hend.1, hend.2,
        UInt32.toNat_ofNat_of_lt' hend.1⟩
    · contradiction
  · contradiction

inductive AllocationStatus where
  | live
  | retired
  deriving Repr, DecidableEq

structure AllocationRecord where
  allocationId : Nat
  ptr : UInt32
  layout : AllocLayout
  status : AllocationStatus
  deriving Repr, DecidableEq

def AllocationStatus.toMetaStatus : AllocationStatus → AllocationMetaStatus
  | .live => .live
  | .retired => .retired

def AllocationRecord.toMeta (record : AllocationRecord) : AllocationMeta :=
  { ptr := record.ptr
    size := record.layout.size
    alignment := record.layout.alignment
    status := record.status.toMetaStatus }

/-- The metadata value created for a new live allocation. -/
def liveMeta (ptr : UInt32) (layout : AllocLayout) : AllocationMeta :=
  { ptr := ptr
    size := layout.size
    alignment := layout.alignment
    status := .live }

/-- The metadata value retained after the no-op Wasm deallocator is called. -/
def retiredMeta (ptr : UInt32) (layout : AllocLayout) : AllocationMeta :=
  { ptr := ptr
    size := layout.size
    alignment := layout.alignment
    status := .retired }

def allocationLayout (metadata : AllocationMeta) : AllocLayout :=
  { size := metadata.size, alignment := metadata.alignment }

def allocationEndExclusive (metadata : AllocationMeta) : Nat :=
  metadata.ptr.toNat + metadata.size

def AllocationMetaValid (metadata : AllocationMeta) : Prop :=
  (allocationLayout metadata).Valid ∧
    metadata.ptr ≠ 0 ∧
    metadata.ptr.toNat % metadata.alignment = 0

/-- At the two alignments used by reachable hash map allocations, a
successful classification yields a fresh, non-null, aligned range and valid
metadata.  This is the pure arithmetic bridge used by allocator call specs. -/
theorem classifyBump_success_reachable
    (frontier : Nat) (layout : AllocLayout) (base finish : UInt32)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvalid : layout.Valid)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish) :
    frontier ≤ base.toNat ∧
    base ≠ 0 ∧
    base.toNat % layout.alignment = 0 ∧
    base.toNat + layout.size < UInt32.size ∧
    base.toNat + layout.size < 2147483648 ∧
    finish.toNat = base.toNat + layout.size ∧
    AllocationMetaValid (liveMeta base layout) := by
  have hraw :=
    classifyBump_success_facts frontier layout base finish hclassify
  dsimp only at hraw
  rcases hraw with ⟨hsum, hbase, hendWord, hendSigned, hfinish⟩
  have hheapBasePositive : 0 < heapBase.toNat := by decide
  rcases halignment with halignment | halignment
  · have hsum' : frontier < UInt32.size := by
      simpa only [halignment, Nat.reduceSubDiff, Nat.add_zero] using hsum
    have hbase' :
        base = UInt32.ofNat frontier &&& (0 - 1) := by
      norm_num [halignment] at hbase ⊢; exact hbase
    rw [align1_mask] at hbase'
    have hbaseNat : base.toNat = frontier := by
      rw [hbase', UInt32.toNat_ofNat_of_lt' hsum']
    have hnonnull : base ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt32.toNat hzero; simp only [UInt32.toNat_zero] at hzeroNat
      rw [hbaseNat] at hzeroNat; omega
    have haligned : base.toNat % layout.alignment = 0 := by
      rw [halignment]; exact Nat.mod_one _
    refine ⟨?_, hnonnull, haligned, hendWord, hendSigned, hfinish, ?_⟩
    · omega
    · exact ⟨hvalid, hnonnull, haligned⟩
  · have hsum' : frontier + 3 < UInt32.size := by
      norm_num [halignment] at hsum ⊢; exact hsum
    have hbase' :
        base = UInt32.ofNat (frontier + 3) &&& (0 - 4) := by
      norm_num [halignment] at hbase ⊢; exact hbase
    have hsumWord :
        (UInt32.ofNat (frontier + 3)).toNat = frontier + 3 := UInt32.toNat_ofNat_of_lt' hsum'
    have hbaseNat :
        base.toNat = (frontier + 3) - (frontier + 3) % 4 := by
      rw [hbase', align4_mask_toNat, hsumWord]
    have hrem : (frontier + 3) % 4 < 4 :=
      Nat.mod_lt _ (by decide)
    have hstart : frontier ≤ base.toNat := by omega
    have hmod4 : base.toNat % 4 = 0 := by
      simpa only [hbaseNat] using Nat.mod_eq_zero_of_dvd
        (Nat.dvd_sub_mod (n := 4) (frontier + 3))
    have hnonnull : base ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt32.toNat hzero; simp only [UInt32.toNat_zero] at hzeroNat
      rw [hzeroNat] at hstart; omega
    have haligned : base.toNat % layout.alignment = 0 := by simpa only [halignment] using hmod4
    exact ⟨hstart, hnonnull, haligned, hendWord, hendSigned, hfinish,
      hvalid, hnonnull, haligned⟩

/-- Alignment-one bump allocation is exact: no padding is introduced, so the
returned pointer is the old frontier and the returned cursor is that frontier
plus the requested size. -/
theorem classifyBump_success_align1
    (frontier size : Nat) (base finish : UInt32)
    (hclassify :
      classifyBump frontier { size := size, alignment := 1 } =
        .success base finish) :
    frontier < UInt32.size ∧
      base = UInt32.ofNat frontier ∧
      base.toNat = frontier ∧
      base.toNat + size < UInt32.size ∧
      base.toNat + size < 2147483648 ∧
      finish.toNat = frontier + size := by
  have hraw :=
    classifyBump_success_facts frontier
      { size := size, alignment := 1 } base finish hclassify
  dsimp only at hraw
  rcases hraw with ⟨hsum, hbase, hendWord, hendSigned, hfinish⟩
  have hfrontier : frontier < UInt32.size := by
    norm_num at hsum ⊢; exact hsum
  have hbase' : base = UInt32.ofNat frontier := by
    norm_num at hbase; exact hbase
  have hbaseNat : base.toNat = frontier := by
    rw [hbase', UInt32.toNat_ofNat_of_lt' hfrontier]
  exact ⟨hfrontier, hbase', hbaseNat, hendWord, hendSigned, by
    rw [hfinish, hbaseNat]⟩

/-! ## Allocator memory-growth arithmetic -/

/-- The exact page target computed by the three reachable bump-allocation
paths after their signed-end guard. -/
def allocatorRequiredPages (finish : UInt32) : UInt32 :=
  (finish + 65535) >>> (16 : UInt32)

/-- Below the allocator's signed-end limit, its generated shift computes the
ordinary ceiling page count without wrapping the preceding addition. -/
theorem allocatorRequiredPages_toNat (finish : UInt32)
    (hfinish : finish.toNat < 2147483648) :
    (allocatorRequiredPages finish).toNat =
      (finish.toNat + 65535) / 65536 := by
  have hsum : finish.toNat + 65535 < 2 ^ 32 := by omega
  unfold allocatorRequiredPages
  rw [UInt32.toNat_shiftRight,
    show (16 : UInt32).toNat % 32 = 16 by decide,
    Nat.shiftRight_eq_div_pow]
  norm_num
  rw [show (65535 : UInt32).toNat = 65535 by decide]
  norm_num at hsum
  rw [Nat.mod_eq_of_lt hsum]

/-- The generated ceiling page count physically covers every byte through the
accepted allocation finish. -/
theorem allocatorRequiredPages_covers (finish : UInt32)
    (hfinish : finish.toNat < 2147483648) :
    finish.toNat ≤ (allocatorRequiredPages finish).toNat * 65536 := by
  rw [allocatorRequiredPages_toNat finish hfinish]
  have hself : (finish.toNat + 65535) / 65536 ≤
      (finish.toNat + 65535) / 65536 := Nat.le_refl _
  have hceil :=
    (Nat.div_le_iff_le_mul (by norm_num : 0 < 65536)).mp hself
  omega

/-- A successful signed-end check bounds the allocator's target by 2 GiB, or
32768 Wasm pages.  This also justifies that the `finish + 65535` computation
used for ceiling division cannot wrap. -/
theorem allocatorRequiredPages_le_signedLimit (finish : UInt32)
    (hfinish : finish.toNat < 2147483648) :
    (allocatorRequiredPages finish).toNat ≤ 32768 := by
  have hsum : finish.toNat + 65535 < 2 ^ 32 := by omega
  have hquot :
      (finish.toNat + 65535) / 65536 < 32769 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 65536)]; omega
  have hquotle :
      (finish.toNat + 65535) / 65536 ≤ 32768 := by omega
  unfold allocatorRequiredPages
  rw [UInt32.toNat_shiftRight,
    show (16 : UInt32).toNat % 32 = 16 by decide,
    Nat.shiftRight_eq_div_pow]
  norm_num
  rw [show (65535 : UInt32).toNat = 65535 by decide]
  norm_num at hsum
  simpa only [Nat.mod_eq_of_lt hsum] using hquotle

/-- At a cap large enough for the target, growing by the exact difference
returns the old page count and installs the target page count. -/
theorem memoryGrow_to_pages (memory : Mem) (target cap : Nat)
    (hle : memory.pages ≤ target)
    (hcap : target ≤ cap)
    (htarget : target < UInt32.size) :
    memory.grow (UInt32.ofNat (target - memory.pages)) cap =
      some ({ memory with pages := target }, memory.pages) := by
  have hdiff : target - memory.pages < UInt32.size := by omega
  simp [Mem.grow, UInt32.toNat_ofNat_of_lt' hdiff,
    Nat.add_sub_of_le hle, hcap]

/-- Once `memory.size < requiredPages`, the exact subtraction emitted by the
allocator grows successfully at the Wasm i32 hard cap. -/
theorem allocatorMemoryGrow_succeeds (memory : Mem) (finish : UInt32)
    (hfinish : finish.toNat < 2147483648)
    (hneed : memory.pages < (allocatorRequiredPages finish).toNat) :
    memory.grow
      (allocatorRequiredPages finish - UInt32.ofNat memory.pages)
      Module.memoryHardCap =
      some ({ memory with pages :=
        (allocatorRequiredPages finish).toNat }, memory.pages) := by
  have htarget :=
    allocatorRequiredPages_le_signedLimit finish hfinish
  have hpages : memory.pages < UInt32.size := by
    norm_num [UInt32.size] at htarget ⊢; omega
  have hpagesWord :
      (UInt32.ofNat memory.pages).toNat = memory.pages :=
    UInt32.toNat_ofNat_of_lt' hpages
  have hleWords :
      UInt32.ofNat memory.pages ≤ allocatorRequiredPages finish := by
    rw [UInt32.le_iff_toNat_le_toNat, hpagesWord]; omega
  have hdelta :
      (allocatorRequiredPages finish -
        UInt32.ofNat memory.pages).toNat =
      (allocatorRequiredPages finish).toNat - memory.pages := by
    rw [UInt32.toNat_sub_of_le _ _ hleWords, hpagesWord]
  unfold Mem.grow
  simp only [hdelta, Nat.add_sub_of_le (Nat.le_of_lt hneed)]
  norm_num [Module.memoryHardCap]; omega

/-- The frozen module declares no maximum, so its declaration-level cap is
the interpreter's i32 hard cap. -/
theorem module_memoryCap :
    Project.RustHashMap.«module».memoryCap = Module.memoryHardCap := by rfl

/-- Instantiation materializes that declaration-level cap in memory-resource
metadata.  A modular allocator proof still needs a state-linked invariant
showing that this immutable field remains the current store's metadata. -/
theorem initialStore_memoryCaps :
    (Project.RustHashMap.«module».initialStore
      (α := Universal.State)).memoryCaps = [Module.memoryHardCap] := by rfl

theorem initialStore_memoryCap :
    (Project.RustHashMap.«module».initialStore
      (α := Universal.State)).memoryCap Project.RustHashMap.«module» 0 =
      Module.memoryHardCap := by rfl

/-- Map-native allocation history.  `nextId` makes freshness explicit; the
map itself is exactly the value stored in ghost authority. -/
structure AllocationHistory where
  records : WasmAllocationMap AllocationMeta
  nextId : Nat

def AllocationHistory.empty : AllocationHistory :=
  { records := ∅, nextId := 0 }

def AllocationHistory.allocate (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout) : AllocationHistory :=
  { records := insert history.records history.nextId (liveMeta ptr layout)
    nextId := history.nextId + 1 }

def AllocationHistory.retire (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32)
    (layout : AllocLayout) : AllocationHistory :=
  { records := insert history.records allocationId (retiredMeta ptr layout)
    nextId := history.nextId }

/-- The metadata transition performed by the reachable reallocator: append
the fresh live block, then retain the old allocation as retired metadata. -/
def AllocationHistory.reallocate (history : AllocationHistory)
    (oldId : Nat) (oldPtr : UInt32) (oldLayout : AllocLayout)
    (newPtr : UInt32) (newLayout : AllocLayout) : AllocationHistory :=
  (history.allocate newPtr newLayout).retire oldId oldPtr oldLayout

def AllocMetaAuth {host : Type} (heapId : GName)
    (history : AllocationHistory) : IProp (WasmHeapGF host) :=
  ghost_map_auth heapId (DFrac.own 1) history.records

/-- Exclusive live-allocation handle.  Its value contains the complete
pointer/layout/status tuple, so agreement with `AllocMetaAuth` rules out using
one allocation identifier for two blocks. -/
def AllocToken {host : Type} (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) : IProp (WasmHeapGF host) :=
  ghost_map_elem heapId (DFrac.own 1) allocationId (liveMeta ptr layout)

/-- Complete ownership of one live allocation. -/
def LiveBlock {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) (bytes : List UInt8) :
    IProp (WasmHeapGF host) := iprop%
  AllocToken heapId allocationId ptr layout ∗
    Slices.ByteSlice 0 ptr bytes ∗
    ⌜bytes.length = layout.size ∧
      ptr ≠ 0 ∧
      ptr.toNat % layout.alignment = 0⌝

/-- The deliberately transparent open/reseal law for a complete live block. -/
theorem LiveBlock_open {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) (bytes : List UInt8) :
    LiveBlock (host := host) heapId allocationId ptr layout bytes ⊣⊢
      iprop(AllocToken heapId allocationId ptr layout ∗
        Slices.ByteSlice 0 ptr bytes ∗
        ⌜bytes.length = layout.size ∧ ptr ≠ 0 ∧
          ptr.toNat % layout.alignment = 0⌝) :=
  .rfl

/-- Temporarily expose all physical bytes of a live allocation while framing
its exclusive allocation token.  Any same-sized replacement bytes reseal the
same live allocation. -/
theorem LiveBlock_bytesFocus {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (ptr : UInt32) (layout : AllocLayout) (oldBytes : List UInt8) :
    LiveBlock (host := host) heapId allocationId ptr layout oldBytes ⊢
      iprop(Slices.ByteSlice 0 ptr oldBytes ∗
        (∀ newBytes : List UInt8,
          ⌜newBytes.length = layout.size⌝ -∗
          Slices.ByteSlice 0 ptr newBytes -∗
          LiveBlock heapId allocationId ptr layout newBytes)) := by
  unfold LiveBlock
  iintro ⟨Htoken, Hbytes, %hfacts⟩
  isplitl_exact Hbytes
  · iintro %newBytes
    iintro %hnewLength
    iintro HnewBytes; iframe Htoken HnewBytes
    ipureexact ⟨hnewLength, hfacts.2.1, hfacts.2.2⟩


/-- Pure chronological invariants shared by every allocator contract.  The
map is complete below `nextId`, contains nothing at or above it, and numeric
allocation order is physical non-overlap order. -/
def HistoryWellFormed (frontier : Nat)
    (history : AllocationHistory) : Prop :=
  (∀ allocationId, allocationId < history.nextId →
      ∃ metadata, get? history.records allocationId = some metadata) ∧
  (∀ allocationId metadata,
      get? history.records allocationId = some metadata →
      allocationId < history.nextId ∧
      AllocationMetaValid metadata ∧
      allocationEndExclusive metadata ≤ frontier) ∧
  (∀ earlierId laterId earlier later,
      earlierId < laterId →
      get? history.records earlierId = some earlier →
      get? history.records laterId = some later →
      allocationEndExclusive earlier ≤ later.ptr.toNat) ∧
  get? history.records history.nextId = none ∧
  ((history.nextId = 0 ∧ frontier = heapBase.toNat) ∨
    (0 < history.nextId ∧
      ∃ last, get? history.records (history.nextId - 1) = some last ∧
        allocationEndExclusive last = frontier))

/-- Appending a valid block at or after the old frontier preserves the full
chronological invariant. -/
theorem HistoryWellFormed.allocate
    (frontier : Nat) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hwf : HistoryWellFormed frontier history)
    (hvalid : AllocationMetaValid (liveMeta ptr layout))
    (hstart : frontier ≤ ptr.toNat) :
    HistoryWellFormed (ptr.toNat + layout.size)
      (history.allocate ptr layout) := by
  rcases hwf with ⟨hcomplete, hrecords, hordered, hfresh, hlast⟩
  simp only [HistoryWellFormed, AllocationHistory.allocate] at ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro allocationId hid
    by_cases heq : allocationId = history.nextId
    · subst allocationId; exact ⟨liveMeta ptr layout, get?_insert_eq rfl⟩
    · have hlt : allocationId < history.nextId := by omega
      obtain ⟨metadata, hmetadata⟩ := hcomplete allocationId hlt
      exact ⟨metadata, (get?_insert_ne (Ne.symm heq)).trans hmetadata⟩
  · intro allocationId metadata hmetadata
    by_cases heq : history.nextId = allocationId
    · subst allocationId; rw [get?_insert_eq rfl] at hmetadata
      injection hmetadata with hmetadata
      subst metadata
      exact ⟨by omega, hvalid, by
        simp [allocationEndExclusive, liveMeta]⟩
    · rw [get?_insert_ne heq] at hmetadata
      obtain ⟨hid, hvalidOld, hend⟩ :=
        hrecords allocationId metadata hmetadata
      exact ⟨by omega, hvalidOld, by omega⟩
  · intro earlierId laterId earlier later hid hearlier hlater
    by_cases hlaterId : history.nextId = laterId
    · subst laterId; rw [get?_insert_eq rfl] at hlater
      injection hlater with hlater
      subst later
      have hne : history.nextId ≠ earlierId := by omega
      rw [get?_insert_ne hne] at hearlier
      have hend := (hrecords earlierId earlier hearlier).2.2
      simpa [liveMeta] using _root_.le_trans hend hstart
    · rw [get?_insert_ne hlaterId] at hlater
      by_cases hearlierId : history.nextId = earlierId
      · subst earlierId
        have hlaterLt := (hrecords laterId later hlater).1
        omega
      · rw [get?_insert_ne hearlierId] at hearlier
        exact hordered earlierId laterId earlier later hid hearlier hlater
  · have hnone : get? history.records (history.nextId + 1) = none := by
      cases hget : get? history.records (history.nextId + 1) with
      | none => rfl
      | some metadata =>
          have hlt := (hrecords (history.nextId + 1) metadata hget).1
          omega
    exact (get?_insert_ne (by omega)).trans hnone
  · right
    refine ⟨by omega, liveMeta ptr layout, ?_, ?_⟩
    · simpa using (get?_insert_eq (m := history.records)
        (v := liveMeta ptr layout) rfl)
    · simp [allocationEndExclusive, liveMeta]

/-- Changing a live entry to retired preserves every layout, range, and
chronological fact. -/
theorem HistoryWellFormed.retire
    (frontier : Nat) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (hwf : HistoryWellFormed frontier history)
    (hlookup : get? history.records allocationId =
      some (liveMeta ptr layout)) :
    HistoryWellFormed frontier
      (history.retire allocationId ptr layout) := by
  rcases hwf with ⟨hcomplete, hrecords, hordered, hfresh, hlast⟩
  have hlive := hrecords allocationId (liveMeta ptr layout) hlookup
  have recover :
      ∀ key metadata,
        get? (insert history.records allocationId (retiredMeta ptr layout))
            key = some metadata →
        ∃ oldMetadata,
          get? history.records key = some oldMetadata ∧
          allocationEndExclusive oldMetadata =
            allocationEndExclusive metadata ∧
          oldMetadata.ptr = metadata.ptr := by
    intro key metadata hmetadata
    by_cases hkey : allocationId = key
    · subst key; rw [get?_insert_eq rfl] at hmetadata
      injection hmetadata with hmetadata
      subst metadata
      exact ⟨liveMeta ptr layout, hlookup, by
        simp [allocationEndExclusive, liveMeta, retiredMeta], by
        simp [liveMeta, retiredMeta]⟩
    · rw [get?_insert_ne hkey] at hmetadata; exact ⟨metadata, hmetadata, rfl, rfl⟩
  simp only [HistoryWellFormed, AllocationHistory.retire] at ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro key hkeyLt
    by_cases hkey : allocationId = key
    · subst key; exact ⟨retiredMeta ptr layout, get?_insert_eq rfl⟩
    · obtain ⟨metadata, hmetadata⟩ := hcomplete key hkeyLt
      exact ⟨metadata, (get?_insert_ne hkey).trans hmetadata⟩
  · intro key metadata hmetadata
    by_cases hkey : allocationId = key
    · subst key; rw [get?_insert_eq rfl] at hmetadata
      injection hmetadata with hmetadata
      subst metadata
      refine ⟨hlive.1, ?_, ?_⟩
      · simpa [AllocationMetaValid, allocationLayout, liveMeta, retiredMeta]
          using hlive.2.1
      · simpa [allocationEndExclusive, liveMeta, retiredMeta]
          using hlive.2.2
    · rw [get?_insert_ne hkey] at hmetadata; exact hrecords key metadata hmetadata
  · intro earlierId laterId earlier later hid hearlier hlater
    obtain ⟨oldEarlier, holdEarlier, hendEarlier, _hptrEarlier⟩ :=
      recover earlierId earlier hearlier
    obtain ⟨oldLater, holdLater, _hendLater, hptrLater⟩ :=
      recover laterId later hlater
    calc
      allocationEndExclusive earlier =
          allocationEndExclusive oldEarlier := hendEarlier.symm
      _ ≤ oldLater.ptr.toNat :=
        hordered earlierId laterId oldEarlier oldLater hid
          holdEarlier holdLater
      _ = later.ptr.toNat := congrArg UInt32.toNat hptrLater
  · have hne : allocationId ≠ history.nextId := by omega
    exact (get?_insert_ne hne).trans hfresh
  · rcases hlast with hzero | hpositive
    · exfalso
      omega
    · right
      rcases hpositive with ⟨hnext, last, hlastLookup, hlastEnd⟩
      refine ⟨hnext, ?_⟩
      by_cases hidLast : allocationId = history.nextId - 1
      · refine ⟨retiredMeta ptr layout, get?_insert_eq hidLast, ?_⟩
        have heq : liveMeta ptr layout = last :=
          Option.some.inj (hlookup.symm.trans (hidLast ▸ hlastLookup))
        calc
          allocationEndExclusive (retiredMeta ptr layout) =
              allocationEndExclusive (liveMeta ptr layout) := by rfl
          _ = allocationEndExclusive last :=
            congrArg allocationEndExclusive heq
          _ = frontier := hlastEnd
      · exact ⟨last, (get?_insert_ne hidLast).trans hlastLookup,
          hlastEnd⟩

/-- Physical ownership retained by the no-op deallocator.  Live entries
contribute `emp`; retired entries own both their exclusive retired fragment
and their complete bytes exactly once. -/
def RetiredEntry {host : Type} [WasmHeapGS host]
    (heapId : GName) (allocationId : Nat)
    (metadata : AllocationMeta) : IProp (WasmHeapGF host) :=
  match metadata.status with
  | .live => iprop(emp)
  | .retired => iprop(
      ghost_map_elem heapId (DFrac.own 1) allocationId metadata ∗
      ∃ bytes : List UInt8,
        ⌜bytes.length = metadata.size⌝ ∗ Slices.ByteSlice 0 metadata.ptr bytes)

def RetiredBytes {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory) :
    IProp (WasmHeapGF host) :=
  iprop([∗map] allocationId ↦ metadata ∈ history.records,
    RetiredEntry heapId allocationId metadata)

/-- Complete bump-allocator authority.  Live bytes remain with clients through
`LiveBlock`; this predicate owns only cursor/frontier/metadata authority and
bytes whose records are retired. -/
def BumpHeap {host : Type} [WasmHeapGS host] [WasmHeapDomainGS host]
    [WasmMemoryPagesGS host]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) : IProp (WasmHeapGF host) := iprop%
  pointsTo_u32 0 allocatorCursor storedCursor ∗
    heapFrontierOwn frontier ∗
    AllocMetaAuth heapId history ∗
    RetiredBytes heapId history ∗
    ∃ ownedPages : Nat,
      memoryPagesOwn ownedPages ∗
      ⌜heapBase.toNat ≤ frontier ∧
        frontier < 2147483648 ∧
        (storedCursor = 0 ↔
          history.nextId = 0 ∧ frontier = heapBase.toNat) ∧
        (storedCursor ≠ 0 → storedCursor.toNat = frontier) ∧
        HistoryWellFormed frontier history ∧
        frontier ≤ ownedPages * 65536⌝

/-- Expose every component of `BumpHeap` without changing ownership. -/
theorem BumpHeap_open {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) :
    BumpHeap (host := host) heapId storedCursor frontier history ⊣⊢
      iprop(pointsTo_u32 0 allocatorCursor storedCursor ∗
        heapFrontierOwn frontier ∗
        AllocMetaAuth heapId history ∗
        RetiredBytes heapId history ∗
        ∃ ownedPages : Nat,
          memoryPagesOwn ownedPages ∗
          ⌜heapBase.toNat ≤ frontier ∧
            frontier < 2147483648 ∧
            (storedCursor = 0 ↔
              history.nextId = 0 ∧ frontier = heapBase.toNat) ∧
            (storedCursor ≠ 0 → storedCursor.toNat = frontier) ∧
            HistoryWellFormed frontier history ∧
            frontier ≤ ownedPages * 65536⌝) :=
  .rfl

/-- Allocate empty metadata authority; its ghost name is the logical heap
identity threaded through every block and allocator contract. -/
theorem AllocMetaAuth_alloc_empty {host : Type} :
    ⊢@{IProp (WasmHeapGF host)} |==>
      ∃ heapId : GName, AllocMetaAuth heapId AllocationHistory.empty := by
  imod (ghost_map_alloc_empty (GF := WasmHeapGF host) (K := Nat)
      (V := AllocationMeta) (H := WasmAllocationMap)) with
    ⟨%heapId, Hauth⟩
  imodintro
  iexists heapId
  unfold AllocMetaAuth AllocationHistory.empty
  iexact Hauth

theorem historyWellFormed_empty :
    HistoryWellFormed heapBase.toNat AllocationHistory.empty := by
  simp [HistoryWellFormed, AllocationHistory.empty,
    LawfulPartialMap.get?_empty]

/-- Assemble the initial allocator authority from the physical zero cursor,
the tight frontier fragment, and empty metadata. -/
theorem BumpHeap_empty {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (ownedPages : Nat)
    (hphysical : heapBase.toNat ≤ ownedPages * 65536) :
    pointsTo_u32 0 allocatorCursor 0 ∗
      heapFrontierOwn heapBase.toNat ∗
      AllocMetaAuth heapId AllocationHistory.empty ∗
      memoryPagesOwn ownedPages ⊢
      BumpHeap (host := host) heapId 0 heapBase.toNat
        AllocationHistory.empty := by
  unfold BumpHeap RetiredBytes
  simp only [AllocationHistory.empty, BI.BigSepM.bigSepM_empty.to_eq]
  iintro ⟨Hcursor, Hfrontier, Hmetadata, Hpages⟩; iframe Hcursor Hfrontier Hmetadata
  isplitl []
  · itrivial
  · iexists ownedPages
    iframe_pureexact using [Hpages] => ⟨Nat.le_refl _, by decide, by decide, by decide,
      historyWellFormed_empty, hphysical⟩

/-- A token agrees with the unique live metadata entry in the named heap. -/
theorem AllocMetaAuth_token_agree {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout) :
    AllocMetaAuth (host := host) heapId history ∗
      AllocToken heapId allocationId ptr layout ⊢
      iprop(⌜get? history.records allocationId =
        some (liveMeta ptr layout)⌝) := by
  unfold AllocMetaAuth AllocToken
  iintro ⟨Hauth, Htoken⟩
  iapply ghost_map_lookup $$ Hauth Htoken

/-- Extend metadata at `nextId` and return the new exclusive live token. -/
theorem AllocMetaAuth_insert {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hfresh : get? history.records history.nextId = none) :
    AllocMetaAuth (host := host) heapId history ==∗
      AllocMetaAuth heapId (history.allocate ptr layout) ∗
      AllocToken heapId history.nextId ptr layout := by
  unfold AllocMetaAuth AllocToken
  iintro Hauth
  imod ghost_map_insert history.nextId (liveMeta ptr layout) hfresh $$ Hauth with
    ⟨Hauth, Htoken⟩
  imodintro
  isimp only [AllocationHistory.allocate]
  iframe

/-- Atomically change one live metadata entry to retired.  The returned
fragment is linear and must be placed in `RetiredBytes` with the block bytes. -/
theorem AllocMetaAuth_retire {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout) :
    AllocMetaAuth (host := host) heapId history ∗
      AllocToken heapId allocationId ptr layout ==∗
      AllocMetaAuth heapId (history.retire allocationId ptr layout) ∗
      ghost_map_elem heapId (DFrac.own 1) allocationId
        (retiredMeta ptr layout) := by
  unfold AllocMetaAuth AllocToken
  iintro ⟨Hauth, Htoken⟩
  imod ghost_map_update (retiredMeta ptr layout) $$ Hauth Htoken with
    ⟨Hauth, Htoken⟩
  imodintro
  isimp only [AllocationHistory.retire]
  iframe

/-- A fresh live entry contributes `emp`, so allocation preserves all retired
storage ownership. -/
theorem RetiredBytes_insert_live {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hfresh : get? history.records history.nextId = none) :
    RetiredBytes (host := host) heapId history ⊢
      RetiredBytes heapId (history.allocate ptr layout) := by
  unfold RetiredBytes
  change ([∗map] allocationId ↦ metadata ∈ history.records,
      RetiredEntry heapId allocationId metadata) ⊢
    [∗map] allocationId ↦ metadata ∈
      insert history.records history.nextId (liveMeta ptr layout),
      RetiredEntry heapId allocationId metadata
  rw [(BI.BigSepM.bigSepM_insert hfresh).to_eq]
  unfold RetiredEntry liveMeta
  iintro Hretired
  isplitl []
  · itrivial
  · iexact Hretired

/-- Move the fragment returned by `AllocMetaAuth_retire` and the entire live
byte range into the retired-resource map. -/
theorem RetiredBytes_retire {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (bytes : List UInt8)
    (hlookup : get? history.records allocationId =
      some (liveMeta ptr layout)) :
    RetiredBytes (host := host) heapId history ∗
      ghost_map_elem heapId (DFrac.own 1) allocationId
        (retiredMeta ptr layout) ∗
      Slices.ByteSlice 0 ptr bytes ∗
      ⌜bytes.length = layout.size⌝ ⊢
      RetiredBytes heapId (history.retire allocationId ptr layout) := by
  unfold RetiredBytes
  isimp only [AllocationHistory.retire]
  iintro ⟨Hretired, Hfragment, Hbytes, %hlen⟩
  ihave ⟨Hold, Hclose⟩ :=
    BI.BigSepM.bigSepM_insert_acc hlookup $$ Hretired
  isimp only [RetiredEntry, liveMeta] at Hold
  iclear Hold
  ispecialize Hclose $$ %(retiredMeta ptr layout)
  iapply Hclose
  unfold RetiredEntry retiredMeta
  isplitl_exact Hfragment
  · iexists bytes
    iframe_pureexact using [Hbytes] => (by simpa [retiredMeta] using hlen)

/-- The complete metadata-side allocation transition.  Physical fresh-byte
ownership is deliberately supplied separately by `stateInterp_alloc_freshRange`. -/
theorem AllocatorResources_insert {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (ptr : UInt32) (layout : AllocLayout)
    (hfresh : get? history.records history.nextId = none) :
    AllocMetaAuth (host := host) heapId history ∗
      RetiredBytes heapId history ==∗
      AllocMetaAuth heapId (history.allocate ptr layout) ∗
      RetiredBytes heapId (history.allocate ptr layout) ∗
      AllocToken heapId history.nextId ptr layout := by
  iintro ⟨Hauth, Hretired⟩
  imod AllocMetaAuth_insert heapId history ptr layout hfresh $$ Hauth with
    ⟨Hauth, Htoken⟩
  ihave HretiredNew := RetiredBytes_insert_live heapId history ptr layout
    hfresh $$ Hretired
  imodintro
  iframe

/-- Assemble the allocator's exact post-commit resources.  The caller supplies
the cursor word and frontier fragment *after* the Wasm store and sparse-range
state update; this lemma performs only the metadata update and representation
reassembly. -/
theorem BumpHeap_commit {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (frontier : Nat) (history : AllocationHistory)
    (base finish : UInt32) (layout : AllocLayout) (bytes : List UInt8)
    (ownedPages : Nat)
    (hheapBase : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hvalid : layout.Valid)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hbytesLength : bytes.length = layout.size)
    (hphysical : finish.toNat ≤ ownedPages * 65536) :
    pointsTo_u32 0 allocatorCursor finish ∗
      heapFrontierOwn finish.toNat ∗
      AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗
      memoryPagesOwn ownedPages ∗
      Slices.ByteSlice 0 base bytes ==∗
      BumpHeap heapId finish finish.toNat
          (history.allocate base layout) ∗
        LiveBlock heapId history.nextId base layout bytes := by
  rcases classifyBump_success_reachable frontier layout base finish
      hheapBase hvalid halignment hclassify with
    ⟨hstart, hnonnull, haligned, _hendWord, hendSigned,
      hfinish, hmetadata⟩
  have hfresh : get? history.records history.nextId = none :=
    hwf.2.2.2.1
  have hwfNew :
      HistoryWellFormed finish.toNat (history.allocate base layout) := by
    rw [hfinish]; exact HistoryWellFormed.allocate frontier history base layout hwf
      hmetadata hstart
  have hbaseNatNe : base.toNat ≠ 0 := by
    intro hzero
    exact hnonnull (UInt32.toNat_inj.mp (by simpa using hzero))
  have hfinishPositive : 0 < finish.toNat := by omega
  have hfinishSigned : finish.toNat < 2147483648 := by simpa only [hfinish] using hendSigned
  have hfinishNonzero : finish ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    simp only [UInt32.toNat_zero] at hzeroNat; omega
  iintro ⟨Hcursor, Hfrontier, Hauth, Hretired, Hpages, Hbytes⟩
  imod AllocatorResources_insert heapId history base layout hfresh $$
      [Hauth Hretired] with ⟨Hauth, Hretired, Htoken⟩
  · iframe
  imodintro
  isplitl [Hcursor Hfrontier Hauth Hretired Hpages]
  · unfold BumpHeap
    iframe_pureexact (by
      refine ⟨by omega, hfinishSigned, ?_, ?_, hwfNew, hphysical⟩
      · constructor
        · intro hzero
          exact (hfinishNonzero hzero).elim
        · intro hzero
          simp only [AllocationHistory.allocate] at hzero; omega
      · intro _hnonzero
        rfl)
  · unfold LiveBlock
    iframe_pureexact using [Htoken Hbytes] => ⟨hbytesLength, hnonnull, haligned⟩

/-- Retirement with the agreement fact needed to update pure history. -/
theorem AllocMetaAuth_retire_with_lookup {host : Type}
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout) :
    AllocMetaAuth (host := host) heapId history ∗
      AllocToken heapId allocationId ptr layout ==∗
      AllocMetaAuth heapId (history.retire allocationId ptr layout) ∗
      ghost_map_elem heapId (DFrac.own 1) allocationId
        (retiredMeta ptr layout) ∗
      ⌜get? history.records allocationId =
        some (liveMeta ptr layout)⌝ := by
  iintro ⟨Hauth, Htoken⟩
  ihave %hlookup : ⌜get? history.records allocationId =
      some (liveMeta ptr layout)⌝ $$ [Hauth Htoken]
  · iapply_frame AllocMetaAuth_token_agree
  imod AllocMetaAuth_retire heapId history allocationId ptr layout $$
      [Hauth Htoken] with ⟨Hauth, Hfragment⟩
  · iframe
  imodintro
  iframe_pureexact hlookup

/-- The no-op physical deallocator consumes a complete live block and moves
its bytes and exclusive metadata fragment into allocator-owned retired state. -/
theorem AllocatorResources_retire {host : Type} [WasmHeapGS host]
    (heapId : GName) (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (bytes : List UInt8) :
    AllocMetaAuth (host := host) heapId history ∗
      RetiredBytes heapId history ∗
      LiveBlock heapId allocationId ptr layout bytes ==∗
      AllocMetaAuth heapId (history.retire allocationId ptr layout) ∗
      RetiredBytes heapId (history.retire allocationId ptr layout) := by
  unfold LiveBlock
  iintro ⟨Hauth, Hretired, Htoken, Hbytes, %hfacts⟩
  icombine Hauth Htoken as Hmetadata
  imod AllocMetaAuth_retire_with_lookup heapId history allocationId ptr
      layout $$ Hmetadata with ⟨Hauth, Hfragment, %hlookup⟩
  ihave HretiredNew := RetiredBytes_retire heapId history allocationId ptr
      layout bytes hlookup $$ [Hretired Hfragment Hbytes]
  · iframe_pureexact hfacts.1
  imodintro
  iframe

/-- The complete logical effect of the generated no-op deallocator: cursor
and frontier stay fixed, while the live token and bytes move exactly once into
the retired portion of `BumpHeap`. -/
theorem BumpHeap_retire {host : Type} [WasmHeapGS host]
    [WasmHeapDomainGS host] [WasmMemoryPagesGS host]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (allocationId : Nat) (ptr : UInt32) (layout : AllocLayout)
    (bytes : List UInt8) :
    BumpHeap (host := host) heapId storedCursor frontier history ∗
      LiveBlock heapId allocationId ptr layout bytes ==∗
      BumpHeap heapId storedCursor frontier
        (history.retire allocationId ptr layout) := by
  iintro ⟨Hbump, Hblock⟩
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hblock⟩
  ihave %hlookup : ⌜get? history.records allocationId =
      some (liveMeta ptr layout)⌝ $$ [Hauth Htoken]
  · iapply_frame AllocMetaAuth_token_agree
  have hwfNew := HistoryWellFormed.retire frontier history allocationId ptr
    layout hheap.2.2.2.2.1 hlookup
  imod AllocatorResources_retire heapId history allocationId ptr layout bytes
      $$ [Hauth Hretired Htoken Hbytes] with ⟨Hauth, Hretired⟩
  · unfold LiveBlock
    iframe_pureexact hblock
  imodintro
  unfold BumpHeap
  iframe_pureexact ⟨hheap.1, hheap.2.1, by
      simpa only [AllocationHistory.retire] using hheap.2.2.1,
    hheap.2.2.2.1, hwfNew, hheap.2.2.2.2.2⟩


/-! ## Fresh range claim -/

/-- Claim a fresh physical range while taking a generated constant step.
The claim is a ghost-only update, so the Wasm store and the instruction's
ordinary transition are unchanged.  All reachable allocator bodies share
this boundary between page-capacity reasoning and sparse byte ownership. -/
theorem twp_const_alloc_freshRange_owned
    [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    {P : HeapIProp}
    (frontier ownedPages : Nat) (base : UInt32) (size : Nat)
    (hbase : frontier ≤ base.toNat)
    (hbound : base.toNat + size ≤ ownedPages * 65536)
    (hnowrap : base.toNat + size < UInt32.size)
    (Hwp : ∀ bytes : List UInt8,
      ⌜bytes.length = size⌝ -∗
      heapFrontierOwn (base.toNat + size) -∗
      memoryPagesOwn ownedPages -∗
      Slices.ByteSlice 0 base bytes -∗
      P -∗
      WP (.running
        ⟨⟨params, localValues, .i32 value :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) :
    P -∗
    heapFrontierOwn frontier -∗
    memoryPagesOwn ownedPages -∗
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .const value :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro HP Hfrontier Hpages
  iapply twp_lift_step_no_fork
      (@TerminalView.running_not_val Universal.State ObservableOutcome _ _)
  iintro %store %ns %obs %nt Hσ
  imod stateInterp_alloc_freshRange_owned store ns obs nt
      frontier ownedPages base size hbase hbound hnowrap $$
      [Hσ Hfrontier Hpages] with ⟨Hσ, Hfrontier, Hpages, Hbytes⟩
  · iframe
  let bytes := physicalBytes store.wasm.mem base size
  ihave Hslice : Slices.ByteSlice 0 base bytes $$
      [Hbytes]
  · unfold Slices.ByteSlice
    iframe_pureexact using [Hbytes] => (by simpa [bytes] using hnowrap)
  ihave Hnext := Hwp bytes
  ispecialize Hnext $$ %(by simp [bytes]) Hfrontier Hpages Hslice HP
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr_pureexact (by
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨_, store, [], ⟨rfl, _, rfl, Step.const⟩⟩)
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.const wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplitl_pureexact rfl
  isplitl_pureexact rfl
  isplitl_exact Hσ
  · iexact Hnext

private abbrev readImport : ImportDecl :=
  { module := "stdio", name := "read",
    params := [.i32, .i32], results := [.i32] }

end Project.RustHashMap.Allocator
