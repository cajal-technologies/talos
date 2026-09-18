import Project.RustHashMap.EntryContracts

/-!
# The RawVec grow layer of the hash map program

The five drivers of the hash map program read the input stream one byte at
a time into a `Vec<u8>`.  When the vector is full, the driver calls the
generated `grow_one` function, local `func98` (absolute index 101).  That
function calls `finish_grow`, local `func97` (absolute index 100), which
calls the allocator.  This module states the ownership of a `Vec<u8>` and
the contracts of the two grow functions.  It ports the vector parts of
`Project.Mergesort.Contracts` and `Project.Mergesort.Representations` with
three changes:

* byte ownership is `Wasm.SepLogic.Slices.ByteSlice 0`;
* `finish_grow` takes four operands, because the element size and the
  alignment are constants in this program;
* `grow_one` has no `additional` operand.  The new capacity is
  `max (2 * capacity) 8`, and the capacity lineage `PushVecFacts` replaces
  the mergesort `GeometricVecFacts`.

`Func30Spec` is the contract of local `func30` (absolute index 33), the
empty marker function that `finish_grow` calls before its first allocation.
-/

namespace Project.RustHashMap.VecGrow

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The vector storage -/

/-- The two-word RawVec header: the capacity at `header` and the pointer at
`header + 4`.  The length word at `header + 8` belongs to `VecU8`. -/
def RawVecHeader [WasmHeapGS Universal.State]
    (header capacity ptr : UInt32) : HeapIProp :=
  iprop(pointsTo_u32 0 header capacity ∗
    pointsTo_u32 0 (header + 4) ptr)

/-- The capacity storage of a byte vector.  An empty vector owns no block
and holds the dangling pointer `1`.  A vector with capacity owns one live
block.  The initialized bytes are a prefix of that block. -/
def VecStorage [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) : HeapIProp := iprop%
  (⌜capacity = 0 ∧ ptr = 1 ∧ initialized = []⌝) ∨
  (∃ allocationId : Nat, ∃ allBytes spare : List UInt8,
      ⌜0 < capacity.toNat ∧
        initialized.length ≤ capacity.toNat ∧
        allBytes = initialized ++ spare ∧
        spare.length = capacity.toNat - initialized.length⌝ ∗
      LiveBlock heapId allocationId ptr
        { size := capacity.toNat, alignment := 1 } allBytes)

/-- A complete live block is vector storage when the allocator has copied
the initialized prefix into it. -/
theorem LiveBlock_to_VecStorage [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat)
    (capacity ptr : UInt32) (initialized allBytes : List UInt8)
    (hcapacity : 0 < capacity.toNat)
    (hprefix : allBytes.take initialized.length = initialized) :
    LiveBlock heapId allocationId ptr
        { size := capacity.toNat, alignment := 1 } allBytes ⊢
      VecStorage heapId capacity ptr initialized := by
  unfold LiveBlock
  iintro ⟨Htoken, Hbytes, %hblock⟩
  have htakeLength := congrArg List.length hprefix
  simp only [List.length_take] at htakeLength
  have hinitialized : initialized.length ≤ allBytes.length := by omega
  let spare := allBytes.drop initialized.length
  have hdecompose : allBytes = initialized ++ spare := by
    calc
      allBytes = allBytes.take initialized.length ++
          allBytes.drop initialized.length :=
        (List.take_append_drop initialized.length allBytes).symm
      _ = initialized ++ spare := by rw [hprefix]
  have hspareLength :
      spare.length = capacity.toNat - initialized.length := by
    simp [spare, hblock.1]
  unfold VecStorage
  iright
  iexists allocationId, allBytes, spare
  isplitr_pureexact ⟨hcapacity, by simpa [hblock.1] using hinitialized,
      hdecompose, hspareLength⟩
  · unfold LiveBlock
    iframe_pureexact using [Htoken Hbytes] => hblock

/-- Focus the initialized prefix of a vector with capacity.  The token and
the spare suffix stay framed, so the same storage closes afterwards. -/
theorem VecStorage_initializedFocus [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) (hinitialized : 0 < initialized.length) :
    VecStorage heapId capacity ptr initialized ⊢
      iprop(Slices.ByteSlice 0 ptr initialized ∗
        (Slices.ByteSlice 0 ptr initialized -∗
          VecStorage heapId capacity ptr initialized)) := by
  unfold VecStorage
  iintro (%hempty | Hallocated)
  · rcases hempty with ⟨_hcapacity, _hptr, rfl⟩
    simp at hinitialized
  · icases Hallocated with
      ⟨%allocationId, %allBytes, %spare, %hstorage, Hblock⟩
    isimp only [LiveBlock] at Hblock
    icases Hblock with ⟨Htoken, HallBytes, %hblock⟩
    ihave HallBytes' : Slices.ByteSlice 0 ptr (initialized ++ spare) $$
        [HallBytes]
    · irw_exact [← hstorage.2.2.1] with HallBytes
    icases (Slices.ByteSlice_append 0 ptr initialized spare).mp $$
        HallBytes' with ⟨Hinitialized, Hspare⟩
    isplitl_exact Hinitialized
    · iintro Hinitialized
      ihave HallBytes : Slices.ByteSlice 0 ptr (initialized ++ spare) $$
          [Hinitialized Hspare]
      · iapply_frame (Slices.ByteSlice_append 0 ptr initialized spare).mpr
      iright
      iexists allocationId, initialized ++ spare, spare
      isplitr_pureexact ⟨hstorage.1, hstorage.2.1, rfl, hstorage.2.2.2⟩
      · unfold LiveBlock
        iframe_pureexact using [Htoken HallBytes] => ⟨by
          simp only [List.length_append, hstorage.2.2.2]; omega,
          hblock.2.1, hblock.2.2⟩

/-- Focus the spare bytes that an append fills.  Returning the new bytes
closes the same block with a longer initialized prefix. -/
theorem VecStorage_appendFocus [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized current : List UInt8)
    (hcurrent : 0 < current.length)
    (hfits : current.length ≤ capacity.toNat - initialized.length) :
    VecStorage heapId capacity ptr initialized ⊢
      iprop(∃ oldChunk : List UInt8,
        ⌜oldChunk.length = current.length⌝ ∗
        Slices.ByteSlice 0 (ptr + UInt32.ofNat initialized.length) oldChunk ∗
        (Slices.ByteSlice 0 (ptr + UInt32.ofNat initialized.length) current -∗
          VecStorage heapId capacity ptr (initialized ++ current))) := by
  unfold VecStorage
  iintro (%hempty | Hallocated)
  · rcases hempty with ⟨rfl, _hptr, rfl⟩
    simp only [UInt32.toNat_zero, Nat.zero_sub] at hfits; omega
  · icases Hallocated with
      ⟨%allocationId, %allBytes, %spare, %hstorage, Hblock⟩
    isimp only [LiveBlock] at Hblock
    icases Hblock with ⟨Htoken, HallBytes, %hblock⟩
    let oldChunk := spare.take current.length
    let tail := spare.drop current.length
    have hchunkLength : oldChunk.length = current.length := by
      simp [oldChunk, hstorage.2.2.2, hfits]
    have hdecompose : spare = oldChunk ++ tail := by
      dsimp only [oldChunk, tail]
      exact (List.take_append_drop current.length spare).symm
    have htailLength :
        tail.length = capacity.toNat -
          (initialized.length + current.length) := by
      simp [tail, hstorage.2.2.2]; omega
    ihave HallBytes' : Slices.ByteSlice 0 ptr (initialized ++ spare) $$
        [HallBytes]
    · irw_exact [← hstorage.2.2.1] with HallBytes
    icases (Slices.ByteSlice_append 0 ptr initialized spare).mp $$
        HallBytes' with ⟨Hinitialized, Hspare⟩
    ihave Hspare' : Slices.ByteSlice 0
        (ptr + UInt32.ofNat initialized.length) (oldChunk ++ tail) $$
        [Hspare]
    · irw_exact [← hdecompose] with Hspare
    icases (Slices.ByteSlice_append 0
        (ptr + UInt32.ofNat initialized.length) oldChunk tail).mp $$
        Hspare' with ⟨Hchunk, Htail⟩
    iexists oldChunk
    isplitr_pureexact hchunkLength
    isplitl_exact Hchunk
    iintro Hcurrent
    ihave Htail' : Slices.ByteSlice 0
        ((ptr + UInt32.ofNat initialized.length) +
          UInt32.ofNat current.length) tail $$ [Htail]
    · irw_exact [← hchunkLength] with Htail
    ihave HspareNew : Slices.ByteSlice 0
        (ptr + UInt32.ofNat initialized.length) (current ++ tail) $$
        [Hcurrent Htail']
    · iapply (Slices.ByteSlice_append 0
        (ptr + UInt32.ofNat initialized.length) current tail).mpr
      iframe
    ihave HallBytesNew :
        Slices.ByteSlice 0 ptr (initialized ++ current ++ tail) $$
        [Hinitialized HspareNew]
    · rw [List.append_assoc]
      iapply_frame (Slices.ByteSlice_append 0 ptr initialized
        (current ++ tail)).mpr
    have hnewLength :
        (initialized ++ current ++ tail).length = capacity.toNat := by
      simp only [List.length_append]; omega
    have hnewInitialized :
        (initialized ++ current).length ≤ capacity.toNat := by
      simp only [List.length_append] at hnewLength ⊢; omega
    iright
    iexists allocationId, initialized ++ current ++ tail, tail
    isplitr_pureexact ⟨hstorage.1, hnewInitialized, rfl, by
        simpa only [List.length_append] using htailLength⟩
    · unfold LiveBlock
      iframe_pureexact using [Htoken HallBytesNew] =>
        ⟨hnewLength, hblock.2.1, hblock.2.2⟩

/-- A complete three-word byte vector with its live allocation. -/
def VecU8 [WasmHeapGS Universal.State]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized : List UInt8) : HeapIProp := iprop%
  RawVecHeader header capacity ptr ∗
    pointsTo_u32 0 (header + 8) (UInt32.ofNat initialized.length) ∗
    VecStorage heapId capacity ptr initialized

/-- The bytes of the three vector words in a stack frame. -/
def vecHeaderBytes (capacity ptr : UInt32)
    (initialized : List UInt8) : List UInt8 :=
  WordCodec.u32le.serialize [capacity, ptr, UInt32.ofNat initialized.length]

@[simp] theorem vecHeaderBytes_length
    (capacity ptr : UInt32) (initialized : List UInt8) :
    (vecHeaderBytes capacity ptr initialized).length = 12 := by
  unfold vecHeaderBytes
  rw [WordCodec.u32le_serialize_length]
  rfl

/-- The deliberately transparent view of a vector. -/
theorem VecU8_open [WasmHeapGS Universal.State]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized : List UInt8) :
    VecU8 heapId header capacity ptr initialized ⊣⊢
      iprop(RawVecHeader header capacity ptr ∗
        pointsTo_u32 0 (header + 8) (UInt32.ofNat initialized.length) ∗
        VecStorage heapId capacity ptr initialized) :=
  .rfl

/-- The three vector words as raw frame bytes, beside the storage.  A driver
uses this split when it frees the storage and then restores the raw frame. -/
theorem VecU8_as_headerBytes_storage [WasmHeapGS Universal.State]
    (heapId : GName) (header capacity ptr : UInt32)
    (initialized : List UInt8)
    (hheader : header.toNat + 12 < UInt32.size) :
    VecU8 heapId header capacity ptr initialized ⊣⊢
      iprop(Slices.ByteSlice 0 header
          (vecHeaderBytes capacity ptr initialized) ∗
        VecStorage heapId capacity ptr initialized) := by
  have haddress : (header + 4) + 4 = header + 8 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  constructor
  · iintro Hvec
    isimp only [VecU8, RawVecHeader] at Hvec
    icases Hvec with
      ⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩
    ihave Hlength' : pointsTo_u32 0 ((header + 4) + 4)
        (UInt32.ofNat initialized.length) $$ [Hlength]
    · irw_exact [haddress] with Hlength
    ihave Harray : arrayAt 0 header
        [capacity, ptr, UInt32.ofNat initialized.length] $$
        [Hcapacity Hpointer Hlength']
    · isimp only [arrayAt]
      iframe
    ihave Hbytes : Slices.WordCells 0 header
        [capacity, ptr, UInt32.ofNat initialized.length] $$ [Harray]
    · iapply (Slices.arrayAt_eq_wordCells 0 header
          [capacity, ptr, UInt32.ofNat initialized.length]).mp
      iexact Harray
    isplitl [Hbytes]
    · unfold Slices.ByteSlice
      isplitl_pureexact (by
        rw [vecHeaderBytes_length]; exact hheader)
      unfold vecHeaderBytes
      iexact Hbytes
    · iexact Hstorage
  · iintro ⟨Hheader, Hstorage⟩
    isimp only [Slices.ByteSlice, vecHeaderBytes] at Hheader
    icases Hheader with ⟨%_hnowrap, Hbytes⟩
    ihave Harray : arrayAt 0 header
        [capacity, ptr, UInt32.ofNat initialized.length] $$ [Hbytes]
    · iapply (Slices.arrayAt_eq_wordCells 0 header
          [capacity, ptr, UInt32.ofNat initialized.length]).mpr
      iexact Hbytes
    isimp only [arrayAt] at Harray
    icases Harray with ⟨Hcapacity, Hpointer, Hlength⟩
    icases Hlength with ⟨Hlength, _Hemp⟩
    ihave Hlength' : pointsTo_u32 0 (header + 8)
        (UInt32.ofNat initialized.length) $$ [Hlength]
    · irw_exact [← haddress] with Hlength
    unfold VecU8 RawVecHeader
    iframe

/-! ## The sixteen-byte frame of `grow_one` -/

/-- The sixteen bytes that `grow_one` takes below the caller's frame. -/
def StackReserve [WasmHeapGS Universal.State]
    (low : UInt32) (bytes : List UInt8) : HeapIProp :=
  iprop(⌜bytes.length = 16⌝ ∗ Slices.ByteSlice 0 low bytes)

/-- The four-byte head and the twelve-byte result slot of the reserve. -/
theorem StackReserve_split [WasmHeapGS Universal.State]
    (low : UInt32) (bytes : List UInt8) :
    StackReserve low bytes ⊣⊢
      iprop(∃ headBytes : List UInt8, ∃ growBefore : List UInt8,
        ⌜bytes = headBytes ++ growBefore ∧
          headBytes.length = 4 ∧ growBefore.length = 12⌝ ∗
        Slices.ByteSlice 0 low headBytes ∗
        Slices.ByteSlice 0 (low + UInt32.ofNat headBytes.length) growBefore) := by
  constructor
  · iintro Hreserve
    isimp only [StackReserve] at Hreserve
    icases Hreserve with ⟨%hlength, Hbytes⟩
    let headBytes := bytes.take 4
    let growBefore := bytes.drop 4
    have hdecompose : bytes = headBytes ++ growBefore := by
      dsimp only [headBytes, growBefore]
      exact (List.take_append_drop 4 bytes).symm
    have hheadLength : headBytes.length = 4 := by
      simp [headBytes, hlength]
    have hgrowLength : growBefore.length = 12 := by
      simp [growBefore, hlength]
    ihave Hsplit : Slices.ByteSlice 0 low (headBytes ++ growBefore) $$ [Hbytes]
    · irw_exact [← hdecompose] with Hbytes
    icases (Slices.ByteSlice_append 0 low headBytes growBefore).mp $$
        Hsplit with ⟨Hhead, Hgrow⟩
    iexists headBytes, growBefore
    isplitr_pureexact ⟨hdecompose, hheadLength, hgrowLength⟩
    · iframe
  · iintro ⟨%headBytes, %growBefore, %hfacts, Hhead, Hgrow⟩
    unfold StackReserve
    isplitl_pureexact (by
      rw [hfacts.1, List.length_append, hfacts.2.1, hfacts.2.2])
    rw [hfacts.1]
    iapply_frame (Slices.ByteSlice_append 0 low headBytes growBefore).mpr

/-! ## The grow witnesses -/

/-- The storage a grow starts from: no block, or one live block. -/
inductive GrowSource where
  | empty
  | allocated (allocationId : Nat) (allBytes spare : List UInt8)

/-- The ownership of a grow source. -/
def GrowSourceOwn [WasmHeapGS Universal.State]
    (heapId : GName) (oldCapacity oldPtr : UInt32)
    (initialized : List UInt8) : GrowSource → HeapIProp
  | .empty => iprop(⌜oldCapacity = 0 ∧ oldPtr = 1 ∧ initialized = []⌝)
  | .allocated allocationId allBytes spare => iprop(
      ⌜0 < oldCapacity.toNat ∧
        initialized.length ≤ oldCapacity.toNat ∧
        allBytes = initialized ++ spare ∧
        spare.length = oldCapacity.toNat - initialized.length⌝ ∗
      LiveBlock heapId allocationId oldPtr
        { size := oldCapacity.toNat, alignment := 1 } allBytes)

private theorem GrowSourceOwn_to_VecStorage [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) (source : GrowSource) :
    GrowSourceOwn heapId capacity ptr initialized source ⊢
      VecStorage heapId capacity ptr initialized := by
  cases source with
  | empty =>
      unfold GrowSourceOwn VecStorage
      iintro Hsource
      ileft
      iexact Hsource
  | allocated allocationId allBytes spare =>
      unfold GrowSourceOwn VecStorage
      iintro Hsource
      iright
      iexists allocationId, allBytes, spare
      iexact Hsource

/-- Vector storage is a grow source with the allocation details explicit. -/
theorem VecStorage_as_growSource [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) :
    VecStorage heapId capacity ptr initialized ⊣⊢
      iprop(∃ source : GrowSource,
        GrowSourceOwn heapId capacity ptr initialized source) := by
  constructor
  · iintro Hstorage
    isimp only [VecStorage] at Hstorage
    icases Hstorage with (%hempty | Hallocated)
    · iexists GrowSource.empty
      isimp only [GrowSourceOwn]
      ipureexact hempty
    · icases Hallocated with
        ⟨%allocationId, %allBytes, %spare, Hfacts, Hblock⟩
      iexists GrowSource.allocated allocationId allBytes spare
      isimp only [GrowSourceOwn]
      iframe
  · iintro ⟨%source, Hsource⟩
    iapply_exact GrowSourceOwn_to_VecStorage heapId capacity ptr initialized
      source with Hsource

/-- The allocation history after a grow from `source`. -/
def growHistory (history : AllocationHistory) (source : GrowSource)
    (oldCapacity oldPtr newPtr : UInt32) (newLayout : AllocLayout) :
    AllocationHistory :=
  match source with
  | .empty => history.allocate newPtr newLayout
  | .allocated allocationId _ _ =>
      history.reallocate allocationId oldPtr
        { size := oldCapacity.toNat, alignment := 1 } newPtr newLayout

/-- The old block is a prefix of the new block after a grow. -/
def growCopied (source : GrowSource) (oldCapacity : UInt32)
    (newBytes : List UInt8) : Prop :=
  match source with
  | .empty => True
  | .allocated _ allBytes _ =>
      newBytes.take oldCapacity.toNat = allBytes

/-- The twelve result bytes of a successful `finish_grow`: the tag `0`, the
new pointer, and the new capacity. -/
def growResultBytes (pointer capacity : UInt32) : List UInt8 :=
  WordCodec.u32le.serialize [0, pointer, capacity]

/-- The reserve after a normal `grow_one`.  The function never touches the
first four bytes.  `finish_grow` overwrites the other twelve. -/
def reserveSuccessShadow (shadow : List UInt8)
    (pointer capacity : UInt32) : List UInt8 :=
  shadow.take 4 ++ growResultBytes pointer capacity

theorem reserveSuccessShadow_length (shadow : List UInt8)
    (pointer capacity : UInt32) (hlength : shadow.length = 16) :
    (reserveSuccessShadow shadow pointer capacity).length = 16 := by
  unfold reserveSuccessShadow growResultBytes
  rw [List.length_append, List.length_take, WordCodec.u32le_serialize_length]
  simp [hlength]

/-! ## The capacity lineage -/

/-- The capacity that `grow_one` selects. -/
def pushCapacity (capacity : Nat) : Nat :=
  max (2 * capacity) 8

/-- The capacity lineage of the input vector.  The vector is empty with the
dangling pointer `1`, or it holds a power of two of at least eight bytes.
The lower bound on the pointer says that the earlier blocks of the doubling
chain sit below the block.  The bound on the exponent follows from the
signed frontier limit of the allocator. -/
def PushVecFacts (capacity ptr : UInt32) (frontier : Nat) : Prop :=
  (capacity = 0 ∧ ptr = 1) ∨
  (∃ exponent : Nat, 3 ≤ exponent ∧ exponent ≤ 29 ∧
    capacity.toNat = 2 ^ exponent ∧
    heapBase.toNat + 2 ^ exponent ≤ ptr.toNat + 8 ∧
    ptr.toNat + 2 ^ exponent ≤ frontier)

theorem PushVecFacts.capacity_le {capacity ptr : UInt32} {frontier : Nat}
    (h : PushVecFacts capacity ptr frontier) :
    capacity.toNat ≤ 536870912 := by
  rcases h with ⟨hcapacity, _⟩ | ⟨exponent, _, hupper, hcapacity, _, _⟩
  · rw [hcapacity]; decide
  · rw [hcapacity]
    calc 2 ^ exponent ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hupper
      _ = 536870912 := by norm_num

/-- The selected layout is valid, and the new capacity is larger. -/
theorem PushVecFacts.layout {capacity ptr : UInt32} {frontier : Nat}
    (h : PushVecFacts capacity ptr frontier) :
    2 * capacity.toNat < UInt32.size ∧
      pushCapacity capacity.toNat < UInt32.size ∧
      8 ≤ pushCapacity capacity.toNat ∧
      capacity.toNat < pushCapacity capacity.toNat ∧
      ({ size := pushCapacity capacity.toNat, alignment := 1 } :
        AllocLayout).Valid := by
  have hle := h.capacity_le
  have hsize : UInt32.size = 4294967296 := rfl
  have hpush : pushCapacity capacity.toNat ≤ 1073741824 := by
    unfold pushCapacity
    exact max_le (by omega) (by norm_num)
  have hpushLower : 8 ≤ pushCapacity capacity.toNat := le_max_right _ _
  have hpushDouble : 2 * capacity.toNat ≤ pushCapacity capacity.toNat :=
    le_max_left _ _
  refine ⟨by omega, by omega, hpushLower, by omega, ?_⟩
  unfold AllocLayout.Valid
  dsimp only
  exact ⟨by omega, by omega, ⟨0, by norm_num⟩, by norm_num, by omega,
    by omega, by norm_num [hsize]⟩

/-- A successful allocation of the selected layout keeps the lineage. -/
theorem PushVecFacts.growSuccess
    {capacity ptr : UInt32} {frontier : Nat}
    (newPtr finish : UInt32)
    (h : PushVecFacts capacity ptr frontier)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hclassify : classifyBump frontier
      { size := pushCapacity capacity.toNat, alignment := 1 } =
        .success newPtr finish) :
    PushVecFacts (UInt32.ofNat (pushCapacity capacity.toNat)) newPtr
      finish.toNat := by
  obtain ⟨_, _, hnewPtr, _, hsigned, hfinish⟩ :=
    classifyBump_success_align1 frontier (pushCapacity capacity.toNat)
      newPtr finish hclassify
  have hheapBase : heapBase.toNat = 1049568 := by decide
  rcases h with ⟨hcapacity, _⟩ | ⟨exponent, hlower, _, hcapacity, hlow, hhigh⟩
  · have hcapacityNat : capacity.toNat = 0 := by rw [hcapacity]; rfl
    have hpush : pushCapacity capacity.toNat = 8 := by
      rw [hcapacityNat]; rfl
    rw [hpush] at hsigned hfinish ⊢
    right
    refine ⟨3, Nat.le_refl 3, by norm_num, by decide, ?_, ?_⟩
    · rw [hnewPtr]; norm_num; omega
    · rw [hnewPtr, hfinish]; norm_num
  · have hpow8 : 8 ≤ 2 ^ exponent := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ exponent := Nat.pow_le_pow_right (by decide) hlower
    have hsucc : 2 ^ (exponent + 1) = 2 * 2 ^ exponent := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hsucc2 : 2 ^ (exponent + 2) = 2 * 2 ^ (exponent + 1) := by
      rw [Nat.pow_succ 2 (exponent + 1), Nat.mul_comm]
    have hpush : pushCapacity capacity.toNat = 2 ^ (exponent + 1) := by
      unfold pushCapacity
      rw [hcapacity, hsucc]
      exact max_eq_left (by omega)
    rw [hpush] at hsigned hfinish ⊢
    have hbound : exponent + 1 ≤ 29 := by
      by_contra hcontra
      have h31 : 2147483648 ≤ 2 ^ (exponent + 2) := by
        calc 2147483648 = 2 ^ 31 := by norm_num
          _ ≤ 2 ^ (exponent + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      generalize 2 ^ exponent = p at *
      generalize 2 ^ (exponent + 1) = q at *
      generalize 2 ^ (exponent + 2) = r at *
      omega
    have hword : 2 ^ (exponent + 1) < UInt32.size := by
      calc 2 ^ (exponent + 1) ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hbound
        _ < UInt32.size := by decide
    right
    refine ⟨exponent + 1, by omega, hbound,
      UInt32.toNat_ofNat_of_lt' hword, ?_, ?_⟩
    · rw [hnewPtr, hsucc]
      generalize 2 ^ exponent = p at *
      omega
    · rw [hnewPtr, hfinish]

/-! ## The contract of `finish_grow` -/

/-- The result continuation of `finish_grow`.  Arithmetic success carries a
normal arm and an OOM arm, because the modular proof does not own the
physical memory cap.  Arithmetic OOM carries only the terminal arm.  Both
OOM arms hand back the resources of the call, with the OOM marker set. -/
def FinishGrowContinuation [WasmSmallStepGS hlc Universal.State]
    (result oldCapacity oldPtr newCapacity : UInt32)
    (source : GrowSource) (initialized growBefore : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let newLayout : AllocLayout :=
    { size := newCapacity.toNat, alignment := 1 }
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ newBytes : List UInt8,
          RuntimeContext -∗
          Slices.ByteSlice 0 result (growResultBytes newPtr newCapacity) -∗
          BumpHeap heapId finish finish.toNat
            (growHistory history source oldCapacity oldPtr newPtr newLayout) -∗
          LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
          ⌜growCopied source oldCapacity newBytes ∧
            newBytes.take initialized.length = initialized⌝ -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∧
        (Slices.ByteSlice 0 result growBefore -∗
          GrowSourceOwn heapId oldCapacity oldPtr initialized source -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      Slices.ByteSlice 0 result growBefore -∗
      GrowSourceOwn heapId oldCapacity oldPtr initialized source -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func97`, absolute index 100, the generated `finish_grow`.  The
operands are the result slot, the old capacity, the old pointer, and the
new capacity, in machine order.  The valid-input specialization has only a
normal return or the OOM outcome. -/
def Func97Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (result oldCapacity oldPtr newCapacity : UInt32)
    (source : GrowSource) (initialized growBefore : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    let newLayout : AllocLayout :=
      { size := newCapacity.toNat, alignment := 1 }
    CallContract 100
      [.i32 newCapacity, .i32 oldPtr, .i32 oldCapacity, .i32 result]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Slices.ByteSlice 0 result growBefore ∗
        GrowSourceOwn heapId oldCapacity oldPtr initialized source ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜growBefore.length = 12 ∧
          8 ≤ newCapacity.toNat ∧
          oldCapacity.toNat < newCapacity.toNat ∧
          newLayout.Valid⌝ ∗
        FinishGrowContinuation result oldCapacity oldPtr newCapacity source
          initialized growBefore heapId storedCursor frontier history input
          output raised callerLocals stack code arity remainder controls calls
          s E Φ)

/-! ## The contract of `grow_one` -/

/-- The result continuation of `grow_one`.  The frame of the function is
the sixteen bytes below the stack pointer `sp`.  A normal return restores
`sp`, and the vector holds the new capacity and pointer.  The final history
is hidden, because no driver depends on it. -/
def GrowOneContinuation [WasmSmallStepGS hlc Universal.State]
    (sp header capacity ptr : UInt32) (initialized shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let newCapacityNat := pushCapacity capacity.toNat
  let newCapacity := UInt32.ofNat newCapacityNat
  let newLayout : AllocLayout :=
    { size := newCapacityNat, alignment := 1 }
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ finalHistory : AllocationHistory,
          RuntimeContext -∗
          StackPointer sp -∗
          StackReserve (sp - 16)
            (reserveSuccessShadow shadow newPtr newCapacity) -∗
          VecU8 heapId header newCapacity newPtr initialized -∗
          BumpHeap heapId finish finish.toNat finalHistory -∗
          ⌜PushVecFacts newCapacity newPtr finish.toNat⌝ -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∧
        (StackPointer (sp - 16) -∗
          StackReserve (sp - 16) shadow -∗
          VecU8 heapId header capacity ptr initialized -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      StackPointer (sp - 16) -∗
      StackReserve (sp - 16) shadow -∗
      VecU8 heapId header capacity ptr initialized -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams input output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Local `func98`, absolute index 101, the generated `grow_one`.  The one
operand is the address of the vector header.  The capacity lineage
`PushVecFacts` excludes the generated capacity-overflow edge. -/
def Func98Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (header sp capacity ptr : UInt32) (initialized shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 101 [.i32 header]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackReserve (sp - 16) shadow ∗
        VecU8 heapId header capacity ptr initialized ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜16 ≤ sp.toNat ∧ header.toNat + 12 < UInt32.size ∧
          PushVecFacts capacity ptr frontier⌝ ∗
        GrowOneContinuation sp header capacity ptr initialized shadow heapId
          storedCursor frontier history input output raised callerLocals
          stack code arity remainder controls calls s E Φ)

/-! ## The marker function -/

/-- Local `func30`, absolute index 33, is the empty marker function that
`finish_grow` calls before its first allocation. -/
def Func30Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 33 [] callerLocals stack code arity remainder controls calls
      s E Φ iprop(RuntimeContext ∗
        (RuntimeContext -∗ ResumeWP [] callerLocals stack code arity remainder
          controls calls s E Φ))

end Project.RustHashMap.VecGrow
