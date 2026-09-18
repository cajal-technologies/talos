import Project.RustHashMap.DriverTail
import Project.RustHashMap.EntriesContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.LookupPures
import Project.RustHashMap.Allocator

/-!
# The helpers that the remove and insert tail proofs share

`Project.RustHashMap.RemoveTailProof` and
`Project.RustHashMap.InsertTailProof` state the same eight pure helpers.
This module holds one public copy of each, so that neither tail repeats
the other.  No lemma here carries program control: each one is a shape
that a template module states at one address or one depth and that a
tail needs at another.

`Project.RustHashMap.ContainsKeyTailProof` keeps its own public
`ByteSlice_single`, `ByteSlice_five_words` and `StackBelow_of_reserve_at`.
Those three are not copies of the eight below.
-/

namespace Project.RustHashMap.TailShared

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Allocator
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.EntriesContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open Project.RustHashMap.DriverTail

/-- The address of a shallower region inside a deeper one.  The shallow
depth is a general `Nat`, because the callee depth of a tail is not a
numeral. -/
theorem stack_addr (sp : UInt32) (deep shallow : Nat)
    (hle : shallow ≤ deep) :
    sp - UInt32.ofNat deep + UInt32.ofNat (deep - shallow)
      = sp - UInt32.ofNat shallow := by
  obtain ⟨e, rfl⟩ : ∃ e, deep = shallow + e := ⟨deep - shallow, by omega⟩
  rw [Nat.add_sub_cancel_left, UInt32.ofNat_add,
    ← HashMap.Table.sub_sub_addr, UInt32.sub_add_cancel]

/-- Hand a callee the top `shallow` bytes of the region and take them
back afterwards.  The kept part comes back unchanged, so the wand
rebuilds the whole region whatever the callee left in its own part. -/
theorem StackBelow_reshape [WasmHeapGS Universal.State]
    (sp : UInt32) (deep shallow : Nat) (bytes : List UInt8)
    (hle : shallow ≤ deep) :
    StackBelow sp deep bytes ⊢
      iprop(∃ low : List UInt8, StackBelow sp shallow low ∗
        (∀ below' : List UInt8, StackBelow sp shallow below' -∗
          ∃ b : List UInt8, StackBelow sp deep b)) := by
  iintro Hbelow
  ihave ⟨Hbelow, %hlen⟩ := StackBelow_length sp deep bytes $$ Hbelow
  ihave ⟨Hlow, Hhigh⟩ :=
    StackBelow_split sp deep shallow bytes hle
      (stack_addr sp deep shallow hle) $$ Hbelow
  iexists (bytes.drop (deep - shallow))
  isplitl [Hhigh]
  · iexact Hhigh
  · iintro %below' Hbelow'
    iexists (bytes.take (deep - shallow) ++ below')
    iapply StackBelow_join sp deep shallow (bytes.take (deep - shallow))
      below' (by rw [List.length_take, hlen]; omega) hle
      (stack_addr sp deep shallow hle)
    iframe Hlow Hbelow'

/-- Three cells back as a twelve-byte header.  `sorted_entries` takes
twelve bytes as its output slot. -/
theorem ByteSlice_of_three_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 : UInt32)
    (hnowrap : ptr.toNat + 12 < UInt32.size) :
    iprop(pointsTo_u32 (α := Universal.State) 0 ptr w0 ∗
        pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 4 + 4) w2) ⊢
      Slices.ByteSlice 0 ptr (WordCodec.u32le.serialize [w0, w1, w2]) := by
  iintro ⟨H0, H1, H2⟩
  isimp only [Slices.ByteSlice]
  isplitl_pureexact (by
    rw [show (WordCodec.u32le.serialize [w0, w1, w2]).length = 12 from rfl]
    exact hnowrap)
  iapply (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
    [w0, w1, w2]).mp
  isimp only [arrayAt]
  iframe H0 H1 H2

/-- Four cells back as a sixteen-byte slot.  The two error arms of the
insert tail rebuild the slot that absolute `func 55` wrote. -/
theorem ByteSlice_of_four_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 w3 : UInt32)
    (hnowrap : ptr.toNat + 16 < UInt32.size) :
    iprop(pointsTo_u32 (α := Universal.State) 0 ptr w0 ∗
        pointsTo_u32 0 (ptr + 4) w1 ∗ pointsTo_u32 0 (ptr + 4 + 4) w2 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4) w3) ⊢
      Slices.ByteSlice 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) := by
  iintro ⟨H0, H1, H2, H3⟩
  isimp only [Slices.ByteSlice]
  isplitl_pureexact (by
    rw [show (WordCodec.u32le.serialize [w0, w1, w2, w3]).length = 16
      from rfl]
    exact hnowrap)
  iapply (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
    [w0, w1, w2, w3]).mp
  isimp only [arrayAt]
  iframe H0 H1 H2 H3

/-- Five cells back as a twenty-byte slot.  The accept arm of the remove
tail reads four of the five words and then hands the same bytes to
`collect_entries`, so the proof needs the direction that
`Project.RustHashMap.ContainsKeyTailProof.ByteSlice_five_words` does not
give. -/
theorem ByteSlice_of_five_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 w3 w4 : UInt32)
    (hnowrap : ptr.toNat + 20 < UInt32.size) :
    iprop(pointsTo_u32 (α := Universal.State) 0 ptr w0 ∗
        pointsTo_u32 0 (ptr + 4) w1 ∗ pointsTo_u32 0 (ptr + 4 + 4) w2 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4) w3 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4 + 4) w4) ⊢
      Slices.ByteSlice 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3, w4]) := by
  iintro ⟨H0, H1, H2, H3, H4⟩
  isimp only [Slices.ByteSlice]
  isplitl_pureexact (by
    rw [show (WordCodec.u32le.serialize [w0, w1, w2, w3, w4]).length = 20
      from rfl]
    exact hnowrap)
  iapply (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
    [w0, w1, w2, w3, w4]).mp
  isimp only [arrayAt]
  iframe H0 H1 H2 H3 H4

/-- The vector storage reports that the initialized bytes fit in the
capacity.  `Project.RustHashMap.RemovePures.acceptedEntries_le_max` asks
for that bound. -/
theorem VecStorage_fits [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32) (initialized : List UInt8) :
    VecStorage heapId capacity ptr initialized ⊢
      iprop(VecStorage heapId capacity ptr initialized ∗
        ⌜initialized.length ≤ capacity.toNat⌝) := by
  iintro Hstorage
  isimp only [VecStorage] at Hstorage
  icases Hstorage with (%hempty | ⟨%allocationId, %allBytes, %spare,
    %hfacts, Hblock⟩)
  · isplitl []
    · isimp only [VecStorage]
      ileft
      ipureexact hempty
    · ipureexact (by rw [hempty.2.2]; exact Nat.zero_le _)
  · isplitl [Hblock]
    · isimp only [VecStorage]
      iright
      iexists allocationId, allBytes, spare
      isplitl_pureexact hfacts
      · iexact Hblock
    · ipureexact hfacts.2.1

/-- The map value as four `u64` cells with the header words named, and
the wand that puts it back at another address.  This is
`Project.RustHashMap.LookupPures.HashMapAt_move` with the two header
words exposed, because a tail reads the twelve bytes that stay at the
source after the move. -/
theorem HashMapAt_move_words [WasmHeapGS Universal.State]
    (src dst : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) :
    HashMap.Table.HashMapAt (α := Universal.State) 0 src k0 k1 t ⊢
      iprop(∃ ctrl : UInt32, ∃ mask : UInt32, ∃ growthLeft : UInt32,
        ∃ items : UInt32,
        pointsTo_u64 0 src (wordPair ctrl mask) ∗
        pointsTo_u64 0 (src + 8) (wordPair growthLeft items) ∗
        pointsTo_u64 0 (src + 16) k0 ∗ pointsTo_u64 0 (src + 24) k1 ∗
        (pointsTo_u64 0 dst (wordPair ctrl mask) -∗
          pointsTo_u64 0 (dst + 8) (wordPair growthLeft items) -∗
          pointsTo_u64 0 (dst + 16) k0 -∗
          pointsTo_u64 0 (dst + 24) k1 -∗
          HashMap.Table.HashMapAt 0 dst k0 k1 t)) := by
  iintro Hmap
  isimp only [HashMap.Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  ihave ⟨%ctrl, %mask, %growthLeft, %items, Hheader, Hback⟩ :=
    TableAt_relocate 0 src dst t $$ Htable
  ihave Hcells :=
    (tableHeader_as_u64 0 src ctrl mask growthLeft items).mp $$ Hheader
  icases Hcells with ⟨Hc0, Hc1⟩
  iexists ctrl, mask, growthLeft, items
  iframe Hc0 Hc1 Hk0 Hk1
  iintro Hd0 Hd1 Hdk0 Hdk1
  ihave Hheader :
      HashMap.Table.tableHeader 0 dst ctrl mask growthLeft items
      $$ [Hd0 Hd1]
  · iapply (tableHeader_as_u64 0 dst ctrl mask growthLeft items).mpr
    iframe Hd0 Hd1
  ihave Htable := Hback $$ Hheader
  isimp only [HashMap.Table.HashMapAt]
  iframe Htable Hdk0 Hdk1

/-- The bytes that the reply writer reads.  An empty pair vector owns no
block and reports the dangling pointer 4.  The spare bytes of a full
block stay with the block and the reply never reads them. -/
theorem PairVecAt_bytes [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId capacity : Nat) (ptr : UInt32)
    (pairs : List (UInt32 × UInt32)) :
    PairVecAt heapId allocationId capacity ptr pairs ⊢
      iprop(Slices.ByteSlice 0 ptr (HashMap.Table.pairBytes pairs) ∗
        ⌜ptr.toNat + 8 * pairs.length < UInt32.size⌝) := by
  unfold PairVecAt
  by_cases hcap : capacity = 0
  · rw [if_pos hcap]
    iintro %hfacts
    obtain ⟨hptr, hpairs⟩ := hfacts
    subst hptr
    subst hpairs
    isimp only [HashMap.Table.pairBytes_nil, List.length_nil,
      Nat.mul_zero, Nat.add_zero]
    isplitl []
    · isimp only [Slices.ByteSlice, List.length_nil]
      isplitl_pureexact (by decide)
      · iapply (pointsToBytes_nil 0 (4 : UInt32)).mpr
        itrivial
    · ipureexact (by decide)
  · rw [if_neg hcap]
    iintro ⟨%pad, %hlen, Hblock⟩
    iunfold LiveBlock at Hblock
    icases Hblock with ⟨_Htoken, Hbytes, %_hfields⟩
    ihave ⟨Hlow, _Hhigh⟩ :=
      (Slices.ByteSlice_append 0 ptr (HashMap.Table.pairBytes pairs)
        pad).mp $$ Hbytes
    isimp only [Slices.ByteSlice] at Hlow
    icases Hlow with ⟨%hbound, Hlow⟩
    isplitl [Hlow]
    · isimp only [Slices.ByteSlice]
      isplitl_pureexact hbound
      · iexact Hlow
    · ipureexact (by
        rw [← HashMap.Table.pairBytes_length pairs]
        exact hbound)

end Project.RustHashMap.TailShared
