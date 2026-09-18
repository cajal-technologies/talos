import Project.RustHashMap.EntriesContracts
import Project.RustHashMap.Func10Proof
import Project.RustHashMap.Func55Proof
import Project.RustHashMap.Func57Proof
import Project.RustHashMap.Func30Proof
import Project.RustHashMap.ImportProofs
import Project.RustHashMap.FrameCells

/-!
# Proof of the reply writer, absolute `func 8`

This file proves local `func5`, absolute `func 8`, against
`Project.RustHashMap.EntriesContracts.Func5Spec`.  The body is WAT lines
1300 to 1491 of `programs/rust/build/rust_hash_map/program.wat`.

The body allocates a 1024-byte buffer, writes the borsh form of an
`Option<u32>` answer, then the entry count, then the key word and the
value word of every entry, writes the buffer to the output stream, and
frees it.

## The loop

The loop at WAT 1370 to 1457 writes one entry per turn.  Its index `n`
counts the entries already written, and the measure is
`pairs.length - n`.  The buffer holds

```
Borsh.option Borsh.u32 o ++ Borsh.u32 (ofNat pairs.length) ++
  pairBytes (pairs.take n)
```

and the rest of the block is spare.  Two grow sites sit in the turn, one
in front of each word store, at WAT 1395 and WAT 1431.  Both go through
`Project.RustHashMap.GrowContract.Func10Spec`, which
`Project.RustHashMap.Func10Proof.func10_correct` proves.

## Why the capacity cannot overflow

`Func10Spec` asks for `growCapacity cap (len + 4) 1 <= 2147483647`.  The
new capacity is twice the old one, so the fact to carry is a bound on the
old one.  `CapFits` below is that fact:

```
heapBase + 2 * cap <= frontier + 1024
```

It holds after the first allocation, because that block is 1024 bytes and
the allocator hands it out at the frontier.  It survives a grow, because
the new block takes `2 * cap` more bytes of the heap and the bump
allocator never hands a byte out twice.  `BumpHeap` bounds the frontier by
2147483648, so the fact bounds `2 * cap` by 2146435104, and the arm needs
2147483648.  The fact is about the allocator alone, so the entry count
enters nowhere.

## The dead arm

Row X-F8-NULL of `Analysis/scope-and-exclusions.md` is the `call 99` and
`unreachable` at WAT 1471 to 1474, behind the guard at WAT 1317 to 1319.
`Func55Spec` returns a live block, and a live block never starts at
address zero, so the guard is false.

The guard at WAT 1466 to 1468 tests the capacity after the write.  The
capacity is 1024 or more on every path, so that arm is dead as well and
every path reaches the free at WAT 1482 to 1485.
-/

namespace Project.RustHashMap.Func5Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.PairGrow
open Project.RustHashMap.GrowContract
open Project.RustHashMap.EntriesContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The shape of the compiled body -/

/-- The `Some` arm of the option, WAT 1328 to 1342. -/
@[reducible] private def optBlock : Program :=
  [.localGet 0, .load32 0, .const 1, .ne, .br_if 0, .localGet 3,
    .localGet 0, .load32 4, .store32 1, .const 5, .localSet 2, .const 1,
    .localSet 4]

/-- The grow in front of the key store, WAT 1379 to 1405. -/
@[reducible] private def growKey : Program :=
  [.localGet 1, .load32 4, .localTee 4, .localGet 2, .sub, .const 3,
    .gtU, .br_if 0, .localGet 1, .const 4, .add, .localGet 2, .const 4,
    .const 1, .const 1, .call 13, .localGet 1, .load32 8, .localSet 3,
    .localGet 1, .load32 4, .localSet 4, .localGet 1, .load32 12,
    .localSet 2]

/-- The grow in front of the value store, WAT 1417 to 1438. -/
@[reducible] private def growValue : Program :=
  [.localGet 4, .localGet 2, .sub, .const 3, .gtU, .br_if 0,
    .localGet 1, .const 4, .add, .localGet 2, .const 4, .const 1,
    .const 1, .call 13, .localGet 1, .load32 8, .localSet 3, .localGet 1,
    .load32 12, .localSet 2]

/-- One turn of the entry loop, WAT 1371 to 1456. -/
@[reducible] private def loopBody : Program :=
  [.localGet 0, .const 4, .add, .load32 0, .localSet 6, .localGet 0,
    .load32 0, .localSet 7, .block 0 0 growKey, .localGet 3, .localGet 2,
    .add, .localGet 7, .store32 0, .localGet 1, .localGet 2, .const 4,
    .add, .localTee 2, .store32 12, .block 0 0 growValue, .localGet 3,
    .localGet 2, .add, .localGet 6, .store32 0, .localGet 1, .localGet 2,
    .const 4, .add, .localTee 2, .store32 12, .localGet 0, .const 8,
    .add, .localTee 0, .localGet 5, .ne, .br_if 0]

/-- The tail of the main arm, WAT 1458 to 1469. -/
@[reducible] private def mainTail : Program :=
  [.localGet 1, .load32 4, .localSet 0, .localGet 1, .load32 8,
    .localTee 3, .localGet 2, .call 64, .localGet 0, .eqz, .br_if 3,
    .br 2]

/-- The allocation, the option, the count and the loop, WAT 1314 to
1469. -/
@[reducible] private def block4 : Program :=
  .const 1024 :: .const 1 :: .call 58 :: .localTee 3 :: .eqz ::
    .br_if 0 :: .localGet 1 :: .localGet 3 :: .store32 8 :: .localGet 1 ::
    .const 1024 :: .store32 4 :: .const 0 :: .localSet 4 ::
    .block 0 0 optBlock :: .localGet 3 :: .localGet 4 :: .store8 0 ::
    .localGet 3 :: .localGet 2 :: .add :: .localGet 0 :: .load32 16 ::
    .localTee 4 :: .store32 0 :: .localGet 1 :: .localGet 2 ::
    .const 4 :: .add :: .localTee 2 :: .store32 12 :: .localGet 4 ::
    .eqz :: .br_if 1 :: .localGet 0 :: .load32 12 :: .localTee 0 ::
    .localGet 4 :: .const 3 :: .shl :: .add :: .localSet 5 ::
    .loop 0 0 loopBody :: mainTail

/-- The block that the null arm leaves, WAT 1312 to 1474. -/
@[reducible] private def block3 : Program :=
  [.block 0 0 block4, .const 1, .const 1024, .call 99, .unreachable]

/-- The block that the empty arm leaves, WAT 1311 to 1480. -/
@[reducible] private def block2 : Program :=
  [.block 0 0 block3, .localGet 3, .localGet 2, .call 64, .const 1024,
    .localSet 0]

/-- The block that every path leaves, WAT 1310 to 1485. -/
@[reducible] private def block1 : Program :=
  [.block 0 0 block2, .localGet 3, .localGet 0, .const 1, .call 60]

/-- The epilogue, WAT 1487 to 1490. -/
@[reducible] private def epilogue : Program :=
  [.localGet 1, .const 16, .add, .globalSet 0]

/-- The free, which is what the innermost block leaves behind. -/
@[reducible] private def freeTail : Program :=
  [.localGet 3, .localGet 0, .const 1, .call 60]

/-- The write of the empty arm, which is what block 3 leaves behind. -/
@[reducible] private def emptyTail : Program :=
  [.localGet 3, .localGet 2, .call 64, .const 1024, .localSet 0]

/-- The null arm, which is what block 4 leaves behind. -/
@[reducible] private def nullTail : Program :=
  [.const 1, .const 1024, .call 99, .unreachable]

/-- The control frame of the block that holds the allocation. -/
@[reducible] private def frame4 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := block4,
    continuation := nullTail, belowStack := [] }

/-- The control frame of the block that the empty arm leaves. -/
@[reducible] private def frame3 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := block3,
    continuation := emptyTail, belowStack := [] }

/-- The control frame of the block that the main arm leaves. -/
@[reducible] private def frame2 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := block2,
    continuation := freeTail, belowStack := [] }

/-- The control frame of the block that every path leaves. -/
@[reducible] private def frame1 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := block1,
    continuation := epilogue, belowStack := [] }

set_option maxRecDepth 1048576 in
/-- The generated body is the frame, the marker call, one block and the
epilogue. -/
private theorem func5_shape :
    Project.RustHashMap.func5 =
      .globalGet 0 :: .const 16 :: .sub :: .localTee 1 :: .globalSet 0 ::
        .call 33 :: .const 1 :: .localSet 2 :: .block 0 0 block1 ::
        epilogue := rfl

private theorem func5_index :
    Project.RustHashMap.«module».funcs[5]? =
      some Project.RustHashMap.func5Def := by rfl

/-- The registers of absolute `func 8`.  Local 0 is the argument and then
the walk pointer, local 1 the frame, local 2 the cursor, local 3 the
buffer, local 4 the count and then the capacity, local 5 the end of the
entry buffer, and locals 6 and 7 the value and the key of one turn. -/
@[reducible] private def rLocals (l0 l1 l2 l3 l4 l5 l6 l7 : UInt32) :
    Locals :=
  { params := [Value.i32 l0],
    locals := [.i32 l1, .i32 l2, .i32 l3, .i32 l4, .i32 l5, .i32 l6,
      .i32 l7],
    values := [] }

/-! ## Pure facts about the bytes -/

/-- The wire form of an entry list is the count word and then the packed
entries. -/
private theorem serializeEntries_split (ps : List (UInt32 × UInt32)) :
    serializeEntries WordCodec.u32le WordCodec.u32le ps =
      Borsh.u32 (UInt32.ofNat ps.length) ++ Table.pairBytes ps := rfl

/-- One word, as the four bytes that `ByteSlice_of_cells` reports. -/
private theorem word_serialize (w : UInt32) :
    WordCodec.u32le.serialize [w] = Borsh.u32 w := by
  simp only [WordCodec.serialize, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Borsh.u32]

private theorem word_serialize_length (w : UInt32) :
    (WordCodec.u32le.serialize [w]).length = 4 := by
  rw [word_serialize, Borsh.u32, WordCodec.u32le_encode_length]

/-- The borsh form of the option is one byte or five. -/
private theorem option_length (o : Option UInt32) :
    (Borsh.option Borsh.u32 o).length = if o.isSome then 5 else 1 := by
  cases o with
  | none => rfl
  | some v =>
      simp only [Borsh.option, Option.isSome_some, if_true,
        List.length_cons, Borsh.u32, WordCodec.u32le_encode_length]

/-- The borsh form of `some v` is the tag byte and then the payload
word. -/
private theorem option_some_split (v : UInt32) :
    Borsh.option Borsh.u32 (some v) = [1] ++ Borsh.u32 v := rfl

/-! ## The capacity fact -/

/-- The allocator fact that the body carries.  The buffer starts at 1024
bytes and doubles, and the bump allocator never hands a byte out twice, so
the frontier is above twice the capacity.  See the module docstring. -/
private def CapFits (cap frontier : Nat) : Prop :=
  heapBase.toNat + 2 * cap ≤ frontier + 1024

/-- The panic arm of the grow is dead under the capacity fact. -/
private theorem capFits_bound {cap frontier : Nat}
    (hfits : CapFits cap frontier) (hfrontier : frontier < 2147483648) :
    2 * cap ≤ 2147483647 := by
  unfold CapFits at hfits
  have hbase : heapBase.toNat = 1049568 := rfl
  omega

set_option maxRecDepth 1048576 in
/-- The first block of 1024 bytes establishes the fact. -/
private theorem capFits_start {frontier newFrontier : Nat}
    (hbase : heapBase.toNat ≤ frontier)
    (hnew : newFrontier = frontier + 1024) :
    CapFits 1024 newFrontier := by
  unfold CapFits
  subst hnew
  omega

set_option maxRecDepth 1048576 in
/-- The fact survives one grow.  The new block takes `2 * cap` more bytes
of the heap. -/
private theorem capFits_grow {cap frontier newFrontier : Nat}
    (hfits : CapFits cap frontier)
    (hnew : newFrontier = frontier + 2 * cap) :
    CapFits (2 * cap) newFrontier := by
  unfold CapFits at hfits ⊢
  subst hnew
  omega

/-- The capacity the grow selects is twice the old one.  The cursor is
never above the capacity and the capacity is 1024 or more, so neither the
required size nor the floor of eight wins the maximum. -/
private theorem growCapacity_double {cap required : Nat}
    (hcap : 1024 ≤ cap) (hreq : required ≤ cap + 4) :
    growCapacity cap required 1 = 2 * cap := by
  unfold growCapacity
  rw [if_pos rfl]
  omega

/-! ## Reading the allocator bounds -/

/-- Read both frontier bounds of the allocator without giving it up.  Copy
of `DecoderGrow.lean:62`, which is private there. -/
private theorem bumpHeap_bounds [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) :
    BumpHeap heapId storedCursor frontier history ⊢
      iprop(BumpHeap heapId storedCursor frontier history ∗
        ⌜heapBase.toNat ≤ frontier ∧ frontier < 2147483648⌝) := by
  iintro Hbump
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
  isplitl [Hcursor Hfrontier Hauth Hretired Hpages]
  · unfold BumpHeap
    iframe Hcursor Hfrontier Hauth Hretired
    iexists ownedPages
    iframe_pureexact using [Hpages] => hheap
  · ipureexact ⟨hheap.1, hheap.2.1⟩

/-! ## Small ownership helpers -/

/-- Split a byte slice at a byte boundary, and join the two halves. -/
private theorem slice_split [WasmHeapGS Universal.State]
    (ptr : UInt32) (k : Nat) (bytes : List UInt8) (hk : k ≤ bytes.length) :
    Slices.ByteSlice (α := Universal.State) 0 ptr bytes ⊣⊢
      iprop(Slices.ByteSlice 0 ptr (bytes.take k) ∗
        Slices.ByteSlice 0 (ptr + UInt32.ofNat k) (bytes.drop k)) := by
  have h := Slices.ByteSlice_append (α := Universal.State) 0 ptr
    (bytes.take k) (bytes.drop k)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hk] at h
  exact h

/-- Move an owned word between two names of one address.  Copy of
`Func4Proof.lean:1023`, which is private there. -/
private theorem wordMove32 [WasmHeapGS Universal.State]
    {address address' : UInt32} {value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 (α := Universal.State) 0 address value ⊢
      pointsTo_u32 0 address' value := by
  rw [haddress]

/-- One word cell is a four-byte slice. -/
private theorem word_as_slice [WasmHeapGS Universal.State]
    (ptr : UInt32) (w : UInt32) (hnowrap : ptr.toNat + 4 < UInt32.size) :
    pointsTo_u32 (α := Universal.State) 0 ptr w ⊢
      Slices.ByteSlice 0 ptr (Borsh.u32 w) := by
  rw [← word_serialize w]
  iintro Hcell
  iapply ByteSlice_of_cells ptr [w] (by simpa using hnowrap)
  isimp only [arrayAt]
  isplitl_exact Hcell
  · itrivial

/-- A four-byte slice is one word cell, and the address bound comes with
it. -/
private theorem slice_as_word [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (hlen : bytes.length = 4) :
    Slices.ByteSlice (α := Universal.State) 0 ptr bytes ⊢
      iprop(⌜ptr.toNat + 4 < UInt32.size⌝ ∗ ∃ w : UInt32,
        pointsTo_u32 0 ptr w) := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%hnowrap, Hraw⟩
  ihave Hbytes : Slices.ByteSlice 0 ptr bytes $$ [Hraw]
  · isimp only [Slices.ByteSlice]
    isplitl_pureexact hnowrap
    · iexact Hraw
  isplitl_pureexact (by rw [hlen] at hnowrap; exact hnowrap)
  · icases ByteSlice_as_cells ptr bytes 1 (by omega) $$ Hbytes with
      ⟨%hcount, Harray⟩
    obtain ⟨w, hw⟩ := one_word _ hcount
    iexists w
    isimp only [hw, arrayAt] at Harray
    icases Harray with ⟨Hcell, _Hemp⟩
    iexact Hcell

/-- A one-byte slice is the address bound and one owned byte cell.  Copy
of `ContainsKeyTailProof.lean:228`. -/
private theorem slice_as_byte [WasmHeapGS Universal.State]
    (ptr : UInt32) (b : UInt8) :
    Slices.ByteSlice (α := Universal.State) 0 ptr [b] ⊣⊢
      iprop(⌜ptr.toNat + 1 < UInt32.size⌝ ∗
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          ⟨0, ptr⟩ (DFrac.own 1) (some b)) := by
  unfold Slices.ByteSlice
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    pointsToBytes]
  exact BI.sep_congr .rfl BI.sep_emp

/-- Two byte offsets in a row are one byte offset. -/
private theorem addr_step (buf : UInt32) (i j : Nat) :
    buf + UInt32.ofNat i + UInt32.ofNat j = buf + UInt32.ofNat (i + j) := by
  rw [UInt32.add_assoc, ← UInt32.ofNat_add]

/-! ## The reply buffer

`BufAt` is the live block of the reply buffer, split into the bytes the
body has written and the spare bytes after them. -/

/-- The reply buffer: one live block of `cap` bytes at alignment one,
whose first bytes are `written`. -/
private def BufAt [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat) (buf : UInt32) (cap : Nat)
    (written : List UInt8) : HeapIProp :=
  iprop(∃ spare : List UInt8,
    ⌜written.length + spare.length = cap ∧ buf ≠ 0⌝ ∗
    AllocToken heapId allocationId buf
      { size := cap, alignment := 1 } ∗
    Slices.ByteSlice 0 buf written ∗
    Slices.ByteSlice 0 (buf + UInt32.ofNat written.length) spare)

/-- Build the buffer view from a live block whose bytes start with the
written prefix. -/
private theorem BufAt_intro [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat) (buf : UInt32) (cap : Nat)
    (written spare : List UInt8)
    (hlen : written.length + spare.length = cap) :
    LiveBlock heapId allocationId buf { size := cap, alignment := 1 }
        (written ++ spare) ⊢
      BufAt heapId allocationId buf cap written := by
  iintro Hblock
  iunfold LiveBlock at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
  icases (Slices.ByteSlice_append (α := Universal.State) 0 buf written
    spare).mp $$ Hbytes with ⟨Hwritten, Hspare⟩
  iunfold BufAt
  iexists spare
  isplitl_pureexact ⟨hlen, hfacts.2.1⟩
  · isplitl_exact Htoken
    · isplitl_exact Hwritten
      · iexact Hspare

/-- Give the buffer back as a live block. -/
private theorem BufAt_elim [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat) (buf : UInt32) (cap : Nat)
    (written : List UInt8) :
    BufAt heapId allocationId buf cap written ⊢
      iprop(∃ bytes : List UInt8,
        ⌜bytes.length = cap ∧ bytes.take written.length = written⌝ ∗
        LiveBlock heapId allocationId buf
          { size := cap, alignment := 1 } bytes) := by
  iintro Hbuf
  iunfold BufAt at Hbuf
  icases Hbuf with ⟨%spare, %hfacts, Htoken, Hwritten, Hspare⟩
  iexists (written ++ spare)
  isplitl_pureexact
    (⟨by simp only [List.length_append]; omega,
      by simp only [List.take_left]⟩ :
      (written ++ spare).length = cap ∧
        (written ++ spare).take written.length = written)
  · isimp only [LiveBlock]
    isplitl_exact Htoken
    · isplitl [Hwritten Hspare]
      · iapply (Slices.ByteSlice_append (α := Universal.State) 0 buf
          written spare).mpr
        isplitl_exact Hwritten
        · iexact Hspare
      · ipureexact
          (⟨by simp only [List.length_append]; omega, hfacts.2,
            Nat.mod_one _⟩ :
            (written ++ spare).length = cap ∧ buf ≠ 0 ∧
              buf.toNat % 1 = 0)

/-- Focus the next word of the spare region.  The store appends the four
bytes of the new word to the written prefix. -/
private theorem BufAt_word [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat) (buf : UInt32) (cap : Nat)
    (written : List UInt8) (hroom : written.length + 4 ≤ cap) :
    BufAt heapId allocationId buf cap written ⊢
      iprop(⌜(buf + UInt32.ofNat written.length).toNat + 4
          < UInt32.size⌝ ∗ ∃ w : UInt32,
        pointsTo_u32 0 (buf + UInt32.ofNat written.length) w ∗
        (∀ w' : UInt32,
          pointsTo_u32 0 (buf + UInt32.ofNat written.length) w' -∗
          BufAt heapId allocationId buf cap
            (written ++ Borsh.u32 w'))) := by
  iintro Hbuf
  iunfold BufAt at Hbuf
  icases Hbuf with ⟨%spare, %hfacts, Htoken, Hwritten, Hspare⟩
  have hspare : 4 ≤ spare.length := by omega
  icases (slice_split (buf + UInt32.ofNat written.length) 4 spare
    hspare).mp $$ Hspare with ⟨Hhead, Htail⟩
  icases slice_as_word (buf + UInt32.ofNat written.length) (spare.take 4)
    (by rw [List.length_take]; omega) $$ Hhead with ⟨%hbound, %w, Hcell⟩
  isplitl_pureexact hbound
  iexists w
  isplitl_exact Hcell
  · iintro %w' Hcell
    ihave Hnew := word_as_slice (buf + UInt32.ofNat written.length) w'
      hbound $$ Hcell
    iunfold BufAt
    iexists (spare.drop 4)
    isplitl_pureexact
      (⟨by
          rw [List.length_append, List.length_drop,
            show (Borsh.u32 w').length = 4 from
              WordCodec.u32le_encode_length w']
          omega,
        hfacts.2⟩ :
        (written ++ Borsh.u32 w').length + (spare.drop 4).length = cap ∧
          buf ≠ 0)
    · isplitl_exact Htoken
      · isplitl [Hwritten Hnew]
        · iapply (Slices.ByteSlice_append (α := Universal.State) 0 buf
            written (Borsh.u32 w')).mpr
          isplitl_exact Hwritten
          · iexact Hnew
        · irw_exact
            [show buf + UInt32.ofNat written.length + UInt32.ofNat 4
                = buf + UInt32.ofNat (written ++ Borsh.u32 w').length by
              rw [addr_step, List.length_append,
                show (Borsh.u32 w').length = 4 from
                  WordCodec.u32le_encode_length w']]
            with Htail

/-! ## The stack region -/

/-- The region below the caller holds the frame of this body at the top
and the region of the grow below it. -/
private theorem below_frame_split [WasmHeapGS Universal.State]
    (sp : UInt32) (below : List UInt8) :
    StackBelow sp replyDepth below ⊢
      iprop(⌜below.length = 32⌝ ∗
        StackBelow (sp - 16) growDepth (below.take 16) ∗
        Slices.ByteSlice 0 (sp - 16) (below.drop 16)) := by
  have haddr : sp - 16 - UInt32.ofNat growDepth
      = sp - UInt32.ofNat replyDepth := by
    rw [show UInt32.ofNat growDepth = (16 : UInt32) from rfl,
      Table.sub_sub_addr,
      show (16 : UInt32) + 16 = UInt32.ofNat replyDepth from by decide]
  have hup : sp - UInt32.ofNat replyDepth + UInt32.ofNat 16 = sp - 16 := by
    rw [show UInt32.ofNat 16 = (16 : UInt32) from rfl,
      show UInt32.ofNat replyDepth = (16 : UInt32) + 16 from by decide,
      ← Table.sub_sub_addr, UInt32.sub_add_cancel]
  iintro Hbelow
  isimp only [StackBelow] at Hbelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  have hlen32 : below.length = 32 := hlength
  icases (slice_split (sp - UInt32.ofNat replyDepth) 16 below
    (by omega)).mp $$ Hbytes with ⟨Hlow, Hhigh⟩
  isplitl_pureexact hlen32
  · isplitl [Hlow]
    · isimp only [StackBelow]
      isplitl_pureexact
        (show (below.take 16).length = growDepth by
          rw [growDepth_eq, List.length_take]; omega)
      · irw_exact [haddr] with Hlow
    · irw_exact [← hup] with Hhigh

/-- Put the two halves of the region back together. -/
private theorem below_frame_join [WasmHeapGS Universal.State]
    (sp : UInt32) (low frame : List UInt8) (hlow : low.length = 16)
    (hframe : frame.length = 16) :
    iprop(StackBelow (sp - 16) growDepth low ∗
        Slices.ByteSlice 0 (sp - 16) frame) ⊢
      StackBelow sp replyDepth (low ++ frame) := by
  have haddr : sp - 16 - UInt32.ofNat growDepth
      = sp - UInt32.ofNat replyDepth := by
    rw [show UInt32.ofNat growDepth = (16 : UInt32) from rfl,
      Table.sub_sub_addr,
      show (16 : UInt32) + 16 = UInt32.ofNat replyDepth from by decide]
  have hup : sp - UInt32.ofNat replyDepth + UInt32.ofNat low.length
      = sp - 16 := by
    rw [hlow, show UInt32.ofNat 16 = (16 : UInt32) from rfl,
      show UInt32.ofNat replyDepth = (16 : UInt32) + 16 from by decide,
      ← Table.sub_sub_addr, UInt32.sub_add_cancel]
  iintro ⟨Hlow, Hframe⟩
  isimp only [StackBelow] at Hlow
  icases Hlow with ⟨%_hlen, Hlow⟩
  isimp only [StackBelow]
  isplitl_pureexact
    (show (low ++ frame).length = replyDepth by
      rw [List.length_append, hlow, hframe]; rfl)
  · iapply (Slices.ByteSlice_append (α := Universal.State) 0
      (sp - UInt32.ofNat replyDepth) low frame).mpr
    isplitl [Hlow]
    · irw_exact [← haddr] with Hlow
    · irw_exact [hup] with Hframe

/-! ## What the body owes its caller -/

/-- The resources that every path of the body gives back, and the machine
state that the return step leaves. -/
private def ReplyDone [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (heapId : GName)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ (finalLocals : Locals) (below' : List UInt8) (sc' : UInt32)
      (frontier' : Nat) (history' : AllocationHistory),
    RuntimeContext -∗
    StackPointer sp -∗
    StackBelow sp replyDepth below' -∗
    Table.optionU32At 0 arg o -∗
    Slices.ByteSlice 0 (arg + 8)
      (WordCodec.u32le.serialize
        [capacity, ptr, UInt32.ofNat pairs.length]) -∗
    Slices.ByteSlice 0 ptr (Table.pairBytes pairs) -∗
    BumpHeap heapId sc' frontier' history' -∗
    Streams input (output ++ Borsh.option Borsh.u32 o ++
      serializeEntries WordCodec.u32le WordCodec.u32le pairs) raised -∗
    WP (.running ⟨finalLocals, [], arity, remainder, [], calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }])

set_option maxHeartbeats 2000000 in
/-- The stack pointer restore that ends every path, WAT 1487 to 1490. -/
private theorem twp_reply_epilogue [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (heapId : GName)
    (below' : List UInt8) (sc' : UInt32) (frontier' : Nat)
    (history' : AllocationHistory) (input output : List UInt8)
    (raised : Bool)
    {l0 l2 l3 l4 l5 l6 l7 : UInt32}
    {arity : Nat} {remainder : List Value} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer (sp - 16) ∗
      StackBelow sp replyDepth below' ∗
      Table.optionU32At 0 arg o ∗
      Slices.ByteSlice 0 (arg + 8)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat pairs.length]) ∗
      Slices.ByteSlice 0 ptr (Table.pairBytes pairs) ∗
      BumpHeap heapId sc' frontier' history' ∗
      Streams input (output ++ Borsh.option Borsh.u32 o ++
        serializeEntries WordCodec.u32le WordCodec.u32le pairs) raised ∗
      ReplyDone sp arg capacity ptr o pairs heapId input output raised
        arity remainder calls s E Φ) ⊢
      WP (.running
          ⟨rLocals l0 (sp - 16) l2 l3 l4 l5 l6 l7, epilogue, arity,
            remainder, [], calls⟩ : Expr Universal.State) @ s; E
        [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hopt, Hheader, Hpairs, Hbump, Hstreams,
    Hdone⟩
  isimp only [StackPointer] at Hsp
  simp only [epilogue, rLocals]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (16 : UInt32) + (sp - 16) = sp by
    rw [UInt32.add_comm, UInt32.sub_add_cancel]]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer sp $$ [Hsp]
  · isimp only [StackPointer]
    iexact Hsp
  isimp only [ReplyDone] at Hdone
  iapply Hdone $$ %(⟨[Value.i32 l0], [.i32 (sp - 16), .i32 l2, .i32 l3,
      .i32 l4, .i32 l5, .i32 l6, .i32 l7], []⟩ : Locals)
    %below' %sc' %frontier' %history'
    Hruntime Hsp Hbelow Hopt Hheader Hpairs Hbump Hstreams

set_option maxHeartbeats 2000000 in
/-- The free of the reply buffer, WAT 1482 to 1485, and the epilogue after
it.  Both arms of the write reach this point. -/
private theorem twp_reply_free [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr buf capW : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (cap : Nat) (heapId : GName)
    (allocationId : Nat) (bufBytes below' : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {l2 l4 l5 l6 l7 : UInt32}
    {arity : Nat} {remainder : List Value} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hcapW : capW.toNat = cap) :
    iprop(RuntimeContext ∗ StackPointer (sp - 16) ∗
      StackBelow sp replyDepth below' ∗
      Table.optionU32At 0 arg o ∗
      Slices.ByteSlice 0 (arg + 8)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat pairs.length]) ∗
      Slices.ByteSlice 0 ptr (Table.pairBytes pairs) ∗
      LiveBlock heapId allocationId buf
        { size := cap, alignment := 1 } bufBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input (output ++ Borsh.option Borsh.u32 o ++
        serializeEntries WordCodec.u32le WordCodec.u32le pairs) raised ∗
      ReplyDone sp arg capacity ptr o pairs heapId input output raised
        arity remainder calls s E Φ) ⊢
      WP (.running
          ⟨rLocals capW (sp - 16) l2 buf l4 l5 l6 l7, freeTail, arity,
            remainder, [frame1], calls⟩ : Expr Universal.State) @ s; E
        [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hopt, Hheader, Hpairs, Hblock, Hbump,
    Hstreams, Hdone⟩
  simp only [freeTail, rLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_const]
  have Hfree := Project.RustHashMap.Func57Proof.func57_correct (hlc := hlc)
    buf capW 1 { size := cap, alignment := 1 } heapId allocationId
    bufBytes storedCursor frontier history
    (callerLocals :=
      ⟨[Value.i32 capW], [.i32 (sp - 16), .i32 l2, .i32 buf, .i32 l4,
        .i32 l5, .i32 l6, .i32 l7], []⟩)
    (stack := []) (code := []) (arity := arity) (remainder := remainder)
    (controls := [frame1]) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hfree
  simp only [List.cons_append, List.nil_append] at Hfree
  iapply Hfree
  isplitl_exacts [Hruntime Hbump Hblock]
  isplitl_pureexact ⟨hcapW, rfl, Or.inl trivial⟩
  iintro Hruntime Hbump
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  wasm_twp_pures [twp_exitControl]
  simp only [List.take_zero, List.nil_append]
  iapply twp_reply_epilogue sp arg capacity ptr o pairs heapId below'
    storedCursor frontier
    (history.retire allocationId buf { size := cap, alignment := 1 })
    input output raised
  iframe

set_option maxHeartbeats 2000000 in
/-- The write of the empty arm, WAT 1476 to 1480.  The entry count is
zero, so the buffer never grew and its capacity is still 1024. -/
private theorem twp_empty_tail [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr buf cursorW : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (heapId : GName)
    (allocationId : Nat) (low frameBytes written : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {l4 l5 l6 l7 : UInt32}
    {arity : Nat} {remainder : List Value} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlow : low.length = 16) (hframeLen : frameBytes.length = 16)
    (hwritten : written = Borsh.option Borsh.u32 o ++
      serializeEntries WordCodec.u32le WordCodec.u32le pairs)
    (hcursor : cursorW.toNat = written.length) :
    iprop(RuntimeContext ∗ StackPointer (sp - 16) ∗
      StackBelow (sp - 16) growDepth low ∗
      Slices.ByteSlice 0 (sp - 16) frameBytes ∗
      Table.optionU32At 0 arg o ∗
      Slices.ByteSlice 0 (arg + 8)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat pairs.length]) ∗
      Slices.ByteSlice 0 ptr (Table.pairBytes pairs) ∗
      BufAt heapId allocationId buf 1024 written ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ReplyDone sp arg capacity ptr o pairs heapId input output raised
        arity remainder calls s E Φ) ⊢
      WP (.running
          ⟨rLocals arg (sp - 16) cursorW buf l4 l5 l6 l7, emptyTail,
            arity, remainder, [frame2, frame1], calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hlow, Hframe, Hopt, Hheader, Hpairs, Hbuf, Hbump,
    Hstreams, Hdone⟩
  have hpos : 0 < written.length := by
    rw [hwritten, List.length_append]
    have : 0 < (Borsh.option Borsh.u32 o).length := by
      rw [option_length]
      split <;> omega
    omega
  iunfold BufAt at Hbuf
  icases Hbuf with ⟨%spare, %hfacts, Htoken, Hwritten, Hspare⟩
  simp only [emptyTail, rLocals]
  wasm_twp_pures [twp_localGet twp_localGet]
  have Hwrite := Project.RustHashMap.ImportProofs.func61_correct
    (hlc := hlc) buf cursorW written input output raised
    (callerLocals :=
      ⟨[Value.i32 arg], [.i32 (sp - 16), .i32 cursorW, .i32 buf, .i32 l4,
        .i32 l5, .i32 l6, .i32 l7], []⟩)
    (stack := []) (code := [.const 1024, .localSet 0]) (arity := arity)
    (remainder := remainder) (controls := [frame2, frame1])
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func61Spec CallContract callExpr at Hwrite
  simp only [List.cons_append, List.nil_append] at Hwrite
  iapply Hwrite
  isplitl_exacts [Hruntime Hstreams Hwritten]
  isplitl_pureexact ⟨hcursor, by omega⟩
  iintro Hruntime Hstreams Hwritten
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_exitControl]
  simp only [List.take_zero, List.nil_append]
  ihave Hbuf : BufAt heapId allocationId buf 1024 written $$
    [Htoken Hwritten Hspare]
  · iunfold BufAt
    iexists spare
    isplitl_pureexact hfacts
    · isplitl_exact Htoken
      · isplitl_exact Hwritten
        · iexact Hspare
  icases BufAt_elim heapId allocationId buf 1024 written $$ Hbuf with
    ⟨%bufBytes, %hbytes, Hblock⟩
  ihave Hbelow := below_frame_join sp low frameBytes hlow hframeLen $$
    [Hlow Hframe]
  · isplitl_exact Hlow
    · iexact Hframe
  ihave Hstreams : Streams input (output ++ Borsh.option Borsh.u32 o ++
      serializeEntries WordCodec.u32le WordCodec.u32le pairs) raised $$
    [Hstreams]
  · irw_exact [List.append_assoc, ← hwritten] with Hstreams
  iapply twp_reply_free sp arg capacity ptr buf 1024 o pairs 1024 heapId
    allocationId bufBytes (low ++ frameBytes) storedCursor frontier
    history input output raised rfl
  iframe

set_option maxHeartbeats 2000000 in
/-- The write of the main arm, WAT 1458 to 1469.  The body reloads the
capacity and the buffer from the frame, writes the buffer out, and leaves
the block by the branch at WAT 1469.  The guard at WAT 1466 to 1468 is
dead, because the capacity is 1024 or more. -/
private theorem twp_main_tail [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr buf capW cursorW w0 : UInt32)
    (o : Option UInt32) (pairs : List (UInt32 × UInt32)) (cap : Nat)
    (heapId : GName) (allocationId : Nat) (low written : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {l0 l3 l4 l5 l6 l7 : UInt32}
    {arity : Nat} {remainder : List Value} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlow : low.length = 16)
    (hframeAddr : (sp - 16).toNat + 16 < UInt32.size)
    (hcapW : capW.toNat = cap) (hcap : 1024 ≤ cap)
    (hwritten : written = Borsh.option Borsh.u32 o ++
      serializeEntries WordCodec.u32le WordCodec.u32le pairs)
    (hcursor : cursorW.toNat = written.length) :
    iprop(RuntimeContext ∗ StackPointer (sp - 16) ∗
      StackBelow (sp - 16) growDepth low ∗
      arrayAt 0 (sp - 16) [w0, capW, buf, cursorW] ∗
      Table.optionU32At 0 arg o ∗
      Slices.ByteSlice 0 (arg + 8)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat pairs.length]) ∗
      Slices.ByteSlice 0 ptr (Table.pairBytes pairs) ∗
      BufAt heapId allocationId buf cap written ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ReplyDone sp arg capacity ptr o pairs heapId input output raised
        arity remainder calls s E Φ) ⊢
      WP (.running
          ⟨rLocals l0 (sp - 16) cursorW l3 l4 l5 l6 l7, mainTail, arity,
            remainder, [frame4, frame3, frame2, frame1], calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hlow, Hcells, Hopt, Hheader, Hpairs, Hbuf, Hbump,
    Hstreams, Hdone⟩
  have hpos : 0 < written.length := by
    rw [hwritten, List.length_append]
    have : 0 < (Borsh.option Borsh.u32 o).length := by
      rw [option_length]
      split <;> omega
    omega
  have hf4 := offset_facts (sp - 16) 4 4 rfl (by omega)
  have hf8 := offset_facts (sp - 16) 8 8 rfl (by omega)
  have hcapNe : capW ≠ 0 := by
    intro hzero
    rw [hzero] at hcapW
    simp only [show (0 : UInt32).toNat = 0 from rfl] at hcapW
    omega
  iunfold BufAt at Hbuf
  icases Hbuf with ⟨%spare, %hfacts, Htoken, Hwritten, Hspare⟩
  simp only [mainTail, rLocals]
  wasm_twp_pures [twp_localGet]
  icases cell_load (sp - 16) 4 [w0, capW, buf, cursorW] 1 capW
    (by simp) rfl (by decide) $$ Hcells with ⟨Hcap, Hcells⟩
  wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := sp - 16)
    (offset := 4) capW hf4.1 hf4.2.1 hf4.2.2.1 hf4.2.2.2 with Hcap
  ihave Hcells := Hcells $$ Hcap
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  icases cell_load (sp - 16) 8 [w0, capW, buf, cursorW] 2 buf
    (by simp) rfl (by decide) $$ Hcells with ⟨Hbuf8, Hcells⟩
  wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := sp - 16)
    (offset := 8) buf hf8.1 hf8.2.1 hf8.2.2.1 hf8.2.2.2 with Hbuf8
  ihave Hcells := Hcells $$ Hbuf8
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  have Hwrite := Project.RustHashMap.ImportProofs.func61_correct
    (hlc := hlc) buf cursorW written input output raised
    (callerLocals :=
      ⟨[Value.i32 capW], [.i32 (sp - 16), .i32 cursorW, .i32 buf, .i32 l4,
        .i32 l5, .i32 l6, .i32 l7], []⟩)
    (stack := []) (code := [.localGet 0, .eqz, .br_if 3, .br 2])
    (arity := arity) (remainder := remainder)
    (controls := [frame4, frame3, frame2, frame1]) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  unfold Func61Spec CallContract callExpr at Hwrite
  simp only [List.cons_append, List.nil_append] at Hwrite
  iapply Hwrite
  isplitl_exacts [Hruntime Hstreams Hwritten]
  isplitl_pureexact ⟨hcursor, by omega⟩
  iintro Hruntime Hstreams Hwritten
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  wasm_twp_pures [twp_localGet]
  iapply Wasm.SmallStep.twp_eqz (result := 0) (by rw [if_neg hcapNe])
  wasm_twp_pures [twp_brIfZero]
  iapply Wasm.SmallStep.twp_br (by rfl)
  simp only [List.take_nil, List.nil_append]
  ihave Hbuf : BufAt heapId allocationId buf cap written $$
    [Htoken Hwritten Hspare]
  · iunfold BufAt
    iexists spare
    isplitl_pureexact hfacts
    · isplitl_exact Htoken
      · isplitl_exact Hwritten
        · iexact Hspare
  icases BufAt_elim heapId allocationId buf cap written $$ Hbuf with
    ⟨%bufBytes, %hbytes, Hblock⟩
  ihave Hframe := ByteSlice_of_cells (sp - 16) [w0, capW, buf, cursorW]
    (by simpa using hframeAddr) $$ Hcells
  ihave Hbelow := below_frame_join sp low
    (WordCodec.u32le.serialize [w0, capW, buf, cursorW]) hlow
    (by rw [WordCodec.u32le_serialize_length]; rfl) $$ [Hlow Hframe]
  · isplitl_exact Hlow
    · iexact Hframe
  ihave Hstreams : Streams input (output ++ Borsh.option Borsh.u32 o ++
      serializeEntries WordCodec.u32le WordCodec.u32le pairs) raised $$
    [Hstreams]
  · irw_exact [List.append_assoc, ← hwritten] with Hstreams
  iapply twp_reply_free sp arg capacity ptr buf capW o pairs cap heapId
    allocationId bufBytes
    (low ++ WordCodec.u32le.serialize [w0, capW, buf, cursorW])
    storedCursor frontier history input output raised hcapW
  iframe

/-! ## The grow -/

/-- The layout of the reply buffer is valid whenever the capacity fact
holds. -/
private theorem buffer_layout_valid {cap : Nat} (hcap : 1024 ≤ cap)
    (hbound : 2 * cap ≤ 2147483647) :
    AllocLayout.Valid { size := cap, alignment := 1 } := by
  refine ⟨?_, ?_, ⟨0, rfl⟩, ?_, ?_, ?_, ?_⟩
  · show 0 < cap
    omega
  · show 0 < 1
    omega
  · show 1 ≤ 2147483648
    omega
  · show cap ≤ 2147483648 - 1
    omega
  · show cap < UInt32.size
    simp only [UInt32.size]
    omega
  · show 1 < UInt32.size
    simp only [UInt32.size]
    omega

/-- The unsigned difference of two words that do not cross. -/
private theorem sub_toNat {a b : UInt32} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have ha := UInt32.toNat_lt a
  have hb := UInt32.toNat_lt b
  simp only [UInt32.toNat_sub] at *
  omega

/-- Read the length of a stack region without giving it up. -/
private theorem below_length [WasmHeapGS Universal.State]
    (sp : UInt32) (depth : Nat) (bytes : List UInt8) :
    StackBelow sp depth bytes ⊢
      iprop(⌜bytes.length = depth⌝ ∗ StackBelow sp depth bytes) := by
  iintro Hbelow
  isimp only [StackBelow] at Hbelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  isplitl_pureexact hlength
  · isimp only [StackBelow]
    isplitl_pureexact hlength
    · iexact Hbytes

/-- Read the byte count of a live block without giving it up. -/
private theorem liveBlock_length [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat) (p : UInt32)
    (layout : AllocLayout) (bytes : List UInt8) :
    LiveBlock heapId allocationId p layout bytes ⊢
      iprop(⌜bytes.length = layout.size⌝ ∗
        LiveBlock heapId allocationId p layout bytes) := by
  iintro Hblock
  iunfold LiveBlock at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
  isplitl_pureexact hfacts.1
  · iunfold LiveBlock
    isplitl_exact Htoken
    · isplitl_exact Hbytes
      · ipureexact hfacts

/-- Read the address bound of a byte slice without giving it up. -/
private theorem slice_bound [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) :
    Slices.ByteSlice (α := Universal.State) 0 ptr bytes ⊢
      iprop(⌜ptr.toNat + bytes.length < UInt32.size⌝ ∗
        Slices.ByteSlice 0 ptr bytes) := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%hnowrap, Hraw⟩
  isplitl_pureexact hnowrap
  · isimp only [Slices.ByteSlice]
    isplitl_pureexact hnowrap
    · iexact Hraw

/-- The shape of a one-byte list. -/
private theorem one_byte (bytes : List UInt8) (h : bytes.length = 1) :
    ∃ b : UInt8, bytes = [b] := by
  rcases bytes with _ | ⟨b, rest⟩
  · simp at h
  rcases rest with _ | ⟨c, rest⟩
  · exact ⟨b, rfl⟩
  · simp at h

/-- The pointer of a live block is never null. -/
private theorem liveBlock_nonzero [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat) (p : UInt32)
    (layout : AllocLayout) (bytes : List UInt8) :
    LiveBlock heapId allocationId p layout bytes ⊢
      iprop(⌜p ≠ 0⌝ ∗ LiveBlock heapId allocationId p layout bytes) := by
  iintro Hblock
  iunfold LiveBlock at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
  isplitl_pureexact hfacts.2.1
  · iunfold LiveBlock
    isplitl_exact Htoken
    · isplitl_exact Hbytes
      · ipureexact hfacts

/-- What the grow leaves for the reload sequence after it. -/
private def GrowCallDone [WasmSmallStepGS hlc Universal.State]
    (fbase : UInt32) (cap : Nat) (heapId : GName) (written : List UInt8)
    (input output : List UInt8) (raised : Bool) (Hexit : HeapIProp)
    (locals : Locals)
    (rest : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ (newBuf : UInt32) (newAllocationId : Nat) (sc' : UInt32)
      (frontier' : Nat) (history' : AllocationHistory)
      (low' : List UInt8),
    ⌜CapFits (2 * cap) frontier' ∧ frontier' < 2147483648 ∧
      heapBase.toNat ≤ frontier' ∧ low'.length = 16⌝ -∗
    RuntimeContext -∗
    StackPointer fbase -∗
    StackBelow fbase growDepth low' -∗
    pointsTo_u32 0 (fbase + 4) (UInt32.ofNat (2 * cap)) -∗
    pointsTo_u32 0 (fbase + 4 + 4) newBuf -∗
    BufAt heapId newAllocationId newBuf (2 * cap) written -∗
    BumpHeap heapId sc' frontier' history' -∗
    Streams input output raised -∗
    Hexit -∗
    WP (.running ⟨locals, rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }])

set_option maxHeartbeats 2000000 in
/-- The grow itself, WAT 1388 to 1395 and WAT 1424 to 1431.  The buffer
doubles, and the capacity fact carries over. -/
private theorem twp_growCall [WasmSmallStepGS hlc Universal.State]
    (fbase buf cursorW : UInt32) (cap cursor allocationId : Nat)
    (heapId : GName) (written low : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) (Hexit : HeapIProp)
    {l0 l3 l4 l5 l6 l7 : UInt32}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hoomOf : Hexit ⊢ iprop(∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage))))
    (hcap : 1024 ≤ cap) (hfits : CapFits cap frontier)
    (hfrontier : frontier < 2147483648)
    (hbaseLe : heapBase.toNat ≤ frontier)
    (hcursorW : cursorW.toNat = cursor)
    (hwritten : written.length = cursor)
    (hfull : cap ≤ cursor + 3) (hroom : cursor ≤ cap)
    (hframe : fbase.toNat + 16 < UInt32.size) (hdepth : 16 ≤ fbase.toNat) :
    iprop(RuntimeContext ∗ StackPointer fbase ∗
      StackBelow fbase growDepth low ∗
      pointsTo_u32 0 (fbase + 4) (UInt32.ofNat cap) ∗
      pointsTo_u32 0 (fbase + 4 + 4) buf ∗
      BufAt heapId allocationId buf cap written ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      Hexit ∗
      GrowCallDone fbase cap heapId written input output raised Hexit
        (rLocals l0 fbase cursorW l3 l4 l5 l6 l7) rest arity remainder
        controls calls s E Φ) ⊢
      WP (.running
          ⟨rLocals l0 fbase cursorW l3 l4 l5 l6 l7,
            .localGet 1 :: .const 4 :: .add :: .localGet 2 :: .const 4 ::
              .const 1 :: .const 1 :: .call 13 :: rest, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hlow, Hcap, Hbufptr, Hblockown, Hbump, Hstreams,
    Hoom, Hdone⟩
  have hone : (1 : UInt32).toNat = 1 := rfl
  have hfour : (4 : UInt32).toNat = 4 := rfl
  have hbound : 2 * cap ≤ 2147483647 := capFits_bound hfits hfrontier
  have hcapW : (UInt32.ofNat cap).toNat = cap :=
    UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
  have hgrowNat :
      growCapacity (UInt32.ofNat cap).toNat
          (cursorW.toNat + (4 : UInt32).toNat) (1 : UInt32).toNat
        = 2 * cap := by
    rw [hcapW, hcursorW, hfour, hone]
    exact growCapacity_double hcap (by omega)
  have hlayout :
      ({ size := (1 : UInt32).toNat * (UInt32.ofNat cap).toNat,
          alignment := (1 : UInt32).toNat } : AllocLayout)
        = { size := cap, alignment := 1 } := by
    rw [hone, hcapW, Nat.one_mul]
  have hf4 := offset_facts fbase 4 4 rfl (by omega)
  icases BufAt_elim heapId allocationId buf cap written $$ Hblockown with
    ⟨%bufBytes, %hbytes, Hblock⟩
  simp only [rLocals]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (4 : UInt32) + fbase = fbase + 4 from UInt32.add_comm 4 fbase]
  wasm_twp_pures [twp_localGet twp_const twp_const twp_const]
  have Hgrow := Project.RustHashMap.Func10Proof.func10_correct (hlc := hlc)
    fbase (fbase + 4) (UInt32.ofNat cap) buf cursorW 4 1 1
    (FinishSource.allocated allocationId bufBytes) low heapId storedCursor
    frontier history input output raised
    (callerLocals :=
      ⟨[Value.i32 l0], [.i32 fbase, .i32 cursorW, .i32 l3, .i32 l4,
        .i32 l5, .i32 l6, .i32 l7], []⟩)
    (stack := []) (code := rest) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hgrow
  simp only [List.cons_append, List.nil_append] at Hgrow
  iapply Hgrow
  isplitl_exacts [Hruntime Hsp Hlow Hcap Hbufptr]
  isplitl [Hblock]
  · rw [hlayout]
    isimp only [FinishSourceOwn]
    isplitl_pureexact (by
      refine ⟨?_, buffer_layout_valid hcap hbound⟩
      rw [hcapW]
      omega)
    · iexact Hblock
  isplitl_exacts [Hbump Hstreams]
  isplitl_pureexact (by
    refine ⟨Or.inl trivial, Or.inl trivial, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf4.1, hfour]
      omega
    · rw [hcursorW, hfour]
      simp only [UInt32.size]
      omega
    · rw [hcapW, hcursorW, hfour]
      omega
    · rw [hgrowNat, hone, Nat.one_mul]
      omega
    · rw [growDepth_eq]
      omega)
  isimp only [GrowContinuation]
  rw [hgrowNat, hcapW, hone]
  simp only [Nat.one_mul]
  cases hdecision :
      classifyBump frontier
        ({ size := 2 * cap, alignment := 1 } : AllocLayout) with
  | oom =>
      iintro Hsp Hlow Hcap Hbufptr Hsource Hbump Hstreams
      ihave Hwand := hoomOf $$ Hoom
      iapply Hwand $$ %input Hstreams
  | success newPtr finish =>
      obtain ⟨hfrontLt, hbaseEq, hbaseNat, hendWord, hendSigned,
        hfinishNat⟩ :=
        classifyBump_success_align1 frontier (2 * cap) newPtr finish
          hdecision
      isplit
      · iintro %newBytes %low' Hruntime Hsp Hlow Hcap Hbufptr Hblock
          Hbump %hcopied Hstreams
        icases below_length fbase growDepth low' $$ Hlow with
          ⟨%hlow', Hlow⟩
        icases liveBlock_length heapId history.nextId newPtr
          { size := 2 * cap, alignment := 1 } newBytes $$ Hblock with
          ⟨%hnewLen, Hblock⟩
        have hlow16 : low'.length = 16 := by
          rw [hlow', growDepth_eq]
        have hcopy : newBytes.take cap = bufBytes := hcopied
        have hprefix : newBytes.take written.length = written := by
          have hcut : (newBytes.take cap).take written.length
              = newBytes.take written.length := by
            rw [List.take_take]
            congr 1
            omega
          rw [← hcut, hcopy, hbytes.2]
        ihave Hbuf := BufAt_intro heapId history.nextId newPtr (2 * cap)
          written (newBytes.drop written.length)
          (by
            rw [List.length_drop]
            have : newBytes.length = 2 * cap := hnewLen
            omega) $$ [Hblock]
        · irw_exact
            [show written ++ newBytes.drop written.length = newBytes by
              conv_rhs =>
                rw [← List.take_append_drop written.length newBytes]
              rw [hprefix]]
            with Hblock
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        isimp only [GrowCallDone] at Hdone
        iapply Hdone $$ %newPtr %history.nextId %finish %finish.toNat
          %(growHistory history
              (FinishSource.allocated allocationId bufBytes) buf
              { size := cap, alignment := 1 } newPtr
              { size := 2 * cap, alignment := 1 })
          %low'
          %(⟨capFits_grow hfits hfinishNat, by omega, by omega, hlow16⟩ :
            CapFits (2 * cap) finish.toNat ∧
              finish.toNat < 2147483648 ∧
              heapBase.toNat ≤ finish.toNat ∧ low'.length = 16)
          Hruntime Hsp Hlow Hcap Hbufptr Hbuf Hbump Hstreams Hoom
      · iintro Hsp Hlow Hcap Hbufptr Hsource Hbump Hstreams
        ihave Hwand := hoomOf $$ Hoom
        iapply Hwand $$ %input Hstreams

/-- The third word of the frame, as one offset. -/
private theorem addr4 (b : UInt32) : b + 4 + 4 = b + 8 := by
  rw [UInt32.add_assoc, show (4 : UInt32) + 4 = 8 from by decide]

/-- The fourth word of the frame, as one offset. -/
private theorem addr12 (b : UInt32) : b + 4 + 4 + 4 = b + 12 := by
  rw [addr4, UInt32.add_assoc, show (4 : UInt32) + 8 = 12 from by decide]

/-- What one grow block leaves for the store after it. -/
private def GrowDone [WasmSmallStepGS hlc Universal.State]
    (fbase w0 cursorW : UInt32) (cursor : Nat) (heapId : GName)
    (written : List UInt8) (input output : List UInt8) (raised : Bool)
    (Hexit : HeapIProp)
    (mkLocals : UInt32 → UInt32 → Locals) (rest : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ (buf capW : UInt32) (cap allocationId : Nat) (sc' : UInt32)
      (frontier' : Nat) (history' : AllocationHistory)
      (low' : List UInt8),
    ⌜capW = UInt32.ofNat cap ∧ 1024 ≤ cap ∧ CapFits cap frontier' ∧
      frontier' < 2147483648 ∧ heapBase.toNat ≤ frontier' ∧
      cursor + 4 ≤ cap ∧ low'.length = 16⌝ -∗
    RuntimeContext -∗
    StackPointer fbase -∗
    StackBelow fbase growDepth low' -∗
    pointsTo_u32 0 fbase w0 -∗
    pointsTo_u32 0 (fbase + 4) capW -∗
    pointsTo_u32 0 (fbase + 4 + 4) buf -∗
    pointsTo_u32 0 (fbase + 4 + 4 + 4) cursorW -∗
    BufAt heapId allocationId buf cap written -∗
    BumpHeap heapId sc' frontier' history' -∗
    Streams input output raised -∗
    Hexit -∗
    WP (.running ⟨mkLocals buf capW, rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }])

set_option maxHeartbeats 2000000 in
/-- The grow block in front of the key store, WAT 1379 to 1405.  The guard
skips the grow when four bytes are free. -/
private theorem twp_growKeyBlock [WasmSmallStepGS hlc Universal.State]
    (fbase buf cursorW w0 : UInt32) (cap cursor allocationId : Nat)
    (heapId : GName) (written low : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) (Hexit : HeapIProp)
    {l0 l4 l5 l6 l7 : UInt32}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hoomOf : Hexit ⊢ iprop(∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage))))
    (hcap : 1024 ≤ cap)
    (hfits : CapFits cap frontier) (hfrontier : frontier < 2147483648)
    (hbaseLe : heapBase.toNat ≤ frontier) (hlow : low.length = 16)
    (hcursorW : cursorW.toNat = cursor) (hwritten : written.length = cursor)
    (hroom : cursor ≤ cap) (hframe : fbase.toNat + 16 < UInt32.size)
    (hdepth : 16 ≤ fbase.toNat) :
    iprop(RuntimeContext ∗ StackPointer fbase ∗
      StackBelow fbase growDepth low ∗
      pointsTo_u32 0 fbase w0 ∗
      pointsTo_u32 0 (fbase + 4) (UInt32.ofNat cap) ∗
      pointsTo_u32 0 (fbase + 4 + 4) buf ∗
      pointsTo_u32 0 (fbase + 4 + 4 + 4) cursorW ∗
      BufAt heapId allocationId buf cap written ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      Hexit ∗
      GrowDone fbase w0 cursorW cursor heapId written input output raised
        Hexit (fun b c => rLocals l0 fbase cursorW b c l5 l6 l7) rest
        arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨rLocals l0 fbase cursorW buf l4 l5 l6 l7,
            .block 0 0 growKey :: rest, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hlow, Hw0, Hcap, Hbufptr, Hcur, Hbuf, Hbump,
    Hstreams, Hoom, Hdone⟩
  have hbound : 2 * cap ≤ 2147483647 := capFits_bound hfits hfrontier
  have hcapNat : (UInt32.ofNat cap).toNat = cap :=
    UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
  have hdiff : (UInt32.ofNat cap - cursorW).toNat = cap - cursor := by
    rw [sub_toNat (by rw [hcapNat, hcursorW]; omega), hcapNat, hcursorW]
  have hgt : (UInt32.ofNat cap - cursorW > (3 : UInt32))
      ↔ 3 < cap - cursor := by
    show ((3 : UInt32) < UInt32.ofNat cap - cursorW) ↔ _
    rw [UInt32.lt_iff_toNat_lt, hdiff,
      show (3 : UInt32).toNat = 3 from rfl]
  have hf4 := offset_facts fbase 4 4 rfl (by omega)
  have hf8 := offset_facts fbase 8 8 rfl (by omega)
  have hf12 := offset_facts fbase 12 12 rfl (by omega)
  simp only [rLocals]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero, growKey]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := fbase) (offset := 4)
    (UInt32.ofNat cap) hf4.1 hf4.2.1 hf4.2.2.1 hf4.2.2.2 with Hcap
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_sub twp_const]
  by_cases hfull : cursor + 4 ≤ cap
  · iapply Wasm.SmallStep.twp_gtU (result := 1)
      (by rw [if_pos (hgt.mpr (by omega))])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    isimp only [GrowDone] at Hdone
    iapply Hdone $$ %buf %(UInt32.ofNat cap) %cap %allocationId
      %storedCursor %frontier %history %low
      %(⟨rfl, hcap, hfits, hfrontier, hbaseLe, hfull, hlow⟩ :
        UInt32.ofNat cap = UInt32.ofNat cap ∧ 1024 ≤ cap ∧
          CapFits cap frontier ∧ frontier < 2147483648 ∧
          heapBase.toNat ≤ frontier ∧ cursor + 4 ≤ cap ∧
          low.length = 16)
      Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump Hstreams Hoom
  · iapply Wasm.SmallStep.twp_gtU (result := 0)
      (by rw [if_neg (by rw [hgt]; omega)])
    wasm_twp_pures [twp_brIfZero]
    iapply twp_growCall (l3 := buf) fbase buf cursorW cap cursor
      allocationId heapId written low storedCursor frontier history input
      output raised Hexit hoomOf hcap hfits hfrontier hbaseLe hcursorW
      hwritten (by omega) hroom hframe hdepth
    isplitl_exacts [Hruntime Hsp Hlow Hcap Hbufptr Hbuf Hbump Hstreams
      Hoom]
    isimp only [GrowCallDone]
    iintro %newBuf %newId %sc' %frontier' %history' %low' %hnew Hruntime
      Hsp Hlow Hcap Hbufptr Hbuf Hbump Hstreams Hoom
    wasm_twp_pures [twp_localGet]
    ihave Hbufptr := wordMove32 (addr4 fbase) $$ Hbufptr
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := fbase)
      (offset := 8) newBuf hf8.1 hf8.2.1 hf8.2.2.1 hf8.2.2.2 with Hbufptr
    ihave Hbufptr := wordMove32 (addr4 fbase).symm $$ Hbufptr
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := fbase)
      (offset := 4) (UInt32.ofNat (2 * cap)) hf4.1 hf4.2.1 hf4.2.2.1
      hf4.2.2.2 with Hcap
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    ihave Hcur := wordMove32 (addr12 fbase) $$ Hcur
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := fbase)
      (offset := 12) cursorW hf12.1 hf12.2.1 hf12.2.2.1 hf12.2.2.2
      with Hcur
    ihave Hcur := wordMove32 (addr12 fbase).symm $$ Hcur
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append]
    isimp only [GrowDone] at Hdone
    iapply Hdone $$ %newBuf %(UInt32.ofNat (2 * cap)) %(2 * cap) %newId
      %sc' %frontier' %history' %low'
      %(⟨rfl, by omega, hnew.1, hnew.2.1, hnew.2.2.1, by omega,
          hnew.2.2.2⟩ :
        UInt32.ofNat (2 * cap) = UInt32.ofNat (2 * cap) ∧
          1024 ≤ 2 * cap ∧ CapFits (2 * cap) frontier' ∧
          frontier' < 2147483648 ∧ heapBase.toNat ≤ frontier' ∧
          cursor + 4 ≤ 2 * cap ∧ low'.length = 16)
      Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump Hstreams Hoom

set_option maxHeartbeats 2000000 in
/-- The grow block in front of the value store, WAT 1417 to 1438.  The
guard reads the capacity register that the first block left, and the
reload after the grow leaves that register alone. -/
private theorem twp_growValueBlock [WasmSmallStepGS hlc Universal.State]
    (fbase buf cursorW w0 : UInt32) (cap cursor allocationId : Nat)
    (heapId : GName) (written low : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) (Hexit : HeapIProp)
    {l0 l5 l6 l7 : UInt32}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hoomOf : Hexit ⊢ iprop(∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage))))
    (hcap : 1024 ≤ cap)
    (hfits : CapFits cap frontier) (hfrontier : frontier < 2147483648)
    (hbaseLe : heapBase.toNat ≤ frontier) (hlow : low.length = 16)
    (hcursorW : cursorW.toNat = cursor) (hwritten : written.length = cursor)
    (hroom : cursor ≤ cap) (hframe : fbase.toNat + 16 < UInt32.size)
    (hdepth : 16 ≤ fbase.toNat) :
    iprop(RuntimeContext ∗ StackPointer fbase ∗
      StackBelow fbase growDepth low ∗
      pointsTo_u32 0 fbase w0 ∗
      pointsTo_u32 0 (fbase + 4) (UInt32.ofNat cap) ∗
      pointsTo_u32 0 (fbase + 4 + 4) buf ∗
      pointsTo_u32 0 (fbase + 4 + 4 + 4) cursorW ∗
      BufAt heapId allocationId buf cap written ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      Hexit ∗
      GrowDone fbase w0 cursorW cursor heapId written input output raised
        Hexit
        (fun b _ => rLocals l0 fbase cursorW b (UInt32.ofNat cap) l5 l6 l7)
        rest arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨rLocals l0 fbase cursorW buf (UInt32.ofNat cap) l5 l6 l7,
            .block 0 0 growValue :: rest, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hlow, Hw0, Hcap, Hbufptr, Hcur, Hbuf, Hbump,
    Hstreams, Hoom, Hdone⟩
  have hbound : 2 * cap ≤ 2147483647 := capFits_bound hfits hfrontier
  have hcapNat : (UInt32.ofNat cap).toNat = cap :=
    UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
  have hdiff : (UInt32.ofNat cap - cursorW).toNat = cap - cursor := by
    rw [sub_toNat (by rw [hcapNat, hcursorW]; omega), hcapNat, hcursorW]
  have hgt : (UInt32.ofNat cap - cursorW > (3 : UInt32))
      ↔ 3 < cap - cursor := by
    show ((3 : UInt32) < UInt32.ofNat cap - cursorW) ↔ _
    rw [UInt32.lt_iff_toNat_lt, hdiff,
      show (3 : UInt32).toNat = 3 from rfl]
  have hf8 := offset_facts fbase 8 8 rfl (by omega)
  have hf12 := offset_facts fbase 12 12 rfl (by omega)
  simp only [rLocals]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero, growValue]
  wasm_twp_pures [twp_localGet twp_localGet twp_sub twp_const]
  by_cases hfull : cursor + 4 ≤ cap
  · iapply Wasm.SmallStep.twp_gtU (result := 1)
      (by rw [if_pos (hgt.mpr (by omega))])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    isimp only [GrowDone] at Hdone
    iapply Hdone $$ %buf %(UInt32.ofNat cap) %cap %allocationId
      %storedCursor %frontier %history %low
      %(⟨rfl, hcap, hfits, hfrontier, hbaseLe, hfull, hlow⟩ :
        UInt32.ofNat cap = UInt32.ofNat cap ∧ 1024 ≤ cap ∧
          CapFits cap frontier ∧ frontier < 2147483648 ∧
          heapBase.toNat ≤ frontier ∧ cursor + 4 ≤ cap ∧
          low.length = 16)
      Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump Hstreams Hoom
  · iapply Wasm.SmallStep.twp_gtU (result := 0)
      (by rw [if_neg (by rw [hgt]; omega)])
    wasm_twp_pures [twp_brIfZero]
    iapply twp_growCall (l3 := buf) (l4 := UInt32.ofNat cap) fbase buf
      cursorW cap cursor allocationId heapId written low storedCursor
      frontier history input output raised Hexit hoomOf hcap hfits
      hfrontier hbaseLe hcursorW hwritten (by omega) hroom hframe hdepth
    isplitl_exacts [Hruntime Hsp Hlow Hcap Hbufptr Hbuf Hbump Hstreams
      Hoom]
    isimp only [GrowCallDone]
    iintro %newBuf %newId %sc' %frontier' %history' %low' %hnew Hruntime
      Hsp Hlow Hcap Hbufptr Hbuf Hbump Hstreams Hoom
    wasm_twp_pures [twp_localGet]
    ihave Hbufptr := wordMove32 (addr4 fbase) $$ Hbufptr
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := fbase)
      (offset := 8) newBuf hf8.1 hf8.2.1 hf8.2.2.1 hf8.2.2.2 with Hbufptr
    ihave Hbufptr := wordMove32 (addr4 fbase).symm $$ Hbufptr
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    ihave Hcur := wordMove32 (addr12 fbase) $$ Hcur
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := fbase)
      (offset := 12) cursorW hf12.1 hf12.2.1 hf12.2.2.1 hf12.2.2.2
      with Hcur
    ihave Hcur := wordMove32 (addr12 fbase).symm $$ Hcur
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append]
    isimp only [GrowDone] at Hdone
    iapply Hdone $$ %newBuf %(UInt32.ofNat (2 * cap)) %(2 * cap) %newId
      %sc' %frontier' %history' %low'
      %(⟨rfl, by omega, hnew.1, hnew.2.1, hnew.2.2.1, by omega,
          hnew.2.2.2⟩ :
        UInt32.ofNat (2 * cap) = UInt32.ofNat (2 * cap) ∧
          1024 ≤ 2 * cap ∧ CapFits (2 * cap) frontier' ∧
          frontier' < 2147483648 ∧ heapBase.toNat ≤ frontier' ∧
          cursor + 4 ≤ 2 * cap ∧ low'.length = 16)
      Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump Hstreams Hoom

/-! ## The bytes the loop writes -/

/-- The length of the borsh form of the option. -/
private def optLen (o : Option UInt32) : Nat :=
  (Borsh.option Borsh.u32 o).length

private theorem optLen_bounds (o : Option UInt32) :
    1 ≤ optLen o ∧ optLen o ≤ 5 := by
  unfold optLen
  rw [option_length]
  split <;> omega

private theorem optLen_none : optLen (none : Option UInt32) = 1 := rfl

private theorem optLen_some (v : UInt32) : optLen (some v) = 5 := by
  simp only [optLen, option_length, Option.isSome_some, if_true]

/-- Move an owned byte slice between two names of one address. -/
private theorem sliceMove [WasmHeapGS Universal.State]
    {a b : UInt32} (bytes : List UInt8) (h : a = b) :
    Slices.ByteSlice (α := Universal.State) 0 a bytes ⊢
      Slices.ByteSlice 0 b bytes := by
  rw [h]

/-- The bytes in the buffer after `n` entries. -/
private def writtenAt (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (n : Nat) : List UInt8 :=
  Borsh.option Borsh.u32 o ++ Borsh.u32 (UInt32.ofNat pairs.length) ++
    Table.pairBytes (pairs.take n)

private theorem writtenAt_length (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) {n : Nat} (hn : n ≤ pairs.length) :
    (writtenAt o pairs n).length = optLen o + 4 + 8 * n := by
  unfold writtenAt optLen
  rw [List.length_append, List.length_append, Table.pairBytes_length,
    List.length_take, Nat.min_eq_left hn, Borsh.u32,
    WordCodec.u32le_encode_length]

/-- After the last entry the buffer holds the whole reply. -/
private theorem writtenAt_full (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) :
    writtenAt o pairs pairs.length =
      Borsh.option Borsh.u32 o ++
        serializeEntries WordCodec.u32le WordCodec.u32le pairs := by
  unfold writtenAt
  rw [List.take_length, serializeEntries_split, List.append_assoc]

/-- One turn appends the key word and then the value word. -/
private theorem writtenAt_succ (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) {n : Nat} (hn : n < pairs.length) :
    writtenAt o pairs (n + 1) =
      writtenAt o pairs n ++ Borsh.u32 pairs[n].1 ++
        Borsh.u32 pairs[n].2 := by
  have hstep : pairs.take (n + 1) = pairs.take n ++ [pairs[n]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hn]
    rfl
  unfold writtenAt
  rw [hstep, Table.pairBytes_append, Table.pairBytes_single]
  simp only [List.append_assoc, Borsh.u32]
  rfl

/-- Two byte offsets of a word, as the store rules ask for them. -/
private theorem addr3 (addr : UInt32) (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧ (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- The cursor after one word. -/
private theorem cursor_step (c : Nat) :
    (4 : UInt32) + UInt32.ofNat c = UInt32.ofNat (c + 4) := by
  rw [show (4 : UInt32) = UInt32.ofNat 4 from rfl, ← UInt32.ofNat_add]
  congr 1
  omega

/-- The walk pointer after one entry. -/
private theorem walk_step (p : UInt32) (n : Nat) :
    (8 : UInt32) + (p + UInt32.ofNat (8 * n))
      = p + UInt32.ofNat (8 * (n + 1)) := by
  rw [UInt32.add_comm, UInt32.add_assoc,
    show (8 : UInt32) = UInt32.ofNat 8 from rfl, ← UInt32.ofNat_add,
    show 8 * n + 8 = 8 * (n + 1) from by omega]

/-- Focus the next word of the spare region at a named cursor. -/
private theorem BufAt_word_at [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId : Nat) (buf : UInt32)
    (cap cursor : Nat) (written : List UInt8)
    (hlen : written.length = cursor) (hroom : cursor + 4 ≤ cap) :
    BufAt heapId allocationId buf cap written ⊢
      iprop(⌜(buf + UInt32.ofNat cursor).toNat + 4 < UInt32.size⌝ ∗
        ∃ w : UInt32, pointsTo_u32 0 (buf + UInt32.ofNat cursor) w ∗
        (∀ w' : UInt32,
          pointsTo_u32 0 (buf + UInt32.ofNat cursor) w' -∗
          BufAt heapId allocationId buf cap
            (written ++ Borsh.u32 w'))) := by
  subst hlen
  exact BufAt_word heapId allocationId buf cap written hroom

/-! ## The entry loop -/

/-- The index of the entry loop.  `n` counts the entries already written;
`buf` is the buffer register and `l4`, `l6` and `l7` are the registers
that one turn overwrites. -/
private structure LoopIdx where
  n : Nat
  buf : UInt32
  l4 : UInt32
  l6 : UInt32
  l7 : UInt32

/-- The resources that one turn of the entry loop keeps. -/
private def LoopInv [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr w0 : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (heapId : GName)
    (input output : List UInt8) (raised : Bool)
    (Hexit : HeapIProp) (i : LoopIdx) : HeapIProp :=
  iprop(∃ (cap allocationId : Nat) (sc : UInt32) (frontier : Nat)
      (history : AllocationHistory) (low : List UInt8),
    ⌜i.n < pairs.length ∧ 1024 ≤ cap ∧ CapFits cap frontier ∧
      frontier < 2147483648 ∧ heapBase.toNat ≤ frontier ∧
      optLen o + 4 + 8 * i.n ≤ cap ∧ low.length = 16⌝ ∗
    RuntimeContext ∗ StackPointer (sp - 16) ∗
    StackBelow (sp - 16) growDepth low ∗
    pointsTo_u32 0 (sp - 16) w0 ∗
    pointsTo_u32 0 (sp - 16 + 4) (UInt32.ofNat cap) ∗
    pointsTo_u32 0 (sp - 16 + 4 + 4) i.buf ∗
    pointsTo_u32 0 (sp - 16 + 4 + 4 + 4)
      (UInt32.ofNat (optLen o + 4 + 8 * i.n)) ∗
    BufAt heapId allocationId i.buf cap (writtenAt o pairs i.n) ∗
    BumpHeap heapId sc frontier history ∗
    Streams input output raised ∗
    Table.optionU32At 0 arg o ∗
    Slices.ByteSlice 0 (arg + 8)
      (WordCodec.u32le.serialize
        [capacity, ptr, UInt32.ofNat pairs.length]) ∗
    Table.PairSlice 0 ptr pairs ∗
    Hexit)

set_option maxHeartbeats 2000000 in
/-- The entry loop, WAT 1370 to 1457.  One turn reads the key and the
value of one entry, grows the buffer when fewer than four bytes are free,
and writes the two words. -/
private theorem twp_entryLoop [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr endPtr w0 : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (heapId : GName)
    (input output : List UInt8) (raised : Bool) (i0 : LoopIdx)
    (Hexit : HeapIProp)
    {arity : Nat} {remainder : List Value} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hoomOf : Hexit ⊢ iprop(∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage))))
    (hdoneOf : Hexit ⊢ ReplyDone sp arg capacity ptr o pairs heapId
      input output raised arity remainder calls s E Φ)
    (hsp : 32 ≤ sp.toNat)
    (hend : endPtr = ptr + UInt32.ofNat (8 * pairs.length))
    (hptr : ptr.toNat + 8 * pairs.length < UInt32.size) :
    LoopInv sp arg capacity ptr w0 o pairs heapId input output raised
        Hexit i0 ⊢
      WP (.running
          ⟨rLocals (ptr + UInt32.ofNat (8 * i0.n)) (sp - 16)
              (UInt32.ofNat (optLen o + 4 + 8 * i0.n)) i0.buf i0.l4
              endPtr i0.l6 i0.l7,
            .loop 0 0 loopBody :: mainTail, arity, remainder,
            [frame4, frame3, frame2, frame1], calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  have hspLt : sp.toNat < UInt32.size := sp.toNat_lt
  have hfbNat : (sp - 16).toNat = sp.toNat - 16 := by
    have hx := UInt32.toNat_lt sp
    simp only [UInt32.toNat_sub, show (16 : UInt32).toNat = 16 from rfl,
      UInt32.size] at *
    omega
  have hframeAddr : (sp - 16).toNat + 16 < UInt32.size := by omega
  have hdepth : 16 ≤ (sp - 16).toNat := by omega
  have hf12 := offset_facts (sp - 16) 12 12 rfl (by omega)
  iintro Hinv
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LoopIdx)
    (measure := fun i => pairs.length - i.n)
    (locals := fun i =>
      rLocals (ptr + UInt32.ofNat (8 * i.n)) (sp - 16)
        (UInt32.ofNat (optLen o + 4 + 8 * i.n)) i.buf i.l4 endPtr i.l6
        i.l7)
    (I := fun i =>
      LoopInv sp arg capacity ptr w0 o pairs heapId input output raised
        Hexit i)
    (initial := i0)
    (initialLocals :=
      rLocals (ptr + UInt32.ofNat (8 * i0.n)) (sp - 16)
        (UInt32.ofNat (optLen o + 4 + 8 * i0.n)) i0.buf i0.l4 endPtr
        i0.l6 i0.l7)
    rfl rfl
  · intro i
    iintro Hrec Hinv
    isimp only [LoopInv] at Hinv
    icases Hinv with ⟨%cap, %allocationId, %sc, %frontier, %history, %low,
      %hpure, Hruntime, Hsp, Hlow, Hw0, Hcap, Hbufptr, Hcur, Hbuf, Hbump,
      Hstreams, Hopt, Hheader, Hpairs, Hexit⟩
    obtain ⟨hn, hcap, hfits, hfrontier, hbaseLe, hcursorLe, hlow⟩ := hpure
    have hbound : 2 * cap ≤ 2147483647 := capFits_bound hfits hfrontier
    have hoptLen := optLen_bounds o
    have hwlen : (writtenAt o pairs i.n).length = optLen o + 4 + 8 * i.n :=
      writtenAt_length o pairs (by omega)
    have hcursorW :
        (UInt32.ofNat (optLen o + 4 + 8 * i.n)).toNat
          = optLen o + 4 + 8 * i.n :=
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
    simp only [Wasm.SmallStep.loopBodyExpr, loopBody, rLocals]
    icases (Table.PairSlice_at_words 0 ptr pairs hn).mp $$ Hpairs with
      ⟨Hleft, ⟨%haddr, Hkey, Hvalue⟩, Hright⟩
    have hw4 : (ptr + UInt32.ofNat (8 * i.n) + 4).toNat
        = (ptr + UInt32.ofNat (8 * i.n)).toNat + 4 := by
      simpa using
        Slices.byteOffset_toNat (ptr + UInt32.ofNat (8 * i.n)) 4
          (by omega)
    obtain ⟨hv1, hv2, hv3⟩ :=
      addr3 (ptr + UInt32.ofNat (8 * i.n) + 4) (by omega)
    obtain ⟨hk1, hk2, hk3⟩ :=
      addr3 (ptr + UInt32.ofNat (8 * i.n)) (by omega)
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (4 : UInt32) + (ptr + UInt32.ofNat (8 * i.n))
        = ptr + UInt32.ofNat (8 * i.n) + 4 from
      UInt32.add_comm 4 (ptr + UInt32.ofNat (8 * i.n))]
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr pairs[i.n].2 hv1 hv2 hv3
      with Hvalue
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr pairs[i.n].1 hk1 hk2 hk3
      with Hkey
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    ihave Hpairs := (Table.PairSlice_at_words 0 ptr pairs hn).mpr $$
      [Hleft Hkey Hvalue Hright]
    · isplitl_exact Hleft
      · isplitl [Hkey Hvalue]
        · isplitl_pureexact haddr
          · isplitl_exact Hkey
            · iexact Hvalue
        · iexact Hright
    iapply twp_growKeyBlock (sp - 16) i.buf
      (UInt32.ofNat (optLen o + 4 + 8 * i.n)) w0 cap
      (optLen o + 4 + 8 * i.n) allocationId heapId (writtenAt o pairs i.n)
      low sc frontier history input output raised Hexit hoomOf hcap hfits
      hfrontier hbaseLe hlow hcursorW hwlen (by omega) hframeAddr hdepth
    isplitl_exacts [Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump
      Hstreams Hexit]
    isimp only [GrowDone]
    iintro %buf1 %capW1 %cap1 %aid1 %sc1 %frontier1 %history1 %low1
      %hpost1 Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump Hstreams
      Hexit
    obtain ⟨hcapW1, hcap1, hfits1, hfrontier1, hbase1, hroom1, hlow1⟩ :=
      hpost1
    have hbound1 : 2 * cap1 ≤ 2147483647 := capFits_bound hfits1 hfrontier1
    subst hcapW1
    wasm_twp_pures [twp_localGet twp_localGet twp_add]
    rw [show UInt32.ofNat (optLen o + 4 + 8 * i.n) + buf1
        = buf1 + UInt32.ofNat (optLen o + 4 + 8 * i.n) from
      UInt32.add_comm _ _]
    icases BufAt_word_at heapId aid1 buf1 cap1 (optLen o + 4 + 8 * i.n)
      (writtenAt o pairs i.n) hwlen (by omega) $$ Hbuf with
      ⟨%hstore1, %oldw1, Hcell, Hclose⟩
    have ha1 := offset_facts
      (buf1 + UInt32.ofNat (optLen o + 4 + 8 * i.n)) 0 0 rfl (by omega)
    wasm_twp_pures [twp_localGet]
    ihave Hcell := wordMove32
      (UInt32.add_zero
        (buf1 + UInt32.ofNat (optLen o + 4 + 8 * i.n))).symm $$ Hcell
    wasm_twp_rebind Wasm.SmallStep.twp_store32
      (address := buf1 + UInt32.ofNat (optLen o + 4 + 8 * i.n))
      (offset := 0) oldw1 ha1.1 ha1.2.1 ha1.2.2.1 ha1.2.2.2 with Hcell
    ihave Hcell := wordMove32
      (UInt32.add_zero
        (buf1 + UInt32.ofNat (optLen o + 4 + 8 * i.n))) $$ Hcell
    ihave Hbuf := Hclose $$ %pairs[i.n].1 Hcell
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    rw [cursor_step]
    ihave Hcur := wordMove32 (addr12 (sp - 16)) $$ Hcur
    wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := sp - 16)
      (offset := 12) (UInt32.ofNat (optLen o + 4 + 8 * i.n)) hf12.1
      hf12.2.1 hf12.2.2.1 hf12.2.2.2 with Hcur
    ihave Hcur := wordMove32 (addr12 (sp - 16)).symm $$ Hcur
    have hwlen1 :
        (writtenAt o pairs i.n ++ Borsh.u32 pairs[i.n].1).length
          = optLen o + 4 + 8 * i.n + 4 := by
      rw [List.length_append, hwlen, Borsh.u32,
        WordCodec.u32le_encode_length]
    have hcursorW1 :
        (UInt32.ofNat (optLen o + 4 + 8 * i.n + 4)).toNat
          = optLen o + 4 + 8 * i.n + 4 :=
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
    iapply twp_growValueBlock (sp - 16) buf1
      (UInt32.ofNat (optLen o + 4 + 8 * i.n + 4)) w0 cap1
      (optLen o + 4 + 8 * i.n + 4) aid1 heapId
      (writtenAt o pairs i.n ++ Borsh.u32 pairs[i.n].1) low1 sc1 frontier1
      history1 input output raised Hexit hoomOf hcap1 hfits1 hfrontier1
      hbase1 hlow1 hcursorW1 hwlen1 (by omega) hframeAddr hdepth
    isplitl_exacts [Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump
      Hstreams Hexit]
    isimp only [GrowDone]
    iintro %buf2 %capW2 %cap2 %aid2 %sc2 %frontier2 %history2 %low2
      %hpost2 Hruntime Hsp Hlow Hw0 Hcap Hbufptr Hcur Hbuf Hbump Hstreams
      Hexit
    obtain ⟨hcapW2, hcap2, hfits2, hfrontier2, hbase2, hroom2, hlow2⟩ :=
      hpost2
    have hbound2 : 2 * cap2 ≤ 2147483647 := capFits_bound hfits2 hfrontier2
    subst hcapW2
    wasm_twp_pures [twp_localGet twp_localGet twp_add]
    rw [show UInt32.ofNat (optLen o + 4 + 8 * i.n + 4) + buf2
        = buf2 + UInt32.ofNat (optLen o + 4 + 8 * i.n + 4) from
      UInt32.add_comm _ _]
    icases BufAt_word_at heapId aid2 buf2 cap2
      (optLen o + 4 + 8 * i.n + 4)
      (writtenAt o pairs i.n ++ Borsh.u32 pairs[i.n].1) hwlen1
      (by omega) $$ Hbuf with ⟨%hstore2, %oldw2, Hcell, Hclose⟩
    have ha2 := offset_facts
      (buf2 + UInt32.ofNat (optLen o + 4 + 8 * i.n + 4)) 0 0 rfl
      (by omega)
    wasm_twp_pures [twp_localGet]
    ihave Hcell := wordMove32
      (UInt32.add_zero
        (buf2 + UInt32.ofNat (optLen o + 4 + 8 * i.n + 4))).symm $$ Hcell
    wasm_twp_rebind Wasm.SmallStep.twp_store32
      (address := buf2 + UInt32.ofNat (optLen o + 4 + 8 * i.n + 4))
      (offset := 0) oldw2 ha2.1 ha2.2.1 ha2.2.2.1 ha2.2.2.2 with Hcell
    ihave Hcell := wordMove32
      (UInt32.add_zero
        (buf2 + UInt32.ofNat (optLen o + 4 + 8 * i.n + 4))) $$ Hcell
    ihave Hbuf := Hclose $$ %pairs[i.n].2 Hcell
    ihave Hbuf : BufAt heapId aid2 buf2 cap2 (writtenAt o pairs (i.n + 1))
      $$ [Hbuf]
    · irw_exact [writtenAt_succ o pairs hn] with Hbuf
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    rw [cursor_step,
      show optLen o + 4 + 8 * i.n + 4 + 4 = optLen o + 4 + 8 * (i.n + 1)
        from by omega]
    ihave Hcur := wordMove32 (addr12 (sp - 16)) $$ Hcur
    wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := sp - 16)
      (offset := 12) (UInt32.ofNat (optLen o + 4 + 8 * i.n + 4)) hf12.1
      hf12.2.1 hf12.2.2.1 hf12.2.2.2 with Hcur
    ihave Hcur := wordMove32 (addr12 (sp - 16)).symm $$ Hcur
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [walk_step]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    by_cases hlast : i.n + 1 = pairs.length
    · have heq : ptr + UInt32.ofNat (8 * (i.n + 1)) = endPtr := by
        rw [hend, hlast]
      rw [heq]
      iapply Wasm.SmallStep.twp_ne (result := 0) (by simp)
      wasm_twp_pures [twp_brIfZero twp_exitControl]
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hcells :
          arrayAt 0 (sp - 16)
            [w0, UInt32.ofNat cap2, buf2,
              UInt32.ofNat (optLen o + 4 + 8 * (i.n + 1))]
          $$ [Hw0 Hcap Hbufptr Hcur]
      · isimp only [arrayAt]
        isplitl_exact Hw0
        · isplitl_exact Hcap
          · isplitl_exact Hbufptr
            · isplitl_exact Hcur
              · itrivial
      iunfold Table.PairSlice at Hpairs
      have hcap2Nat : (UInt32.ofNat cap2).toNat = cap2 :=
        UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
      have hcursorNat2 :
          (UInt32.ofNat (optLen o + 4 + 8 * (i.n + 1))).toNat
            = optLen o + 4 + 8 * (i.n + 1) :=
        UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
      have hfinal :
          (UInt32.ofNat (optLen o + 4 + 8 * (i.n + 1))).toNat
            = (writtenAt o pairs (i.n + 1)).length := by
        rw [writtenAt_length o pairs (by omega)]
        exact hcursorNat2
      have hwrittenFull : writtenAt o pairs (i.n + 1)
          = Borsh.option Borsh.u32 o ++
            serializeEntries WordCodec.u32le WordCodec.u32le pairs := by
        rw [hlast]
        exact writtenAt_full o pairs
      ihave Hdone := hdoneOf $$ Hexit
      iapply twp_main_tail sp arg capacity ptr buf2 (UInt32.ofNat cap2)
        (UInt32.ofNat (optLen o + 4 + 8 * (i.n + 1))) w0 o pairs cap2
        heapId aid2 low2 (writtenAt o pairs (i.n + 1)) sc2 frontier2
        history2 input output raised hlow2 hframeAddr hcap2Nat (by omega)
        hwrittenFull hfinal
      iframe
    · have hne : ptr + UInt32.ofNat (8 * (i.n + 1)) ≠ endPtr := by
        rw [hend]
        intro heq
        have h1 : (ptr + UInt32.ofNat (8 * (i.n + 1))).toNat
            = ptr.toNat + 8 * (i.n + 1) :=
          Slices.byteOffset_toNat ptr _ (by omega)
        have h2 : (ptr + UInt32.ofNat (8 * pairs.length)).toNat
            = ptr.toNat + 8 * pairs.length :=
          Slices.byteOffset_toNat ptr _ (by omega)
        rw [heq, h2] at h1
        omega
      iapply Wasm.SmallStep.twp_ne (result := 1) (by rw [if_pos hne])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
        (by rfl)
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hback := Hrec
        $$ %(⟨i.n + 1, buf2, UInt32.ofNat cap1, pairs[i.n].2,
            pairs[i.n].1⟩ : LoopIdx)
          %(by simp only []; omega)
      iapply Hback
      isimp only [LoopInv]
      iexists cap2, aid2, sc2, frontier2, history2, low2
      isplitl_pureexact
        (⟨by omega, by omega, hfits2, hfrontier2, hbase2, by omega,
          hlow2⟩ :
          i.n + 1 < pairs.length ∧ 1024 ≤ cap2 ∧
            CapFits cap2 frontier2 ∧ frontier2 < 2147483648 ∧
            heapBase.toNat ≤ frontier2 ∧
            optLen o + 4 + 8 * (i.n + 1) ≤ cap2 ∧ low2.length = 16)
      · iframe
  · iexact Hinv

/-! ## The count word, the empty test and the loop entry -/

/-- WAT 1348 to 1370: the count word, the cursor, the empty test and the
walk that the loop starts from. -/
@[reducible] private def countStage : Program :=
  .localGet 3 :: .localGet 2 :: .add :: .localGet 0 :: .load32 16 ::
    .localTee 4 :: .store32 0 :: .localGet 1 :: .localGet 2 ::
    .const 4 :: .add :: .localTee 2 :: .store32 12 :: .localGet 4 ::
    .eqz :: .br_if 1 :: .localGet 0 :: .load32 12 :: .localTee 0 ::
    .localGet 4 :: .const 3 :: .shl :: .add :: .localSet 5 ::
    .loop 0 0 loopBody :: mainTail

/-- The third word of the header, as one offset. -/
private theorem addr16 (b : UInt32) : b + 8 + 4 + 4 = b + 16 := by
  rw [UInt32.add_assoc, show (4 : UInt32) + 4 = 8 from by decide,
    UInt32.add_assoc, show (8 : UInt32) + 8 = 16 from by decide]

/-- The second word of the header, as one offset. -/
private theorem addr12b (b : UInt32) : b + 8 + 4 = b + 12 := by
  rw [UInt32.add_assoc, show (8 : UInt32) + 4 = 12 from by decide]

/-- Three left shifts are one multiplication by eight. -/
private theorem shl3 (n : Nat) (hn : n ≤ 2 ^ 27) :
    UInt32.ofNat n <<< ((3 : UInt32) % 32) = UInt32.ofNat (8 * n) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hpow32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hpow27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft,
    show ((3 : UInt32) % 32).toNat % 32 = 3 from by decide,
    Nat.shiftLeft_eq, show (2 : Nat) ^ 3 = 8 from by norm_num,
    UInt32.toNat_ofNat_of_lt' (by omega),
    Nat.mod_eq_of_lt (by omega),
    UInt32.toNat_ofNat_of_lt' (by omega)]
  omega

set_option maxHeartbeats 4000000 in
/-- The stage that stores the entry count, sets the cursor, takes the
empty arm when the count is zero and otherwise enters the loop. -/
private theorem twp_countStage [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr base cursorW : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (heapId : GName)
    (allocationId : Nat) (low spare : List UInt8) (f0 f3 : UInt32)
    (sc : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) {Hexit : HeapIProp}
    {l4 l5 l6 l7 : UInt32}
    {arity : Nat} {remainder : List Value} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hoomOf : Hexit ⊢ iprop(∀ remaining' : List UInt8,
      Streams remaining' output true -∗
        Φ (.trapped (.host OOM.trapMessage))))
    (hdoneOf : Hexit ⊢ ReplyDone sp arg capacity ptr o pairs heapId
      input output raised arity remainder calls s E Φ)
    (hcursorEq : cursorW = UInt32.ofNat (optLen o))
    (hsp : 32 ≤ sp.toNat)
    (hframeAddr : (sp - 16).toNat + 16 < UInt32.size)
    (hlow : low.length = 16)
    (hspare : spare.length + optLen o = 1024)
    (hbase : base ≠ 0)
    (hpairsBound : pairs.length ≤ 2 ^ 27)
    (hargNowrap : arg.toNat + 20 < UInt32.size)
    (hptrNowrap : ptr.toNat + 8 * pairs.length < UInt32.size)
    (hfits : CapFits 1024 frontier) (hfrontier : frontier < 2147483648)
    (hbaseLe : heapBase.toNat ≤ frontier) :
    iprop(RuntimeContext ∗ StackPointer (sp - 16) ∗
      StackBelow (sp - 16) growDepth low ∗
      pointsTo_u32 0 (sp - 16) f0 ∗
      pointsTo_u32 0 (sp - 16 + 4) 1024 ∗
      pointsTo_u32 0 (sp - 16 + 4 + 4) base ∗
      pointsTo_u32 0 (sp - 16 + 4 + 4 + 4) f3 ∗
      AllocToken heapId allocationId base
        { size := 1024, alignment := 1 } ∗
      Slices.ByteSlice 0 base (Borsh.option Borsh.u32 o) ∗
      Slices.ByteSlice 0 (base + UInt32.ofNat (optLen o)) spare ∗
      BumpHeap heapId sc frontier history ∗
      Streams input output raised ∗
      Table.optionU32At 0 arg o ∗
      Slices.ByteSlice 0 (arg + 8)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat pairs.length]) ∗
      Table.PairSlice 0 ptr pairs ∗
      Hexit) ⊢
      WP (.running
          ⟨rLocals arg (sp - 16) cursorW base l4 l5 l6 l7,
            countStage, arity, remainder,
            [frame4, frame3, frame2, frame1], calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hlow, Hw0, Hcap, Hbufptr, Hcur, Htoken, Hopt0,
    Hspare, Hbump, Hstreams, Hopt, Hheader, Hpairs, Hexit⟩
  subst hcursorEq
  have hpow27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have hsize : UInt32.size = 4294967296 := rfl
  have hoptLen := optLen_bounds o
  have hcursorW : (UInt32.ofNat (optLen o)).toNat = optLen o :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have ha16 := offset_facts arg 16 16 rfl (by omega)
  have ha12 := offset_facts arg 12 12 rfl (by omega)
  have hf12 := offset_facts (sp - 16) 12 12 rfl (by omega)
  ihave Hcells := cells_of_ByteSlice (arg + 8)
    [capacity, ptr, UInt32.ofNat pairs.length] $$ Hheader
  isimp only [arrayAt] at Hcells
  icases Hcells with ⟨Hcapacity, Hptrcell, Hcount, _Hnil⟩
  ihave Hcount := wordMove32 (addr16 arg) $$ Hcount
  ihave Hptrcell := wordMove32 (addr12b arg) $$ Hptrcell
  simp only [countStage, rLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_add]
  rw [show UInt32.ofNat (optLen o) + base = base + UInt32.ofNat (optLen o)
      from UInt32.add_comm _ _]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := arg) (offset := 16)
    (UInt32.ofNat pairs.length) ha16.1 ha16.2.1 ha16.2.2.1 ha16.2.2.2
    with Hcount
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  icases (slice_split (base + UInt32.ofNat (optLen o)) 4 spare
    (by omega)).mp $$ Hspare with ⟨Hhead, Htail⟩
  icases slice_as_word (base + UInt32.ofNat (optLen o)) (spare.take 4)
    (by rw [List.length_take]; omega) $$ Hhead with
    ⟨%hwbound, %oldw, Hcell⟩
  have hc0 := offset_facts (base + UInt32.ofNat (optLen o)) 0 0 rfl
    (by omega)
  ihave Hcell := wordMove32
    (UInt32.add_zero (base + UInt32.ofNat (optLen o))).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store32
    (address := base + UInt32.ofNat (optLen o)) (offset := 0) oldw
    hc0.1 hc0.2.1 hc0.2.2.1 hc0.2.2.2 with Hcell
  ihave Hcell := wordMove32
    (UInt32.add_zero (base + UInt32.ofNat (optLen o))) $$ Hcell
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  rw [cursor_step (optLen o)]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  ihave Hcur := wordMove32 (addr12 (sp - 16)) $$ Hcur
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := sp - 16)
    (offset := 12) f3 hf12.1 hf12.2.1 hf12.2.2.1 hf12.2.2.2 with Hcur
  ihave Hcur := wordMove32 (addr12 (sp - 16)).symm $$ Hcur
  -- the buffer now holds the option and the count
  have hwritten0 : writtenAt o pairs 0
      = Borsh.option Borsh.u32 o ++
        Borsh.u32 (UInt32.ofNat pairs.length) := by
    unfold writtenAt
    rw [List.take_zero, Table.pairBytes_nil, List.append_nil]
  have hwlen0 : (writtenAt o pairs 0).length = optLen o + 4 := by
    rw [writtenAt_length o pairs (by omega)]
  ihave Hcountslice := word_as_slice (base + UInt32.ofNat (optLen o))
    (UInt32.ofNat pairs.length) hwbound $$ Hcell
  ihave Hbuf : BufAt heapId allocationId base 1024 (writtenAt o pairs 0)
    $$ [Htoken Hopt0 Hcountslice Htail]
  · iunfold BufAt
    iexists (spare.drop 4)
    isplitl_pureexact
      (⟨by rw [hwlen0, List.length_drop]; omega, hbase⟩ :
        (writtenAt o pairs 0).length + (spare.drop 4).length = 1024 ∧
          base ≠ 0)
    · isplitl_exact Htoken
      · isplitl [Hopt0 Hcountslice]
        · rw [hwritten0]
          iapply (Slices.ByteSlice_append (α := Universal.State) 0 base
            (Borsh.option Borsh.u32 o)
            (Borsh.u32 (UInt32.ofNat pairs.length))).mpr
          isplitl_exact Hopt0
          · irw_exact
              [show (Borsh.option Borsh.u32 o).length = optLen o from rfl]
              with Hcountslice
        · irw_exact
            [show base + UInt32.ofNat (optLen o) + UInt32.ofNat 4
                = base + UInt32.ofNat (writtenAt o pairs 0).length from by
              rw [addr_step, hwlen0]]
            with Htail
  by_cases hzero : pairs.length = 0
  · -- the empty arm, WAT 1359 to 1361 and 1476 to 1480
    have hcountZero : UInt32.ofNat pairs.length = 0 := by
      rw [hzero]
      rfl
    wasm_twp_pures [twp_localGet]
    iapply Wasm.SmallStep.twp_eqz (result := 1) (by rw [if_pos hcountZero])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave Hdone := hdoneOf $$ Hexit
    ihave Hptrcell := wordMove32 (addr12b arg).symm $$ Hptrcell
    ihave Hcount := wordMove32 (addr16 arg).symm $$ Hcount
    ihave Hheader :
        Slices.ByteSlice 0 (arg + 8)
          (WordCodec.u32le.serialize
            [capacity, ptr, UInt32.ofNat pairs.length])
        $$ [Hcapacity Hptrcell Hcount]
    · iapply ByteSlice_of_cells (arg + 8)
        [capacity, ptr, UInt32.ofNat pairs.length]
        (by
          have hx : (arg + 8).toNat = arg.toNat + 8 :=
            Slices.byteOffset_toNat arg 8 (by omega)
          simp only [List.length_cons, List.length_nil]
          omega)
      isimp only [arrayAt]
      isplitl_exact Hcapacity
      · isplitl_exact Hptrcell
        · isplitl_exact Hcount
          · itrivial
    ihave Hcells :
        arrayAt 0 (sp - 16)
          [f0, 1024, base, UInt32.ofNat (optLen o + 4)]
        $$ [Hw0 Hcap Hbufptr Hcur]
    · isimp only [arrayAt]
      isplitl_exact Hw0
      · isplitl_exact Hcap
        · isplitl_exact Hbufptr
          · isplitl_exact Hcur
            · itrivial
    ihave Hframe := ByteSlice_of_cells (sp - 16)
      [f0, 1024, base, UInt32.ofNat (optLen o + 4)]
      (by simpa using hframeAddr) $$ Hcells
    iunfold Table.PairSlice at Hpairs
    have hwrittenFull : writtenAt o pairs 0
        = Borsh.option Borsh.u32 o ++
          serializeEntries WordCodec.u32le WordCodec.u32le pairs := by
      rw [← hzero]
      exact writtenAt_full o pairs
    have hcursorFull : (UInt32.ofNat (optLen o + 4)).toNat
        = (writtenAt o pairs 0).length := by
      rw [hwlen0, UInt32.toNat_ofNat_of_lt' (by omega)]
    iapply twp_empty_tail sp arg capacity ptr base
      (UInt32.ofNat (optLen o + 4)) o pairs heapId allocationId low
      (WordCodec.u32le.serialize
        [f0, 1024, base, UInt32.ofNat (optLen o + 4)])
      (writtenAt o pairs 0) sc frontier history input output raised hlow
      (by rw [WordCodec.u32le_serialize_length]; rfl) hwrittenFull
      hcursorFull
    iframe
  · -- the entry loop, WAT 1362 to 1370
    have hcountNe : UInt32.ofNat pairs.length ≠ 0 := by
      intro hnull
      apply hzero
      have hx := congrArg UInt32.toNat hnull
      rw [UInt32.toNat_ofNat_of_lt' (by omega),
        show (0 : UInt32).toNat = 0 from rfl] at hx
      exact hx
    wasm_twp_pures [twp_localGet]
    iapply Wasm.SmallStep.twp_eqz (result := 0) (by rw [if_neg hcountNe])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := arg) (offset := 12) ptr
      ha12.1 ha12.2.1 ha12.2.2.1 ha12.2.2.2 with Hptrcell
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_const twp_shl]
    rw [shl3 pairs.length hpairsBound]
    wasm_twp_pures [twp_add]
    rw [show UInt32.ofNat (8 * pairs.length) + ptr
        = ptr + UInt32.ofNat (8 * pairs.length) from UInt32.add_comm _ _]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    ihave Hptrcell := wordMove32 (addr12b arg).symm $$ Hptrcell
    ihave Hcount := wordMove32 (addr16 arg).symm $$ Hcount
    ihave Hheader :
        Slices.ByteSlice 0 (arg + 8)
          (WordCodec.u32le.serialize
            [capacity, ptr, UInt32.ofNat pairs.length])
        $$ [Hcapacity Hptrcell Hcount]
    · iapply ByteSlice_of_cells (arg + 8)
        [capacity, ptr, UInt32.ofNat pairs.length]
        (by
          have hx : (arg + 8).toNat = arg.toNat + 8 :=
            Slices.byteOffset_toNat arg 8 (by omega)
          simp only [List.length_cons, List.length_nil]
          omega)
      isimp only [arrayAt]
      isplitl_exact Hcapacity
      · isplitl_exact Hptrcell
        · isplitl_exact Hcount
          · itrivial
    have Hloop := twp_entryLoop sp arg capacity ptr
      (ptr + UInt32.ofNat (8 * pairs.length)) f0 o pairs heapId input
      output raised
      (⟨0, base, UInt32.ofNat pairs.length, l6, l7⟩ : LoopIdx) Hexit
      hoomOf hdoneOf hsp rfl hptrNowrap
    simp only [] at Hloop
    rw [show (8 : Nat) * 0 = 0 from rfl, Nat.add_zero,
      show UInt32.ofNat 0 = (0 : UInt32) from rfl, UInt32.add_zero]
      at Hloop
    iapply Hloop
    isimp only [LoopInv]
    iexists 1024, allocationId, sc, frontier, history, low
    isplitl_pureexact
      (⟨by omega, by omega, hfits, hfrontier, hbaseLe, by omega, hlow⟩ :
        0 < pairs.length ∧ 1024 ≤ 1024 ∧ CapFits 1024 frontier ∧
          frontier < 2147483648 ∧ heapBase.toNat ≤ frontier ∧
          optLen o + 4 + 8 * 0 ≤ 1024 ∧ low.length = 16)
    · iframe

set_option maxHeartbeats 2000000 in
/-- The normal arm of the contract, as the continuation that every path
of the body ends with.  The return step of WAT 1490 turns the empty code
of the callee into the resume of the caller. -/
private theorem exit_arms [WasmSmallStepGS hlc Universal.State]
    (sp arg capacity ptr : UInt32) (o : Option UInt32)
    (pairs : List (UInt32 × UInt32)) (heapId : GName)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) :
    (iprop((∀ below' : List UInt8, ∀ storedCursor' : UInt32,
          ∀ frontier' : Nat, ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp replyDepth below' -∗
          Table.optionU32At 0 arg o -∗
          Slices.ByteSlice 0 (arg + 8)
            (WordCodec.u32le.serialize
              [capacity, ptr, UInt32.ofNat pairs.length]) -∗
          Slices.ByteSlice 0 ptr (Table.pairBytes pairs) -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input (output ++ Borsh.option Borsh.u32 o ++
            serializeEntries WordCodec.u32le WordCodec.u32le pairs)
            raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls
            calls s E Φ) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage)))) ⊢
      iprop(∀ remaining' : List UInt8,
        Streams remaining' output true -∗
          Φ (.trapped (.host OOM.trapMessage)))) ∧
    (iprop((∀ below' : List UInt8, ∀ storedCursor' : UInt32,
          ∀ frontier' : Nat, ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp replyDepth below' -∗
          Table.optionU32At 0 arg o -∗
          Slices.ByteSlice 0 (arg + 8)
            (WordCodec.u32le.serialize
              [capacity, ptr, UInt32.ofNat pairs.length]) -∗
          Slices.ByteSlice 0 ptr (Table.pairBytes pairs) -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input (output ++ Borsh.option Borsh.u32 o ++
            serializeEntries WordCodec.u32le WordCodec.u32le pairs)
            raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls
            calls s E Φ) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage)))) ⊢
      ReplyDone sp arg capacity ptr o pairs heapId input output raised 0
        []
        ({ locals := ⟨callerLocals.params, callerLocals.locals, stack⟩,
            continuation := code, resultArity := arity,
            callerRemainder := remainder, control := controls,
            returningInstance := ⟨0⟩ } :: calls) s E Φ) := by
  refine ⟨BI.and_elim_r, BI.and_elim_l.trans ?_⟩
  iintro Hnormal
  isimp only [ReplyDone]
  iintro %finalLocals %below' %sc' %frontier' %history' Hruntime Hsp
    Hbelow Hopt Hheader Hpairs Hbump Hstreams
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  iclose_map_runtime Hruntime with Hmodule Henv
  ihave Hnormal := Hnormal $$ %below' %sc' %frontier' %history'
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
  iapply Hnormal $$ Hruntime Hsp Hbelow Hopt Hheader Hpairs Hbump Hstreams

/-! ## The body -/

set_option maxHeartbeats 4000000 in
/-- Absolute `func 8`, local `func5`, the borsh reply writer. -/
theorem func5_correct [WasmSmallStepGS hlc Universal.State] :
    Func5Spec (hlc := hlc) := by
  unfold Func5Spec CallContract callExpr
  intro sp arg capacity ptr o pairs below heapId storedCursor frontier
    history input output raised callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hopt, Hheader, Hpairs, Hbump, Hstreams,
    %hfacts, Hcont⟩
  obtain ⟨hpairsBound, hspLow, hargNowrap, hptrNowrap⟩ := hfacts
  have hdeep : replyDepth = 32 := rfl
  have hspLt : sp.toNat < UInt32.size := sp.toNat_lt
  have hsp32 : 32 ≤ sp.toNat := by rw [hdeep] at hspLow; exact hspLow
  have hfbNat : (sp - 16).toNat = sp.toNat - 16 := by
    simp only [UInt32.toNat_sub, show (16 : UInt32).toNat = 16 from rfl,
      UInt32.size] at *
    omega
  have hframeAddr : (sp - 16).toNat + 16 < UInt32.size := by
    simp only [UInt32.size] at *
    omega
  have hdepth : 16 ≤ (sp - 16).toNat := by omega
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 8
      Project.RustHashMap.func5Def (by decide) func5_index with Hmodule
  simp only [Project.RustHashMap.func5Def, Function.toLocals,
    Function.numParams, List.take_succ_cons, List.take_zero,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, ValueType.zero]
  rw [func5_shape]
  iclose_map_runtime Hruntime with Hmodule Henv
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer (sp - 16) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  have Hmark : Project.RustHashMap.VecGrow.Func30Spec (hlc := hlc) :=
    Project.RustHashMap.Func30Proof.func30_correct
  unfold Project.RustHashMap.VecGrow.Func30Spec CallContract callExpr
    at Hmark
  simp only [List.nil_append] at Hmark
  iapply Hmark
    (callerLocals :=
      ⟨[Value.i32 arg], [.i32 (sp - 16), .i32 0, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0], []⟩)
    (stack := [])
  isplitl_exact Hruntime
  · iintro Hruntime
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    iapply twp_block
    simp only [List.drop_zero, block1]
    iapply twp_block
    simp only [List.drop_zero, block2]
    iapply twp_block
    simp only [List.drop_zero, block3]
    iapply twp_block
    simp only [List.drop_zero, block4]
    -- the stack frame and its four cells
    icases below_frame_split sp below $$ Hbelow with
      ⟨%hbelowLen, Hlow, Hframe⟩
    have hlowLen : (below.take 16).length = 16 := by
      rw [List.length_take]
      omega
    have hframeLen : (below.drop 16).length = 16 := by
      rw [List.length_drop]
      omega
    icases ByteSlice_as_cells (sp - 16) (below.drop 16) 4
      (by rw [hframeLen]) $$ Hframe with ⟨%hwordsLen, Hcells⟩
    obtain ⟨f0, f1, f2, f3, hfshape⟩ :=
      four_words (Slices.decodeWords (below.drop 16)) hwordsLen
    isimp only [hfshape, arrayAt] at Hcells
    icases Hcells with ⟨Hw0, Hcap, Hbufptr, Hcur, _Hnil⟩
    have hf4 := offset_facts (sp - 16) 4 4 rfl (by omega)
    have hf8 := offset_facts (sp - 16) 8 8 rfl (by omega)
    have hf12 := offset_facts (sp - 16) 12 12 rfl (by omega)
    icases bumpHeap_bounds heapId storedCursor frontier history $$ Hbump
      with ⟨Hbump, %hbumpFacts⟩
    -- the allocation of the reply buffer, WAT 1314 to 1316
    wasm_twp_pures [twp_const twp_const]
    have Halloc : Func55Spec (hlc := hlc) :=
      Project.RustHashMap.Func55Proof.func55_correct
    unfold Func55Spec CallContract callExpr at Halloc
    simp only [List.cons_append, List.nil_append] at Halloc
    iapply Halloc (size := 1024) (alignment := 1)
      (layout := { size := 1024, alignment := 1 }) (heapId := heapId)
      (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals :=
        ⟨[Value.i32 arg], [.i32 (sp - 16), .i32 1, .i32 0, .i32 0, .i32 0,
          .i32 0, .i32 0], []⟩)
      (stack := [])
    isplitl_exact Hruntime
    isplitl_exacts [Hbump Hstreams]
    have hlayoutFacts :
        AllocLayout.Matches { size := 1024, alignment := 1 } 1024 1 ∧
          AllocLayout.Valid { size := 1024, alignment := 1 } ∧
          ((1 : Nat) = 1 ∨ (1 : Nat) = 4) :=
      ⟨⟨rfl, rfl⟩, buffer_layout_valid (by omega) (by omega), Or.inl rfl⟩
    isplitl_pureexact hlayoutFacts
    unfold AllocContinuation
    cases hdecision :
        classifyBump frontier
          ({ size := 1024, alignment := 1 } : AllocLayout) with
    | oom =>
        iintro Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        ihave Hoom := Hoom $$ %input
        iapply Hoom $$ Hstreams
    | success base finish =>
        obtain ⟨hfrontLt, hbaseEq, hbaseNat, hendWord, hendSigned,
          hfinishNat⟩ :=
          classifyBump_success_align1 frontier 1024 base finish hdecision
        isplit
        · iintro %allocBytes Hruntime Hbump Hblock Hstreams
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          simp only [List.cons_append, List.nil_append]
          icases liveBlock_nonzero heapId history.nextId base
            { size := 1024, alignment := 1 } allocBytes $$ Hblock with
            ⟨%hbaseNonzero, Hblock⟩
          icases liveBlock_length heapId history.nextId base
            { size := 1024, alignment := 1 } allocBytes $$ Hblock with
            ⟨%hallocLen, Hblock⟩
          have hcapFits : CapFits 1024 finish.toNat :=
            capFits_start hbumpFacts.1 hfinishNat
          wasm_twp_localTee [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          iapply twp_eqz (result := 0) (by simp [hbaseNonzero])
          wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet]
          ihave Hbufptr := wordMove32 (addr4 (sp - 16)) $$ Hbufptr
          wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 8)
            f2 hf8.1 hf8.2.1 hf8.2.2.1 hf8.2.2.2 with Hbufptr
          wasm_twp_pures [twp_localGet twp_const]
          wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 4)
            f1 hf4.1 hf4.2.1 hf4.2.2.1 hf4.2.2.2 with Hcap
          wasm_twp_pures [twp_const]
          wasm_twp_localSet [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          -- the two exits of the body
          obtain ⟨hoomOf, hdoneOf⟩ :=
            exit_arms sp arg capacity ptr o pairs heapId input output
              raised callerLocals stack code arity remainder controls
              calls s E Φ
          -- the bytes of the fresh buffer
          iunfold LiveBlock at Hblock
          icases Hblock with ⟨Htoken, Hbytes, %hbfacts⟩
          icases slice_bound base allocBytes $$ Hbytes with
            ⟨%hbaseBound, Hbytes⟩
          have hallocNat : allocBytes.length = 1024 := hallocLen
          have hbb : base.toNat + 1024 < UInt32.size := by
            rw [hallocNat] at hbaseBound
            exact hbaseBound
          have ha0 := addr3 arg (by omega)
          have ha4 := offset_facts arg 4 4 rfl (by omega)
          icases (slice_split base 1 allocBytes (by omega)).mp $$ Hbytes
            with ⟨Hb0, Hrest⟩
          obtain ⟨b0, hb0⟩ :=
            one_byte (allocBytes.take 1) (by rw [List.length_take]; omega)
          isimp only [hb0] at Hb0
          icases (slice_as_byte base b0).mp $$ Hb0 with ⟨%_hb0, Hbyte⟩
          ihave Hpairs : Table.PairSlice 0 ptr pairs $$ [Hpairs]
          · iunfold Table.PairSlice
            iexact Hpairs
          ihave Hbufptr := wordMove32 (addr4 (sp - 16)).symm $$ Hbufptr
          iapply twp_block
          simp only [List.drop_zero, optBlock]
          cases o with
          | none =>
              isimp only [Table.optionU32At] at Hopt
              icases Hopt with ⟨%pad, Htag, Hpad⟩
              wasm_twp_pures [twp_localGet]
              wasm_twp_rebind Wasm.SmallStep.twp_load32_addr (0 : UInt32)
                ha0.1 ha0.2.1 ha0.2.2 with Htag
              wasm_twp_pures [twp_const]
              iapply Wasm.SmallStep.twp_ne (result := 1)
                (by rw [if_pos (by decide : (0 : UInt32) ≠ 1)])
              iapply Wasm.SmallStep.twp_brIf
                (by decide : (1 : UInt32) ≠ 0) (by rfl)
              simp only [List.take_zero, List.nil_append]
              wasm_twp_pures [twp_localGet twp_localGet]
              wasm_twp_rebind Wasm.SmallStep.twp_store8_addr_gen b0
                with Hbyte
              ihave Hopt0 :
                  Slices.ByteSlice 0 base
                    (Borsh.option Borsh.u32 (none : Option UInt32))
                  $$ [Hbyte]
              · rw [show Borsh.option Borsh.u32 (none : Option UInt32)
                      = [(0 : UInt32).toUInt8] from rfl]
                iapply (slice_as_byte base ((0 : UInt32).toUInt8)).mpr
                isplitl_pureexact (by omega : base.toNat + 1 < UInt32.size)
                · iexact Hbyte
              ihave Hrest := sliceMove (allocBytes.drop 1)
                (show base + UInt32.ofNat 1
                    = base + UInt32.ofNat (optLen (none : Option UInt32))
                  from by rw [optLen_none]) $$ Hrest
              ihave Hopt : Table.optionU32At 0 arg (none : Option UInt32)
                $$ [Htag Hpad]
              · isimp only [Table.optionU32At]
                iexists pad
                isplitl_exact Htag
                · iexact Hpad
              iapply twp_countStage sp arg capacity ptr base 1
                (none : Option UInt32) pairs heapId history.nextId
                (below.take 16) (allocBytes.drop 1) f0 f3 finish
                finish.toNat
                (history.allocate base { size := 1024, alignment := 1 })
                input output raised hoomOf hdoneOf
                (by rw [optLen_none]; rfl) (by omega) hframeAddr hlowLen
                (by rw [List.length_drop, optLen_none]; omega)
                hbaseNonzero hpairsBound hargNowrap hptrNowrap hcapFits
                (by omega) (by omega)
              iframe
          | some v =>
              isimp only [Table.optionU32At] at Hopt
              icases Hopt with ⟨Htag, Hpayload⟩
              wasm_twp_pures [twp_localGet]
              wasm_twp_rebind Wasm.SmallStep.twp_load32_addr (1 : UInt32)
                ha0.1 ha0.2.1 ha0.2.2 with Htag
              wasm_twp_pures [twp_const]
              iapply Wasm.SmallStep.twp_ne (result := 0)
                (by rw [if_neg (by simp)])
              wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet]
              wasm_twp_rebind twp_load32 (address := arg) (offset := 4) v
                ha4.1 ha4.2.1 ha4.2.2.1 ha4.2.2.2 with Hpayload
              have hrestLen : (allocBytes.drop 1).length = 1023 := by
                rw [List.length_drop]
                omega
              icases (slice_split (base + UInt32.ofNat 1) 4
                (allocBytes.drop 1) (by omega)).mp $$ Hrest with
                ⟨Hhead, Htail⟩
              icases slice_as_word (base + UInt32.ofNat 1)
                ((allocBytes.drop 1).take 4)
                (by rw [List.length_take]; omega) $$ Hhead with
                ⟨%hwb, %oldw, Hcell⟩
              have hb1 := offset_facts base 1 1 rfl (by omega)
              ihave Hcell := wordMove32
                (show base + UInt32.ofNat 1 = base + 1 from rfl) $$ Hcell
              wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := base)
                (offset := 1) oldw hb1.1 hb1.2.1 hb1.2.2.1 hb1.2.2.2
                with Hcell
              ihave Hcell := wordMove32
                (show base + 1 = base + UInt32.ofNat 1 from rfl) $$ Hcell
              wasm_twp_pures [twp_const]
              wasm_twp_localSet [List.length_cons, List.length_nil,
                Nat.reduceAdd, Nat.reduceSub, List.set]
              wasm_twp_pures [twp_const]
              wasm_twp_localSet [List.length_cons, List.length_nil,
                Nat.reduceAdd, Nat.reduceSub, List.set]
              wasm_twp_pures [twp_exitControl]
              simp only [List.take_zero, List.nil_append]
              wasm_twp_pures [twp_localGet twp_localGet]
              wasm_twp_rebind Wasm.SmallStep.twp_store8_addr_gen b0
                with Hbyte
              ihave Hpay := word_as_slice (base + UInt32.ofNat 1) v hwb
                $$ Hcell
              ihave Hopt0 :
                  Slices.ByteSlice 0 base
                    (Borsh.option Borsh.u32 (some v))
                  $$ [Hbyte Hpay]
              · rw [show Borsh.option Borsh.u32 (some v)
                      = [(1 : UInt32).toUInt8] ++ Borsh.u32 v from rfl]
                iapply (Slices.ByteSlice_append (α := Universal.State) 0
                  base [(1 : UInt32).toUInt8] (Borsh.u32 v)).mpr
                isplitl [Hbyte]
                · iapply (slice_as_byte base ((1 : UInt32).toUInt8)).mpr
                  isplitl_pureexact
                    (by omega : base.toNat + 1 < UInt32.size)
                  · iexact Hbyte
                · irw_exact
                    [show base + UInt32.ofNat
                        ([(1 : UInt32).toUInt8] : List UInt8).length
                        = base + UInt32.ofNat 1 from rfl]
                    with Hpay
              ihave Hopt : Table.optionU32At 0 arg (some v)
                $$ [Htag Hpayload]
              · isimp only [Table.optionU32At]
                isplitl_exact Htag
                · iexact Hpayload
              ihave Htail := sliceMove ((allocBytes.drop 1).drop 4)
                (show base + UInt32.ofNat 1 + UInt32.ofNat 4
                    = base + UInt32.ofNat (optLen (some v)) from by
                  rw [addr_step, optLen_some]) $$ Htail
              iapply twp_countStage sp arg capacity ptr base 5
                (some v) pairs heapId history.nextId (below.take 16)
                ((allocBytes.drop 1).drop 4) f0 f3 finish finish.toNat
                (history.allocate base { size := 1024, alignment := 1 })
                input output raised hoomOf hdoneOf
                (by rw [optLen_some]; rfl) (by omega) hframeAddr hlowLen
                (by
                  rw [List.length_drop, List.length_drop, optLen_some]
                  omega)
                hbaseNonzero hpairsBound hargNowrap hptrNowrap hcapFits
                (by omega) (by omega)
              iframe
        · iintro Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          ihave Hoom := Hoom $$ %input
          iapply Hoom $$ Hstreams

end Project.RustHashMap.Func5Proof
