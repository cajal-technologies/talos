import Project.RustHashMap.RemoveRead
import Project.RustHashMap.KeyDecoderContract
import Project.RustHashMap.CollectContract
import Project.RustHashMap.EntriesContracts

/-!
# The tail of the `map_remove` driver: program fragments

The `map_remove` driver is local `func6`, absolute index 9.  The read
phase of the driver is proved in `Project.RustHashMap.RemoveRead`.  This
file splits the code after the read phase into one definition per control
block, so that the proof of the tail can name each block.

The whole driver is WAT lines 1492 to 1740 of
`programs/rust/build/rust_hash_map/program.wat`.  The tail is WAT lines
1597 to 1739.  The tail does these steps:

1. It calls the key decoder, absolute `func 10`, with the 20-byte output
   slot at frame offset 16, the input pointer in local 3 and the input
   length in local 1.
2. It reads the tag word of the output slot.  A tag of zero means `Ok`.
   Any other tag means `Err`, and the code jumps to the error arm.
3. On `Ok` it copies the decoded map header into the entries vector
   header, moves the leading key into local 1, frees the input buffer,
   and calls `collect_entries`, absolute `func 5`, with the 32-byte map
   slot.
4. It calls the remove kernel, absolute `func 11`, with a 40-byte output
   slot at frame offset 64.  The kernel writes the removed value as an
   `Option<u32>` at offsets 64 to 72 and the new map value at offsets 72
   to 104.
5. It saves the option word in local 5 and copies the new map value back
   over the map slot, one 64-bit word at a time, from the top down.
6. It calls `sorted_entries`, absolute `func 7`, with a 12-byte output
   slot at frame offset 72, restores the option word at offset 64, and
   calls the reply writer, absolute `func 8`, with the 20-byte record at
   offsets 64 to 84.
7. It frees the pair buffer, drops the hash table, and restores the stack
   pointer.

The frame holds 320 bytes.  The regions are these, as offsets from the
frame base:

| region                          | offsets    |
|---------------------------------|------------|
| entries vec header for `call 5` | 0 to 12    |
| `call 10` out slot              | 16 to 36   |
| map slot, which overlays it     | 16 to 48   |
| input vec header                | 52 to 64   |
| `call 11` out slot              | 64 to 104  |
| `call 7` out header             | 72 to 84   |
| 256-byte chunk buffer           | 64 to 320  |

The read phase leaves the chunk buffer at offsets 64 to 320.  The tail
reuses its first 40 bytes as the output slot of the remove kernel and
never reads the rest.

The tail has two exits.  The reject exit frees the decoded error and the
input buffer, and it writes nothing.  The accept exit writes the removed
value and the map that remains.  There is no `unreachable` and no
allocator failure arm in this function, because every allocation sits
inside a callee.

The constants keep the unsigned form that the Lean AST uses: `i32.const
-8` is `4294967288`.  The AST drops the alignment of a load or a store,
so `i64.load offset=24 align=4` is `load64 24`.
-/

namespace Project.RustHashMap.RemoveTailDefs

open Wasm
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.EntriesContracts
open Project.RustHashMap.RemoveRead

/-! ## The stack that the callees take -/

/-- The deepest stack that a callee of the remove tail takes below the
driver frame.  `sorted_entries`, absolute `func 7`, takes the most,
because it sorts the entries, so this is `serializeDepth`. -/
def removeCalleeDepth : Nat := serializeDepth

theorem removeCalleeDepth_serialize :
    serializeDepth = removeCalleeDepth := rfl

theorem removeCalleeDepth_eq : removeCalleeDepth = 14096 := rfl

/-- The read phase keeps sixteen bytes of `StackReserve`, so the tail
carries the rest of the region as one slice. -/
theorem removeExtra_eq : removeCalleeDepth - 16 = 14080 := by decide

theorem keyDecoderDepth_le_remove :
    keyDecoderDepth ≤ removeCalleeDepth := by decide

theorem collectDepth_le_remove : collectDepth ≤ removeCalleeDepth := by
  decide

theorem replyDepth_le_remove : replyDepth ≤ removeCalleeDepth := by
  decide

theorem errorNewDepth_le_remove :
    errorNewDepth ≤ removeCalleeDepth := by decide

/-- A table holds at most `2 ^ 27` buckets, so the sort of the entries
stays inside the region that the tail carries. -/
theorem sortedEntriesDepth_le_remove {items : Nat}
    (hitems : items ≤ 2 ^ 27) :
    sortedEntriesDepth items ≤ removeCalleeDepth :=
  sortedEntriesDepth_le_serialize hitems

/-- The stack that `map_remove` takes: its own 320-byte frame and the
region that its callees take below it. -/
def removeDepth : Nat := 320 + removeCalleeDepth

theorem removeDepth_eq : removeDepth = 14416 := rfl

theorem removeDepth_le : removeDepth ≤ entryStackTop.toNat := by decide

/-- The base of the region that the tail carries.  The driver frame base
is 1048256, and the callee region ends 14096 bytes below it. -/
theorem func6Base_sub_depth :
    func6Base - UInt32.ofNat removeCalleeDepth = 1034160 := by decide

/-! ## The blocks of the tail, from the innermost outward -/

/-- The release of the input byte vector before the collect call.  A
capacity of zero leaves nothing to free.  WAT lines 1620 to 1626. -/
@[reducible] def rmFreeInput : Program :=
  [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1,
    .call 60]

/-- The copy of the decoded map header into the entries vector header at
frame offset 0, and the move of the leading key into local 1.  The
capacity and the pointer travel as one 64-bit word.  WAT lines 1608 to
1618. -/
@[reducible] def rmAcceptCopy : Program :=
  [.localGet 0, .localGet 0, .load64 24, .store64 0, .localGet 0,
    .localGet 0, .load32 32, .store32 8, .localGet 0, .load32 20,
    .localSet 1]

/-- The call of `collect_entries`, absolute `func 5`.  It takes the
32-byte map slot at frame offset 16 and the entries vector header at
frame offset 0.  WAT lines 1628 to 1632. -/
@[reducible] def rmCollect : Program :=
  [.localGet 0, .const 16, .add, .localGet 0, .call 5]

/-- The call of the remove kernel, absolute `func 11`.  It takes the
40-byte output slot at frame offset 64, the map slot at frame offset 16
and the key in local 1.  The option word of the answer goes to local
5.  WAT lines 1633 to 1643. -/
@[reducible] def rmRemove : Program :=
  [.localGet 0, .const 64, .add, .localGet 0, .const 16, .add,
    .localGet 1, .call 11, .localGet 0, .load64 64, .localSet 5]

/-- The copy of the new map value back over the map slot.  The four
64-bit words move from the top down, so the source and the target never
overlap in the wrong order.  WAT lines 1644 to 1659. -/
@[reducible] def rmCopyBack : Program :=
  [.localGet 0, .localGet 0, .load64 96, .store64 40,
    .localGet 0, .localGet 0, .load64 88, .store64 32,
    .localGet 0, .localGet 0, .load64 80, .store64 24,
    .localGet 0, .localGet 0, .load64 72, .store64 16]

/-- The call of `sorted_entries`, absolute `func 7`.  It takes the
12-byte output header at frame offset 72 and the map slot at frame offset
16.  WAT lines 1660 to 1666. -/
@[reducible] def rmSort : Program :=
  [.localGet 0, .const 72, .add, .localGet 0, .const 16, .add, .call 7]

/-- The call of the reply writer, absolute `func 8`.  The store puts the
option word back at frame offset 64, so the record at offsets 64 to 84
holds the option and then the pair buffer header.  WAT lines 1667 to
1673. -/
@[reducible] def rmReply : Program :=
  [.localGet 0, .localGet 5, .store64 64, .localGet 0, .const 64, .add,
    .call 8]

/-- The release of the pair buffer that `sorted_entries` allocated.  The
entry count sits at frame offset 72 and the pointer at frame offset 76.
A count of zero leaves nothing to free.  WAT lines 1675 to 1686. -/
@[reducible] def rmFreePairs : Program :=
  [.localGet 0, .load32 72, .localTee 1, .eqz, .br_if 0, .localGet 0,
    .load32 76, .localGet 1, .const 3, .shl, .const 4, .call 60]

/-- The drop of the hash table.  The bucket count sits at map offset 4
and the control pointer at map offset 0, which are frame offsets 20 and
16.  A bucket count of zero leaves nothing to free, and so does a total
size of zero.  Both guards leave the outer block.  WAT lines 1688 to
1713. -/
@[reducible] def rmTableDrop : Program :=
  [.localGet 0, .load32 20, .localTee 1, .eqz, .br_if 1, .localGet 1,
    .const 3, .shl, .localTee 3, .localGet 1, .add, .const 17, .add,
    .localTee 1, .eqz, .br_if 1, .localGet 0, .load32 16, .localGet 3,
    .sub, .const 4294967288, .add, .localGet 1, .const 8, .call 60, .br 1]

/-- The accept arm.  The guard reads the tag word at frame offset 16, and
a tag that is not zero leaves the arm.  The arm then copies the header,
frees the input, builds the table with `call 5`, removes the key with
`call 11`, copies the new map back, sorts the entries with `call 7`,
writes the reply with `call 8`, frees the pair buffer, and drops the
table.  WAT lines 1605 to 1713. -/
@[reducible] def rmOkArm : Program :=
  [.localGet 0, .load32 16, .br_if 0] ++ rmAcceptCopy ++
    .block 0 0 rmFreeInput ::
      (rmCollect ++ rmRemove ++ rmCopyBack ++ rmSort ++ rmReply ++
        .block 0 0 rmFreePairs :: rmTableDrop)

/-- The drop of the decoded error string.  A length below one carries no
allocation, so nothing is freed.  WAT lines 1716 to 1726. -/
@[reducible] def rmDropError : Program :=
  [.localGet 0, .load32 20, .localTee 1, .const 1, .ltS, .br_if 0,
    .localGet 0, .load32 24, .localGet 1, .const 1, .call 60]

/-- The reject arm.  It frees the decoded error string and then frees the
input byte vector.  The last block of the tail ends right after it, so it
carries no branch of its own.  WAT lines 1715 to 1734. -/
@[reducible] def rmErrArm : Program :=
  .block 0 0 rmDropError ::
    [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1,
      .call 60]

/-- The body of the outer block: the accept arm, then the reject arm.
WAT lines 1604 to 1734. -/
@[reducible] def rmOuterBody : Program :=
  .block 0 0 rmOkArm :: rmErrArm

/-- The call of the key decoder.  Local 1 holds the input length and
local 3 holds the input pointer, both left by the read phase.  WAT lines
1597 to 1602. -/
@[reducible] def rmDecodeCall : Program :=
  [.localGet 0, .const 16, .add, .localGet 3, .localGet 1, .call 10]

/-- The restore of the stack pointer.  Every path reaches it.  WAT lines
1736 to 1739. -/
@[reducible] def rmEpilogue : Program :=
  [.localGet 0, .const 320, .add, .globalSet 0]

/-- The tail of the `map_remove` driver is the decode call, the outer
block, and the stack epilogue. -/
theorem func6AfterRead_shape :
    func6AfterRead =
      rmDecodeCall ++ .block 0 0 rmOuterBody :: rmEpilogue := by
  rfl

end Project.RustHashMap.RemoveTailDefs
