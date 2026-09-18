import Project.RustHashMap.InsertRead
import Project.RustHashMap.CollectContract
import Project.RustHashMap.EntriesContracts
import Project.RustHashMap.MapOpContracts

/-!
# The tail of the `map_insert` driver: program fragments

The `map_insert` driver is local `func0`, absolute function 3.  WAT
lines 30 to 469 of `programs/rust/build/rust_hash_map/program.wat` hold
it.  `Project.RustHashMap.InsertRead` proves the read phase and stops at
the two exits of the seventh block.  This file splits the code after
those two exits into one definition per stage, so that the proof of the
tail can name each one.

The tail is WAT lines 123 to 468.  It does these steps:

1. It reloads the three vector words, WAT 123 to 136, and stores the
   length and the pointer in the decode header at frame offsets 316 and
   312.
2. It cuts the key and the value off the front of the input, WAT 137 to
   171.  Two guards on the original length send a short input to one of
   the two error arms.
3. The two error arms, WAT 181 to 233 and 235 to 285, build the
   "failed to fill whole buffer" error with absolute `func 55` and
   decode it with absolute `func 52`.  Both leave through the reject
   exit.
4. It calls the borsh decoder, absolute `func 4`, WAT 287 to 293, with
   the 16-byte output slot at frame offset 336 and the header at 312.
   A tag that is not `okTag` and a count of unread bytes that is not
   zero both leave through the reject exit.
5. The success tail, WAT 360 to 463, copies the decoded triple into the
   entries vector header, frees the input, builds the table with
   absolute `func 5`, inserts the pair with absolute `func 6`, copies
   the new map back, sorts the entries with absolute `func 7`, writes
   the reply with absolute `func 8`, frees the pair buffer and drops the
   table.

## The frame

The frame holds 368 bytes.  The regions are these, as offsets from the
frame base:

| region                            | offsets    |
|-----------------------------------|------------|
| entries vec header for `call 5`   | 8 to 20    |
| input vec header of the read phase| 24 to 36   |
| `call 52` out slot on an error arm| 24 to 40   |
| map slot                          | 24 to 56   |
| `call 55` out slot on an error arm| 56 to 72   |
| chunk buffer of the read phase    | 56 to 312  |
| `call 6` out slot                 | 56 to 96   |
| `call 7` out header               | 64 to 76   |
| decode header for `call 4`        | 312 to 320 |
| `call 55` out slot, not all read  | 320 to 336 |
| `call 4` out slot                 | 336 to 352 |
| error word scratch                | 352 to 364 |

The chunk buffer and the input vector header are dead after WAT 136.
The three slots at 24, 56 and 64 overlay them.

## The branch depths

Seven blocks open in a row at WAT 51 to 57.  Their ends are at WAT 464,
359, 340, 286, 234, 180 and 172, so the seven continuations are
`insAfter2` to `insAfter7` of `Project.RustHashMap.InsertRead` and the
code after the outer block.  Every branch of the tail was read off that
nesting:

| WAT | branch    | target frame | target code   |
|-----|-----------|--------------|---------------|
| 140 | `br_if 1` | the sixth    | `insAfter6`   |
| 157 | `br_if 2` | the fifth    | `insAfter5`   |
| 171 | `br 3`    | the fourth   | `insAfter4`   |
| 202 | `br_if 0` | the inner A  | `insErrTailA` |
| 226 | `br_if 0` | the inner A  | `insErrTailA` |
| 230 | `br 3`    | the third    | `insAfter3`   |
| 257 | `br_if 0` | the fourth   | `insAfter4`   |
| 281 | `br_if 0` | the fourth   | `insAfter4`   |
| 285 | `br 1`    | the third    | `insAfter3`   |
| 300 | `br_if 0` | the ok guard | `insAfterDecode` |
| 304 | `br 1`    | the third    | `insAfter3`   |
| 312 | `br_if 1` | the second   | `insAfter2`   |
| 330 | `br_if 0` | the third    | `insAfter3`   |
| 345 | `br_if 0` | the error drop | `insRejectTail` |
| 353 | `br_if 1` | the outer    | the epilogue  |
| 358 | `br 1`    | the outer    | the epilogue  |
| 370 | `br_if 0` | the free input | `insCollectAndRest` |
| 430 | `br_if 0` | the free pairs | `insTableDrop` |
| 443 | `br_if 0` | the outer    | the epilogue  |
| 454 | `br_if 0` | the outer    | the epilogue  |

The first error arm carries a block of its own, WAT 196 to 231, and the
second does not, so the two dead tag tests read `br_if 0` in both arms
but reach different code.  The table drop sits directly inside the outer
block, so its two guards read `br_if 0` and the arm carries no branch of
its own, which the `map_remove` twin does not share.

The constants keep the unsigned form that the Lean AST uses: `i32.const
-4` is `4294967292`, `i32.const -8` is `4294967288`, and `i32.const
-2147483647` is `2147483649`, which is
`Project.RustHashMap.BodyContracts.okTag`.  The AST drops the alignment
of a load or a store, so `i64.load offset=60 align=4` is `load64 60`.
-/

namespace Project.RustHashMap.InsertTailDefs

open Wasm
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.EntriesContracts
open Project.RustHashMap.MapOpContracts
open Project.RustHashMap.InsertRead

/-! ## The stack that the callees take -/

/-- The deepest stack that a callee of the insert tail takes below the
driver frame.  `sorted_entries`, absolute `func 7`, takes the most,
because it sorts the entries, so this is `serializeDepth`. -/
def insertCalleeDepth : Nat := serializeDepth

theorem insertCalleeDepth_serialize :
    serializeDepth = insertCalleeDepth := rfl

theorem insertCalleeDepth_eq : insertCalleeDepth = 14096 := rfl

/-- The read phase keeps sixteen bytes of `StackReserve`, so the tail
carries the rest of the region as one slice. -/
theorem insertExtra_eq : insertCalleeDepth - 16 = 14080 := by decide

/-- The borsh decoder, absolute `func 4`, is the `call 4` of WAT 293. -/
theorem decoderDepth_le_insert :
    decoderDepth ≤ insertCalleeDepth := by decide

/-- `borsh::io::Error::new`, absolute `func 55`, is the `call 55` of WAT
187, 241 and 319. -/
theorem errorNewDepth_le_insert :
    errorNewDepth ≤ insertCalleeDepth := by decide

theorem collectDepth_le_insert :
    collectDepth ≤ insertCalleeDepth := by decide

/-- The insert shim, absolute `func 6`, is the `call 6` of WAT 391. -/
theorem insertWrapDepth_le_insert :
    insertWrapDepth ≤ insertCalleeDepth := by decide

theorem replyDepth_le_insert : replyDepth ≤ insertCalleeDepth := by
  decide

/-- A table holds at most `2 ^ 27` buckets, so the sort of the entries
stays inside the region that the tail carries. -/
theorem sortedEntriesDepth_le_insert {items : Nat}
    (hitems : items ≤ 2 ^ 27) :
    sortedEntriesDepth items ≤ insertCalleeDepth :=
  sortedEntriesDepth_le_serialize hitems

/-- The stack that `map_insert` takes: its own 368-byte frame and the
region that its callees take below it. -/
def insertDepth : Nat := 368 + insertCalleeDepth

theorem insertDepth_eq : insertDepth = 14464 := rfl

theorem insertDepth_le : insertDepth ≤ entryStackTop.toNat := by decide

/-- The base of the region that the tail carries.  The driver frame base
is 1048208, and the callee region ends 14096 bytes below it. -/
theorem func0Base_sub_depth :
    func0Base - UInt32.ofNat insertCalleeDepth = 1034112 := by decide

/-! ## The rest of the seventh block -/

/-- The reload of the three vector words.  The capacity goes to local 2,
the pointer to local 1, and the length to local 4 and to the decode
header at frame offset 316.  The pointer goes to frame offset 312 in the
same run.  WAT lines 123 to 136. -/
@[reducible] def insReload : Program :=
  [.localGet 0, .load32 24, .localSet 2, .localGet 0, .load32 28,
    .localSet 1, .localGet 0, .localGet 0, .load32 32, .localTee 4,
    .store32 316, .localGet 0, .localGet 1, .store32 312]

/-- The inline decode of the key and the value.  Both guards read the
original length in local 4, so the second one tests eight against the
length before the first cut.  The key lands in local 3 and the value in
local 5, and both loads read through the original pointer in local 1.
The `br_if 1` of WAT 140 leaves the sixth block, the `br_if 2` of WAT
157 leaves the fifth, and the `br 3` of WAT 171 leaves the fourth.  WAT
lines 137 to 171. -/
@[reducible] def insDecodeKV : Program :=
  [.localGet 4, .const 3, .leU, .br_if 1,
    .localGet 0, .localGet 4, .const 4294967292, .add, .store32 316,
    .localGet 0, .localGet 1, .const 4, .add, .store32 312,
    .localGet 1, .load32 0, .localSet 3,
    .localGet 4, .const 8, .ltU, .br_if 2,
    .localGet 0, .localGet 4, .const 4294967288, .add, .store32 316,
    .localGet 0, .localGet 1, .const 8, .add, .store32 312,
    .localGet 1, .load32 4, .localSet 5, .br 3]

theorem insRest7_shape : insRest7 = insReload ++ insDecodeKV := rfl

/-- The empty arm of the read phase, WAT lines 173 to 179.  It writes an
empty slice into the decode header, sets the pointer register to one and
the capacity register to zero, and then falls into the first error arm.
This is the name that `Project.RustHashMap.InsertRead` leaves as
`insAfter7`. -/
@[reducible] def insEmptyArm : Program := insAfter7

/-! ## The two error arms -/

/-- The error call of the first error arm.  The output slot is at frame
offset 56, the kind is 17, and the static message is the 27 bytes
"failed to fill whole buffer" at address 1049080.  The two stores save
the words at offsets 60 to 72 into the scratch at 352 to 364.  WAT lines
181 to 195. -/
@[reducible] def insErrCallA : Program :=
  [.localGet 0, .const 56, .add, .const 17, .const 1049080, .const 27,
    .call 55, .localGet 0, .localGet 0, .load64 60, .store64 352,
    .localGet 0, .localGet 0, .load32 68, .store32 360]

/-- The body of the block of the first error arm.  Both tag tests are
dead: `Func52Spec` gives a first word that is not `okTag`, and so does
`Func49Spec`.  The live path restores the three saved words, decodes the
error with absolute `func 52` into the slot at frame offset 24, moves
the message pointer into local 3, and leaves the third block.  WAT lines
197 to 230. -/
@[reducible] def insErrBodyA : Program :=
  [.localGet 0, .load32 56, .localTee 4, .const 2147483649, .eq,
    .br_if 0, .localGet 0, .localGet 4, .store32 56,
    .localGet 0, .localGet 0, .load64 352, .store64 60,
    .localGet 0, .localGet 0, .load32 360, .store32 68,
    .localGet 0, .const 24, .add, .localGet 0, .const 56, .add,
    .call 52, .localGet 0, .load32 24, .localTee 4,
    .const 2147483649, .eq, .br_if 0, .localGet 0, .load32 28,
    .localSet 3, .br 3]

/-- The code that the two dead tag tests of the first error arm reach.
It sets local 3 to zero and falls into the second error arm.  WAT lines
232 to 233. -/
@[reducible] def insErrTailA : Program := [.const 0, .localSet 3]

/-- The first error arm, WAT lines 181 to 233.  The input was shorter
than four bytes, or it was empty.  This is the name that
`Project.RustHashMap.InsertRead` leaves as `insAfter6`. -/
@[reducible] def insErrArmA : Program := insAfter6

theorem insAfter6_shape :
    insAfter6 = insErrCallA ++ .block 0 0 insErrBodyA :: insErrTailA :=
  rfl

/-- The error call of the second error arm.  It is the call of
`insErrCallA` with the same slot, kind, message and saves, and it then
clears the value register in local 5.  WAT lines 235 to 251. -/
@[reducible] def insErrCallB : Program :=
  [.localGet 0, .const 56, .add, .const 17, .const 1049080, .const 27,
    .call 55, .localGet 0, .localGet 0, .load64 60, .store64 352,
    .localGet 0, .localGet 0, .load32 68, .store32 360, .const 0,
    .localSet 5]

/-- The rest of the second error arm.  It is the body of the block of
the first arm with two differences: the arm carries no block, so the two
dead tag tests read `br_if 0` against the fourth block, and the live
path leaves the third block with `br 1`.  WAT lines 252 to 285. -/
@[reducible] def insErrRestB : Program :=
  [.localGet 0, .load32 56, .localTee 4, .const 2147483649, .eq,
    .br_if 0, .localGet 0, .localGet 4, .store32 56,
    .localGet 0, .localGet 0, .load64 352, .store64 60,
    .localGet 0, .localGet 0, .load32 360, .store32 68,
    .localGet 0, .const 24, .add, .localGet 0, .const 56, .add,
    .call 52, .localGet 0, .load32 24, .localTee 4,
    .const 2147483649, .eq, .br_if 0, .localGet 0, .load32 28,
    .localSet 3, .br 1]

/-- The second error arm, WAT lines 235 to 285.  The input held a key
but no value.  This is the name that `Project.RustHashMap.InsertRead`
leaves as `insAfter5`. -/
@[reducible] def insErrArmB : Program := insAfter5

theorem insAfter5_shape : insAfter5 = insErrCallB ++ insErrRestB := rfl

/-! ## The decoder call -/

/-- The call of the borsh decoder, absolute `func 4`.  The 16-byte
output slot is at frame offset 336 and the header that the reload and
the two cuts wrote is at frame offset 312.  WAT lines 287 to 293. -/
@[reducible] def insDecodeCall : Program :=
  [.localGet 0, .const 336, .add, .localGet 0, .const 312, .add,
    .call 4]

/-- The body of the guard block of the decoder.  The `br_if 0` of WAT
300 is the accepting branch: it leaves the block when the tag word is
`okTag`.  The reject path moves the message pointer into local 3 and
leaves the third block.  WAT lines 295 to 304. -/
@[reducible] def insOkGuard : Program :=
  [.localGet 0, .load32 336, .localTee 4, .const 2147483649, .eq,
    .br_if 0, .localGet 0, .load32 340, .localSet 3, .br 1]

/-- The load of the decoded pair buffer.  The capacity is the low word
and the pointer the high word of local 6.  WAT lines 306 to 308. -/
@[reducible] def insDecodePair : Program :=
  [.localGet 0, .load64 340, .localSet 6]

/-- The "not all bytes read" arm.  It builds the `io::Error` with kind
12 and the 18 bytes "Not all bytes read" at address 1049107, reads the
two error words out of the slot at frame offset 320, and frees the
decoded pair buffer when its capacity is not zero.  The buffer holds
`8 * capacity` bytes with alignment 4.  WAT lines 313 to 339. -/
@[reducible] def insNotAllRead : Program :=
  [.localGet 0, .const 320, .add, .const 12, .const 1049107, .const 18,
    .call 55, .localGet 0, .load32 324, .localSet 3, .localGet 0,
    .load32 320, .localSet 4, .localGet 6, .wrapI64, .localTee 5, .eqz,
    .br_if 0, .localGet 6, .constI64 32, .shrUI64, .wrapI64,
    .localGet 5, .const 3, .shl, .const 4, .call 60]

/-- The trailing-bytes test and the arm that fails it.  A count of zero
at frame offset 316 leaves the second block for the success tail.  WAT
lines 309 to 339. -/
@[reducible] def insTrailing : Program :=
  [.localGet 0, .load32 316, .eqz, .br_if 1] ++ insNotAllRead

/-- The decoder answer: the pair load and the trailing-bytes test.  WAT
lines 306 to 339. -/
@[reducible] def insAfterDecode : Program :=
  insDecodePair ++ insTrailing

theorem insAfter4_shape :
    insAfter4 =
      insDecodeCall ++ .block 0 0 insOkGuard :: insAfterDecode := rfl

/-! ## The reject exit -/

/-- The drop of the decoded error string.  A length below one carries no
allocation, so nothing is freed.  WAT lines 342 to 349. -/
@[reducible] def insDropError : Program :=
  [.localGet 4, .const 1, .ltS, .br_if 0, .localGet 3, .localGet 4,
    .const 1, .call 60]

/-- The release of the input byte vector on the reject exit.  A capacity
of zero leaves nothing to free.  Both paths leave the outer block, so
the arm ends with a branch of its own.  WAT lines 351 to 358. -/
@[reducible] def insRejectTail : Program :=
  [.localGet 2, .eqz, .br_if 1, .localGet 1, .localGet 2, .const 1,
    .call 60, .br 1]

/-- The reject exit, WAT lines 341 to 358.  It frees the decoded error
string and the input byte vector, and it writes nothing.  This is the
name that `Project.RustHashMap.InsertRead` leaves as `insAfter3`. -/
@[reducible] def insReject : Program := insAfter3

theorem insAfter3_shape :
    insAfter3 = .block 0 0 insDropError :: insRejectTail := rfl

/-! ## The success tail -/

/-- The entries vector header for the collect call.  The pair count sits
at frame offset 348 and goes to offset 16, and the capacity and the
pointer travel as one 64-bit word to offsets 8 and 12.  WAT lines 360 to
366. -/
@[reducible] def insEntriesHeader : Program :=
  [.localGet 0, .localGet 0, .load32 348, .store32 16, .localGet 0,
    .localGet 6, .store64 8]

/-- The release of the input byte vector before the collect call.  A
capacity of zero leaves nothing to free.  WAT lines 368 to 374. -/
@[reducible] def insFreeInput : Program :=
  [.localGet 2, .eqz, .br_if 0, .localGet 1, .localGet 2, .const 1,
    .call 60]

/-- The call of `collect_entries`, absolute `func 5`.  It takes the
32-byte map slot at frame offset 24 and the entries vector header at
frame offset 8.  WAT lines 376 to 382. -/
@[reducible] def insCollect : Program :=
  [.localGet 0, .const 24, .add, .localGet 0, .const 8, .add, .call 5]

/-- The call of the insert shim, absolute `func 6`.  It takes the
40-byte output slot at frame offset 56, the map slot at frame offset 24,
the key in local 3 and the value in local 5.  The option word of the
answer goes to local 6.  WAT lines 383 to 394. -/
@[reducible] def insShim : Program :=
  [.localGet 0, .const 56, .add, .localGet 0, .const 24, .add,
    .localGet 3, .localGet 5, .call 6, .localGet 0, .load64 56,
    .localSet 6]

/-- The copy of the new map value back over the map slot.  The four
64-bit words move from the top down, so the source and the target never
overlap in the wrong order.  WAT lines 395 to 410. -/
@[reducible] def insCopyBack : Program :=
  [.localGet 0, .localGet 0, .load64 88, .store64 48,
    .localGet 0, .localGet 0, .load64 80, .store64 40,
    .localGet 0, .localGet 0, .load64 72, .store64 32,
    .localGet 0, .localGet 0, .load64 64, .store64 24]

/-- The call of `sorted_entries`, absolute `func 7`.  It takes the
12-byte output header at frame offset 64 and the map slot at frame
offset 24.  WAT lines 411 to 417. -/
@[reducible] def insSort : Program :=
  [.localGet 0, .const 64, .add, .localGet 0, .const 24, .add, .call 7]

/-- The call of the reply writer, absolute `func 8`.  The store puts the
option word back at frame offset 56, so the record at offsets 56 to 76
holds the option and then the pair buffer header.  WAT lines 418 to
424. -/
@[reducible] def insReply : Program :=
  [.localGet 0, .localGet 6, .store64 56, .localGet 0, .const 56, .add,
    .call 8]

/-- The release of the pair buffer that `sorted_entries` allocated.  The
entry count sits at frame offset 64 and the pointer at frame offset 68.
A count of zero leaves nothing to free.  WAT lines 426 to 437. -/
@[reducible] def insFreePairs : Program :=
  [.localGet 0, .load32 64, .localTee 1, .eqz, .br_if 0, .localGet 0,
    .load32 68, .localGet 1, .const 3, .shl, .const 4, .call 60]

/-- The drop of the hash table.  The bucket count sits at map offset 4
and the control pointer at map offset 0, which are frame offsets 28 and
24.  A bucket count of zero leaves nothing to free, and so does a total
size of zero.  The arm sits directly inside the outer block, so both
guards read `br_if 0` and the arm carries no branch of its own.  WAT
lines 439 to 463. -/
@[reducible] def insTableDrop : Program :=
  [.localGet 0, .load32 28, .localTee 1, .eqz, .br_if 0, .localGet 1,
    .const 3, .shl, .localTee 4, .localGet 1, .add, .const 17, .add,
    .localTee 1, .eqz, .br_if 0, .localGet 0, .load32 24, .localGet 4,
    .sub, .const 4294967288, .add, .localGet 1, .const 8, .call 60]

/-! ## The suffixes of the success tail

Each call needs the code that follows it as an explicit argument, so
each suffix gets a name. -/

/-- The free of the pair buffer and the table drop.  WAT lines 418 to
463. -/
@[reducible] def insAfterSort : Program :=
  insReply ++ .block 0 0 insFreePairs :: insTableDrop

/-- The sort call and everything after it.  WAT lines 411 to 463. -/
@[reducible] def insAfterCopyBack : Program := insSort ++ insAfterSort

/-- The copy back of the new map value and everything after it.  WAT
lines 395 to 463. -/
@[reducible] def insAfterShim : Program :=
  insCopyBack ++ insAfterCopyBack

/-- The shim call and everything after it.  WAT lines 383 to 463. -/
@[reducible] def insAfterCollect : Program := insShim ++ insAfterShim

/-- The collect call and everything after it.  WAT lines 376 to 463. -/
@[reducible] def insCollectAndRest : Program :=
  insCollect ++ insAfterCollect

/-- The success tail, WAT lines 360 to 463.  This is the name that
`Project.RustHashMap.InsertRead` leaves as `insAfter2`. -/
@[reducible] def insSuccessTail : Program := insAfter2

theorem insAfter2_shape :
    insAfter2 =
      insEntriesHeader ++
        .block 0 0 insFreeInput :: insCollectAndRest := rfl

/-! ## The locals

The driver declares seven locals.  Locals 0 to 5 are `i32` and local 6
is `i64`.  Local 0 holds the frame base on every path. -/

/-- The locals after the reload of WAT 136.  The capacity is in local 2,
the pointer in local 1, and the length in local 4.  Local 3 holds the
last chunk byte that the read phase left, local 5 holds zero and local 6
holds the zero of the frame setup.

The same shape names three later states, because the two cuts write
memory only: after the key load of WAT 153 local 3 holds the key, and
the second error arm starts in that state.  The first error arm starts
in this shape as well, and after the empty arm of WAT 179 it starts as
`afterReloadLocalsIns 0 1 0 0`. -/
def afterReloadLocalsIns (capacity ptr byte length : UInt32) : Locals :=
  ⟨[], [.i32 func0Base, .i32 ptr, .i32 capacity, .i32 byte,
    .i32 length, .i32 0, .i64 0], []⟩

/-- The locals at the decoder call of WAT 287.  The key is in local 3
and the value in local 5, both cut off the front of the input.  Local 4
still holds the original length. -/
def afterDecodeKVLocalsIns (capacity ptr key value length : UInt32) :
    Locals :=
  ⟨[], [.i32 func0Base, .i32 ptr, .i32 capacity, .i32 key,
    .i32 length, .i32 value, .i64 0], []⟩

/-- The locals at the start of the success tail, WAT 360.  The tag test
of WAT 297 left `okTag` in local 4, and the pair load of WAT 308 left
the capacity and the pointer of the decoded buffer in local 6. -/
def successLocalsIns (capacity ptr key value : UInt32) (pair : UInt64) :
    Locals :=
  ⟨[], [.i32 func0Base, .i32 ptr, .i32 capacity, .i32 key,
    .i32 okTag, .i32 value, .i64 pair], []⟩

end Project.RustHashMap.InsertTailDefs
