import Project.RustHashMap.ContainsKeyRead
import Project.RustHashMap.GetRead
import Project.RustHashMap.KeyDecoderContract
import Project.RustHashMap.CollectContract

/-!
# The tails of the two lookup drivers: program fragments

The `map_contains_key` driver is local `func16`, absolute index 19.  The
`map_get` driver is local `func18`, absolute index 21.  The read phase of
each driver is proved in `Project.RustHashMap.ContainsKeyRead` and
`Project.RustHashMap.GetRead`.  This file splits the code after the read
phase into one definition per control block, so that the proof of each
tail can name each block.

The tail of `map_contains_key` is WAT lines 4652 to 4769 of
`programs/rust/build/rust_hash_map/program.wat`.  The tail of `map_get` is
WAT lines 5162 to 5306.  The two tails have the same shape.  Each one does
these steps:

1. It calls the key decoder, absolute `func 10`, with the 20-byte output
   slot in the frame, the input pointer in local 3 and the input length in
   local 1.
2. It reads the tag word of the output slot.  A tag of zero means `Ok`.
   Any other tag means `Err`, and the code jumps to the error arm.
3. On `Ok` it copies the decoded map header into the entries vector
   header, moves the leading key into local 1, frees the input buffer, and
   calls `collect_entries`, absolute `func 5`, with the 32-byte map slot.
4. It calls the lookup kernel, absolute `func 12` for `contains_key` and
   absolute `func 20` for `get`, calls the marker `func 33`, allocates
   1024 bytes, writes the answer, writes the bytes to the output stream
   with `func 64`, and frees the buffer.
5. It drops the hash table and restores the stack pointer.

The frame of `map_contains_key` holds 304 bytes and the frame of `map_get`
holds 320 bytes.  The regions are these, as offsets from the frame base:

| region                          | abs 19   | abs 21   |
|---------------------------------|----------|----------|
| entries vec header for `call 5` | 0 to 12  | 16 to 28 |
| `call 20` out slot              | none     | 8 to 16  |
| `call 10` out slot              | 16 to 36 | 32 to 52 |
| input vec header                | 36 to 48 | 52 to 64 |
| 256-byte chunk buffer           | 48 to 304| 64 to 320|
| map slot, the head of the chunk | 48 to 80 | 64 to 96 |

Each tail has three exits.  The reject exit frees the decoded error and
the input buffer, and it writes nothing.  The accept exit writes the
answer to the output stream.  The third exit is the allocator failure,
which raises `talos.oom`.

The constants keep the unsigned form that the Lean AST uses: `i32.const
-8` is `4294967288`.  The store of the payload word of `map_get` is
`i32.store offset=1 align=1`, which the AST writes as `store32 1`.
-/

namespace Project.RustHashMap.LookupTailDefs

open Wasm
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.ContainsKeyRead
open Project.RustHashMap.GetRead

/-! ## The stack that the callees take -/

/-- The deepest stack that a callee of a lookup tail takes below the
driver frame.  The key decoder takes the most, so this is
`keyDecoderDepth`. -/
def lookupCalleeDepth : Nat := keyDecoderDepth

theorem lookupCalleeDepth_keyDecoder :
    keyDecoderDepth = lookupCalleeDepth := rfl

theorem collectDepth_le_lookup : collectDepth ≤ lookupCalleeDepth := by
  decide

theorem errorNewDepth_le_lookup : errorNewDepth ≤ lookupCalleeDepth := by
  decide

/-- The stack that `map_contains_key` takes: its own 304-byte frame and
the region that its callees take below it. -/
def containsKeyDepth : Nat := 304 + lookupCalleeDepth

/-- The stack that `map_get` takes: its own 320-byte frame and the region
that its callees take below it. -/
def getDepth : Nat := 320 + lookupCalleeDepth

theorem containsKeyDepth_le :
    containsKeyDepth ≤ entryStackTop.toNat := by decide

theorem getDepth_le : getDepth ≤ entryStackTop.toNat := by decide

/-! ## The blocks of `map_contains_key`, from the innermost outward -/

/-- The release of the input byte vector before the collect call.  A
capacity of zero leaves nothing to free.  WAT lines 4676 to 4682. -/
@[reducible] def ckFreeInput : Program :=
  [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1,
    .call 60]

/-- The drop of the hash table.  The bucket count sits at map offset 4 and
the control pointer at map offset 0, which are frame offsets 52 and 48.
A bucket count of zero leaves nothing to free.  WAT lines 4712 to 4737. -/
@[reducible] def ckTableDrop : Program :=
  [.localGet 0, .load32 52, .localTee 1, .eqz, .br_if 2, .localGet 1,
    .const 3, .shl, .localTee 3, .localGet 1, .add, .const 17, .add,
    .localTee 1, .eqz, .br_if 2, .localGet 0, .load32 48, .localGet 3,
    .sub, .const 4294967288, .add, .localGet 1, .const 8, .call 60, .br 2]

/-- The reply.  It allocates 1024 bytes with alignment 1, writes the
answer byte, writes that byte to the output stream, frees the buffer, and
then drops the hash table.  The `br_if 1` leaves the decode block and
reaches the allocator failure.  WAT lines 4696 to 4737. -/
@[reducible] def ckReply : Program :=
  [.const 1024, .const 1, .call 58, .localTee 1, .eqz, .br_if 1,
    .localGet 1, .localGet 3, .store8 0, .localGet 1, .const 1, .call 64,
    .localGet 1, .const 1024, .const 1, .call 60] ++ ckTableDrop

/-- The accept arm.  The guard reads the tag word at frame offset 16, and
a tag that is not zero leaves the arm.  The arm then copies the capacity
and the pointer as one 64-bit word, copies the pair count, moves the
leading key into local 1, frees the input, builds the table with
`call 5`, asks the kernel with `call 12`, and replies.  WAT lines 4661 to
4737. -/
@[reducible] def ckOkArm : Program :=
  [.localGet 0, .load32 16, .br_if 0, .localGet 0, .localGet 0, .load64 24,
    .store64 0, .localGet 0, .localGet 0, .load32 32, .store32 8,
    .localGet 0, .load32 20, .localSet 1, .block 0 0 ckFreeInput,
    .localGet 0, .const 48, .add, .localGet 0, .call 5, .localGet 0,
    .const 48, .add, .localGet 1, .call 12, .localSet 3, .call 33] ++
    ckReply

/-- The drop of the decoded error string.  A length below one carries no
allocation, so nothing is freed.  WAT lines 4740 to 4750. -/
@[reducible] def ckDropError : Program :=
  [.localGet 0, .load32 20, .localTee 1, .const 1, .ltS, .br_if 0,
    .localGet 0, .load32 24, .localGet 1, .const 1, .call 60]

/-- The reject arm.  It frees the decoded error string, then frees the
input byte vector, and then leaves the outer block.  WAT lines 4739 to
4759. -/
@[reducible] def ckErrArm : Program :=
  .block 0 0 ckDropError ::
    [.localGet 2, .eqz, .br_if 1, .localGet 3, .localGet 2, .const 1,
      .call 60, .br 1]

/-- The decode block: the accept arm, then the reject arm.  WAT lines 4660
to 4759. -/
@[reducible] def ckDecodeBlock : Program :=
  .block 0 0 ckOkArm :: ckErrArm

/-- The body of the outer block: the decode block, then the allocator
failure.  The allocator never returns zero, so the last four instructions
are dead.  WAT lines 4659 to 4764. -/
@[reducible] def ckOuterBody : Program :=
  .block 0 0 ckDecodeBlock ::
    [.const 1, .const 1024, .call 99, .unreachable]

/-- The call of the key decoder.  Local 1 holds the input length and local
3 holds the input pointer, both left by the read phase.  WAT lines 4652 to
4657. -/
@[reducible] def ckDecodeCall : Program :=
  [.localGet 0, .const 16, .add, .localGet 3, .localGet 1, .call 10]

/-- The restore of the stack pointer.  Every path reaches it.  WAT lines
4766 to 4769. -/
@[reducible] def ckEpilogue : Program :=
  [.localGet 0, .const 304, .add, .globalSet 0]

/-- The tail of the `map_contains_key` driver is the decode call, the
outer block, and the stack epilogue. -/
theorem func16AfterRead_shape :
    func16AfterRead =
      ckDecodeCall ++ .block 0 0 ckOuterBody :: ckEpilogue := by
  rfl

/-! ## The blocks of `map_get`, from the innermost outward -/

/-- The release of the input byte vector before the collect call.  A
capacity of zero leaves nothing to free.  WAT lines 5186 to 5192. -/
@[reducible] def getFreeInput : Program :=
  [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1,
    .call 60]

/-- The drop of the hash table.  The bucket count sits at map offset 4 and
the control pointer at map offset 0, which are frame offsets 68 and 64.
A bucket count of zero leaves nothing to free.  WAT lines 5249 to 5274. -/
@[reducible] def getTableDrop : Program :=
  [.localGet 0, .load32 68, .localTee 1, .eqz, .br_if 2, .localGet 1,
    .const 3, .shl, .localTee 3, .localGet 1, .add, .const 17, .add,
    .localTee 1, .eqz, .br_if 2, .localGet 0, .load32 64, .localGet 3,
    .sub, .const 4294967288, .add, .localGet 1, .const 8, .call 60, .br 2]

/-- The payload block.  Local 4 holds the discriminant that the kernel
wrote.  A discriminant of one means `some`, and then the block stores the
payload word at buffer offset 1, sets the reply length to five, and sets
the reply tag to one.  WAT lines 5227 to 5237. -/
@[reducible] def getPayloadBlock : Program :=
  [.localGet 4, .const 1, .ne, .br_if 0, .localGet 1, .localGet 5,
    .store32 1, .const 5, .localSet 3, .const 1, .localSet 2]

/-- The reply.  The reply length starts at one, which is the `none` case.
The code allocates 1024 bytes with alignment 1, writes the payload word
when the answer is `some`, writes the tag byte, writes the bytes to the
output stream, frees the buffer, and then drops the hash table.  The
`br_if 1` leaves the decode block and reaches the allocator failure.  WAT
lines 5216 to 5274. -/
@[reducible] def getReply : Program :=
  [.const 1, .localSet 3, .const 1024, .const 1, .call 58, .localTee 1,
    .eqz, .br_if 1, .const 0, .localSet 2, .block 0 0 getPayloadBlock,
    .localGet 1, .localGet 2, .store8 0, .localGet 1, .localGet 3,
    .call 64, .localGet 1, .const 1024, .const 1, .call 60] ++ getTableDrop

/-- The accept arm.  The guard reads the tag word at frame offset 32, and
a tag that is not zero leaves the arm.  The arm then copies the capacity
and the pointer as one 64-bit word, copies the pair count, moves the
leading key into local 1, frees the input, builds the table with
`call 5`, asks the kernel with `call 20`, loads the two out words into
locals 5 and 4, and replies.  WAT lines 5171 to 5274. -/
@[reducible] def getOkArm : Program :=
  [.localGet 0, .load32 32, .br_if 0, .localGet 0, .localGet 0, .load64 40,
    .store64 16, .localGet 0, .localGet 0, .load32 48, .store32 24,
    .localGet 0, .load32 36, .localSet 1, .block 0 0 getFreeInput,
    .localGet 0, .const 64, .add, .localGet 0, .const 16, .add, .call 5,
    .localGet 0, .const 8, .add, .localGet 0, .const 64, .add,
    .localGet 1, .call 20, .localGet 0, .load32 12, .localSet 5,
    .localGet 0, .load32 8, .localSet 4, .call 33] ++ getReply

/-- The drop of the decoded error string.  A length below one carries no
allocation, so nothing is freed.  WAT lines 5277 to 5287. -/
@[reducible] def getDropError : Program :=
  [.localGet 0, .load32 36, .localTee 1, .const 1, .ltS, .br_if 0,
    .localGet 0, .load32 40, .localGet 1, .const 1, .call 60]

/-- The reject arm.  It frees the decoded error string, then frees the
input byte vector, and then leaves the outer block.  WAT lines 5276 to
5296. -/
@[reducible] def getErrArm : Program :=
  .block 0 0 getDropError ::
    [.localGet 2, .eqz, .br_if 1, .localGet 3, .localGet 2, .const 1,
      .call 60, .br 1]

/-- The decode block: the accept arm, then the reject arm.  WAT lines 5170
to 5296. -/
@[reducible] def getDecodeBlock : Program :=
  .block 0 0 getOkArm :: getErrArm

/-- The body of the outer block: the decode block, then the allocator
failure.  The allocator never returns zero, so the last four instructions
are dead.  WAT lines 5169 to 5301. -/
@[reducible] def getOuterBody : Program :=
  .block 0 0 getDecodeBlock ::
    [.const 1, .const 1024, .call 99, .unreachable]

/-- The call of the key decoder.  Local 1 holds the input length and local
3 holds the input pointer, both left by the read phase.  WAT lines 5162 to
5167. -/
@[reducible] def getDecodeCall : Program :=
  [.localGet 0, .const 32, .add, .localGet 3, .localGet 1, .call 10]

/-- The restore of the stack pointer.  Every path reaches it.  WAT lines
5303 to 5306. -/
@[reducible] def getEpilogue : Program :=
  [.localGet 0, .const 320, .add, .globalSet 0]

/-- The tail of the `map_get` driver is the decode call, the outer block,
and the stack epilogue. -/
theorem func18AfterRead_shape :
    func18AfterRead =
      getDecodeCall ++ .block 0 0 getOuterBody :: getEpilogue := by
  rfl

end Project.RustHashMap.LookupTailDefs
