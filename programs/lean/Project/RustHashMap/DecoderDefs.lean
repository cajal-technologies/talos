import Project.RustHashMap.BodyContracts

/-!
# The borsh decoder: program fragments

The decoder is local `func1`, absolute index 4.  It is
`Vec<(u32, u32)>::deserialize`.  The driver calls it from its tail, which
`Project.RustHashMap.DriverTail` splits the same way.

This file splits the body into one definition for each control block, so
that the proof of the decoder can name each block.  `func1_shape` closes
the split by `rfl`.

The body is WAT lines 470 to 850 of
`programs/rust/build/rust_hash_map/program.wat`.  It does these steps:

1. It takes a 64-byte frame and keeps the base in local 2.
2. It reads the length word of the slice header.  Fewer than four bytes
   left is the "unexpected end of input" error.
3. It reads the four-byte count and advances the header past it.  A count
   of zero is the empty vector, and it allocates nothing.
4. It allocates `8 * min(count, 512)` bytes for the pair buffer.
5. It runs one loop step for each pair.  A step reads eight input bytes,
   grows the buffer when the buffer is full, and writes the key at
   `buffer + 8 i` and the value at `buffer + 8 i + 4`.
6. It writes the capacity, the pointer and the count into the output slot
   under the tag `okTag`.

The locals are:

| Local | Holds |
| --- | --- |
| 0 | the output slot |
| 1 | the slice header |
| 2 | the frame base |
| 3 | the unread length, then the number of pairs written |
| 4 | the capacity, then the scratch error slot at `frame + 52` |
| 5 | the number of unread input bytes |
| 6 | the input cursor |
| 7 | the declared pair count |
| 8 | the pair buffer |
| 9 | the byte offset of the next value, from 4 in steps of 8 |
| 10 | the key |
| 11 | scratch |
| 12 | the value |

The constants keep the unsigned form that the Lean AST uses.
`.const 2147483649` is `0x80000001`, which is `okTag`.
`.const 4294967292` is minus 4, and `.const 4294967288` is minus 8.
-/

namespace Project.RustHashMap.Decoder

open Wasm

/-! ## The header -/


/-- The frame.  The body takes 64 bytes below the stack pointer and
keeps the base in local 2.  WAT lines 472 to 476. -/
def framePrologue : Program :=
  [.globalGet 0, .const 64, .sub, .localTee 2, .globalSet 0]

/-- The short-input arm of the header read.  Fewer than four bytes left
is the "unexpected end of input" error.  The body builds the
`io::Error` with `func 55`, turns it into the decode error with
`func 52`, writes the four error words into the output slot, and
leaves through the outer block.  The two `okTag` tests are dead
arms, because word 0 of a built error is a `String` capacity.
WAT lines 481 to 545. -/
def headerError : Program :=
  [.localGet 1, .load32 4, .localTee 3, .const 3, .gtU, .br_if 0,
    .localGet 2, .const 48, .add, .const 17, .const 1049080, .const 27,
    .call 55, .localGet 2, .localGet 2, .load64 52, .store64 32,
    .localGet 2, .localGet 2, .load32 60, .store32 40, .localGet 2,
    .load32 48, .localTee 3, .const 2147483649, .eq, .br_if 1, .localGet 2,
    .localGet 3, .store32 48, .localGet 2, .localGet 2, .load64 32,
    .store64 52, .localGet 2, .localGet 2, .load32 40, .store32 60,
    .localGet 2, .const 16, .add, .localGet 2, .const 48, .add, .call 52,
    .localGet 2, .load32 16, .localTee 3, .const 2147483649, .eq, .br_if 1,
    .localGet 2, .load32 20, .localSet 4, .localGet 0, .localGet 2,
    .load64 24, .store64 8, .localGet 0, .localGet 4, .store32 4,
    .localGet 0, .localGet 3, .store32 0, .br 3]

/-- The header read.  It takes four bytes off the slice, advances the
cursor and the remaining length, and keeps the declared pair count in
local 7.  A count that is not zero goes on to the allocation.
WAT lines 547 to 564. -/
def headerRead : Program :=
  [.localGet 1, .localGet 3, .const 4294967292, .add, .localTee 5,
    .store32 4, .localGet 1, .localGet 1, .load32 0, .localTee 3, .const 4,
    .add, .localTee 6, .store32 0, .localGet 3, .load32 0, .localTee 7,
    .br_if 1]

/-- The header block: the short-input arm and the read that follows it.
WAT lines 480 to 564. -/
def headerPhase : Program :=
  .block 0 0 headerError :: headerRead

/-- The empty vector.  A declared count of zero allocates nothing.  The
output slot takes the tag `okTag`, the capacity 0, the dangling
pointer 4, and the length 0.  WAT lines 566 to 572. -/
def emptyResult : Program :=
  [.localGet 0, .constI64 4, .store64 8, .localGet 0, .constI64 2147483649,
    .store64 0, .br 1]

/-- The header stage: the header block and the empty vector that follows
it.  WAT lines 479 to 572. -/
def headerStage : Program :=
  .block 0 0 headerPhase :: emptyResult

/-! ## The loop -/


/-- The allocation of the pair buffer.  The capacity is `min(count, 512)`
and the request is `8 * capacity` bytes with alignment 4.  The three
words of the vector go to frame offsets 4, 8 and 12.  Local 4 then
holds `frame + 52`, the tail of the `io::Error` slot that starts at
`frame + 48`, and local 9 holds 4, the byte offset of the first value.
WAT lines 577 to 610. -/
def allocPair : Program :=
  [.localGet 7, .const 512, .localGet 7, .const 512, .ltU, .select,
    .localTee 4, .const 3, .shl, .localTee 3, .const 4, .call 58,
    .localTee 8, .eqz, .br_if 0, .const 0, .localSet 3, .localGet 2,
    .const 0, .store32 12, .localGet 2, .localGet 8, .store32 8,
    .localGet 2, .localGet 4, .store32 4, .localGet 2, .const 48, .add,
    .const 4, .add, .localSet 4, .const 4, .localSet 9]

/-- The short-input arm of one loop step.  Fewer than four bytes left is
the same "unexpected end of input" error, and `br 7` leaves the whole
loop through the error return.  The two `okTag` tests are dead in the
same way as in `headerError`, and they lead to the zero key.
WAT lines 617 to 666. -/
def shortPairError : Program :=
  [.localGet 5, .const 3, .gtU, .br_if 0, .localGet 2, .const 48, .add,
    .const 17, .const 1049080, .const 27, .call 55, .localGet 2,
    .localGet 4, .load64 0, .store64 32, .localGet 2, .localGet 4,
    .load32 8, .store32 40, .localGet 2, .load32 48, .localTee 10,
    .const 2147483649, .eq, .br_if 1, .localGet 4, .localGet 2, .load64 32,
    .store64 0, .localGet 4, .localGet 2, .load32 40, .store32 8,
    .localGet 2, .localGet 10, .store32 48, .localGet 2, .const 16, .add,
    .localGet 2, .const 48, .add, .call 52, .localGet 2, .load32 16,
    .localTee 11, .const 2147483649, .eq, .br_if 1, .br 7]

/-- The key read.  It takes four bytes off the slice.  Four or more bytes
left goes on to the value read in one step of eight bytes.  Fewer
takes the second error arm.  WAT lines 668 to 691. -/
def keyRead : Program :=
  [.localGet 1, .localGet 5, .const 4294967292, .add, .localTee 12,
    .store32 4, .localGet 1, .localGet 6, .const 4, .add, .localTee 11,
    .store32 0, .localGet 6, .load32 0, .localSet 10, .localGet 12,
    .const 4, .geU, .br_if 2, .localGet 11, .localSet 6, .localGet 12,
    .localSet 5, .br 1]

/-- The key block: the short-input arm and the key read.
WAT lines 616 to 691. -/
def keyStage : Program :=
  .block 0 0 shortPairError :: keyRead

/-- The key of a step that runs out of input.  WAT lines 693 to 694. -/
def zeroKey : Program :=
  [.const 0, .localSet 10]

/-- The key block and the zero key that follows it.
WAT lines 615 to 694. -/
def keyOutcome : Program :=
  .block 0 0 keyStage :: zeroKey

/-- The short-input arm of the value read.  It builds the same error.
The `br_if 4` leaves through the error return when word 0 is not
`okTag`.  The `br 1` after it appends a pair with the value 0, and it
is dead, because word 0 of a built error is never `okTag`.
WAT lines 696 to 743. -/
def shortValueError : Program :=
  [.localGet 2, .const 48, .add, .const 17, .const 1049080, .const 27,
    .call 55, .localGet 2, .localGet 4, .load64 0, .store64 32, .localGet 2,
    .localGet 4, .load32 8, .store32 40, .const 0, .localSet 12,
    .localGet 2, .load32 48, .localTee 11, .const 2147483649, .eq, .br_if 1,
    .localGet 4, .localGet 2, .load64 32, .store64 0, .localGet 4,
    .localGet 2, .load32 40, .store32 8, .localGet 2, .localGet 11,
    .store32 48, .localGet 2, .const 16, .add, .localGet 2, .const 48, .add,
    .call 52, .localGet 2, .load32 16, .localTee 11, .const 2147483649, .ne,
    .br_if 4, .br 1]

/-- The value block: the key outcome and the short-input arm of the
value.  WAT lines 614 to 743. -/
def valueStage : Program :=
  .block 0 0 keyOutcome :: shortValueError

/-- The pair read.  One step takes eight input bytes, the key at the
cursor and the value at `cursor + 4`.  WAT lines 745 to 761. -/
def pairRead : Program :=
  [.localGet 1, .localGet 5, .const 4294967288, .add, .localTee 5,
    .store32 4, .localGet 1, .localGet 6, .const 8, .add, .localTee 11,
    .store32 0, .localGet 6, .load32 4, .localSet 12, .localGet 11,
    .localSet 6]

/-- The pair block: the value block and the pair read.
WAT lines 613 to 761. -/
def pairStage : Program :=
  .block 0 0 valueStage :: pairRead

/-- The amortized grow.  It runs only when the length word equals the
capacity word, and `func 26` doubles the buffer.
WAT lines 764 to 775. -/
def growBody : Program :=
  [.localGet 3, .localGet 2, .load32 4, .ne, .br_if 0, .localGet 2,
    .const 4, .add, .call 26, .localGet 2, .load32 8, .localSet 8]

/-- The append.  The key goes to `buffer + 8 i` and the value to
`buffer + 8 i + 4`.  The length word takes `i + 1`, the offset takes
eight more, and the loop runs again while the length is not the
declared count.  WAT lines 777 to 801. -/
def appendPair : Program :=
  [.localGet 8, .localGet 9, .add, .localTee 11, .localGet 12, .store32 0,
    .localGet 11, .const 4294967292, .add, .localGet 10, .store32 0,
    .localGet 2, .localGet 3, .const 1, .add, .localTee 3, .store32 12,
    .localGet 9, .const 8, .add, .localSet 9, .localGet 7, .localGet 3, .ne,
    .br_if 0]

/-- One loop step: the pair block, the grow block, and the append.
WAT lines 612 to 801. -/
def pairLoopBody : Program :=
  .block 0 0 pairStage :: .block 0 0 growBody :: appendPair

/-- The accepting return.  The output slot takes the length, the capacity
and the pointer, and then the tag `okTag`.  WAT lines 803 to 814. -/
def okReturn : Program :=
  [.localGet 0, .localGet 2, .load32 12, .store32 12, .localGet 0,
    .localGet 2, .load64 4, .store64 4, .localGet 0, .const 2147483649,
    .store32 0, .br 2]

/-- The decode stage: the allocation, the loop, and the accepting return.
WAT lines 577 to 814. -/
def decodeStage : Program :=
  allocPair ++ .loop 0 0 pairLoopBody :: okReturn

/-- The allocation-failure arm.  It is dead, because `func 58` never
returns null.  See the `Func1Spec` docstring.  WAT lines 816 to 819. -/
def deadAllocError : Program :=
  [.const 4, .localGet 3, .call 99, .unreachable]

/-- The allocation stage: the decode stage and the dead arm.
WAT lines 576 to 819. -/
def allocStage : Program :=
  .block 0 0 decodeStage :: deadAllocError

/-! ## The body -/


/-- The error return.  It reads the four error words out of the scratch
slot at `frame + 16`, writes them into the output slot, and calls the
deallocate of the pair buffer.  A capacity of zero calls nothing, and
absolute `func 60` has an empty body.  WAT lines 821 to 844. -/
def errorReturn : Program :=
  [.localGet 2, .load32 20, .localSet 3, .localGet 0, .localGet 2,
    .load64 24, .store64 8, .localGet 0, .localGet 3, .store32 4,
    .localGet 0, .localGet 11, .store32 0, .localGet 2, .load32 4,
    .localTee 3, .eqz, .br_if 0, .localGet 8, .localGet 3, .const 3, .shl,
    .const 4, .call 60]

/-- The body of the outer block: the header stage, the empty call of
absolute `func 33`, the allocation stage, and the error return.
WAT lines 478 to 844. -/
def outerBody : Program :=
  .block 0 0 headerStage :: .call 33 :: .block 0 0 allocStage ::
    errorReturn

/-- The restore of the stack pointer.  Every path reaches it.
WAT lines 846 to 849. -/
def stackEpilogue : Program :=
  [.localGet 2, .const 64, .add, .globalSet 0]

/-- The decoder is the frame, the outer block, and the stack
epilogue. -/
theorem func1_shape :
    Project.RustHashMap.func1 =
      framePrologue ++ .block 0 0 outerBody :: stackEpilogue := by
  rfl

end Project.RustHashMap.Decoder
