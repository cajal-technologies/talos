import Project.RustHashMap.ReadAllDefs

/-!
# The tail of the `map_len` driver: program fragments

The `map_len` driver is local `func19`, absolute index 22.  Its read phase
is proved in `Project.RustHashMap.ReadAllPhase`.  This file splits the code
after the read phase into one definition per control block, so that the
proof of the tail can name each block.  `ReadAll.func19AfterRead` is the
whole tail, defined as `func19.drop 20`.

The tail is WAT lines 5413 to 5597 of
`programs/rust/build/rust_hash_map/program.wat`.  It does these steps:

1. It writes the input length at frame offset 284 and the input pointer at
   frame offset 280, then calls the borsh decoder (absolute `func 4`) with
   the 16-byte output slot at offset 288 and the slice header at offset 280.
2. It reads the first word of the output slot.  The value `0x80000001`
   means `Ok`.  Any other value means `Err`, and the code jumps to the
   error epilogue.
3. On `Ok` it checks the count of unread bytes at offset 284.  A count
   that is not zero is the "not all bytes read" error: the code builds an
   `io::Error` with `func 55`, drops the decoded pairs, and joins the
   error epilogue.
4. It stores the decoded triple `(capacity, pointer, length)` at frame
   offsets 12, 16 and 20, frees the input buffer, and calls
   `collect_entries` (absolute `func 5`) with the 32-byte map slot at
   offset 24.
5. It reads the item count from map offset 36, calls the marker `func 33`,
   allocates 1024 bytes, writes the count as four bytes, writes them to
   the output stream with `func 64`, and frees the buffer.
6. It drops the hash table and restores the stack pointer.

Every branch of the tail ends at the same stack epilogue, so the block
structure carries the control flow.  The constants keep the unsigned form
that the Lean AST uses: `i32.const -2147483647` is `0x80000001`, which is
`2147483649`, `i32.const -2147483648` is `2147483648`, and `i32.const -8`
is `4294967288`.
-/

namespace Project.RustHashMap.DriverTail

open Wasm

/-! ## The blocks, from the innermost outward -/

/-- The drop of the decoded pair buffer, on the "not all bytes read" path.
The buffer holds `8 * count` bytes with alignment 4.  A count of zero
leaves nothing to free.  WAT lines 5470 to 5480. -/
def dropDecoded : Program :=
  [.localGet 4, .eqz, .br_if 0, .localGet 6, .localGet 4, .const 3, .shl,
    .const 4, .call 60]

/-- The "not all bytes read" branch.  It builds the `io::Error` with the
static message at address 1049107, reads the four error words out of the
map slot, drops the decoded pairs, and then joins the error epilogue.
WAT lines 5446 to 5486. -/
def notAllReadBody : Program :=
  [.localGet 0, .load32 284, .eqz, .br_if 0, .localGet 0, .const 24, .add,
    .const 12, .const 1049107, .const 18, .call 55, .localGet 0, .load32 36,
    .localSet 7, .localGet 0, .load32 32, .localSet 8, .localGet 0,
    .load32 28, .localSet 5, .localGet 0, .load32 24, .localSet 1,
    .block 0 0 dropDecoded, .localGet 1, .const 2147483649, .ne, .br_if 2,
    .br 1]

/-- The choice between the "not all bytes read" error and the decoded
vector.  The fall-through arm loads the decoded length from offset 300 and
moves the capacity and the pointer into the reply registers.
WAT lines 5445 to 5494. -/
def decodeOutcome : Program :=
  .block 0 0 notAllReadBody ::
    [.localGet 0, .load32 300, .localSet 7, .localGet 4, .localSet 5,
      .localGet 6, .localSet 8]

/-- The release of the input byte vector before the collect call.  A
capacity of zero leaves nothing to free.  WAT lines 5504 to 5512. -/
def freeInput : Program :=
  [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1, .call 60]

/-- The reply.  It allocates 1024 bytes with alignment 1, writes the item
count as four unaligned bytes, writes them to the output stream, frees the
buffer, and then drops the hash table.  The table drop uses the bucket mask
at map offset 28 and the control pointer at map offset 24.  WAT lines 5524
to 5567. -/
def replyBody : Program :=
  [.const 1024, .const 1, .call 58, .localTee 1, .eqz, .br_if 0,
    .localGet 1, .localGet 3, .store32 0, .localGet 1, .const 4, .call 64,
    .localGet 1, .const 1024, .const 1, .call 60, .localGet 0, .load32 28,
    .localTee 1, .eqz, .br_if 2, .localGet 1, .const 3, .shl, .localTee 3,
    .localGet 1, .add, .const 17, .add, .localTee 1, .eqz, .br_if 2,
    .localGet 0, .load32 24, .localGet 3, .sub, .const 4294967288, .add,
    .localGet 1, .const 8, .call 60, .br 2]

/-- The collect call, the marker call, and the reply.  The four
instructions after the reply block run only when the allocator returns
zero.  The allocator never returns zero, so they are dead.  WAT lines 5513
to 5571. -/
def collectAndReply : Program :=
  [.localGet 0, .const 24, .add, .localGet 0, .const 12, .add, .call 5,
    .localGet 0, .load32 36, .localSet 3, .call 33,
    .block 0 0 replyBody, .const 1, .const 1024, .call 99, .unreachable]

/-- The `Ok` path of the decode.  WAT lines 5442 to 5571. -/
def okPath : Program :=
  [.localGet 0, .load32 296, .localSet 6] ++
  .block 0 0 decodeOutcome ::
  [.localGet 0, .localGet 7, .store32 20, .localGet 0, .localGet 8,
    .store32 16, .localGet 0, .localGet 5, .store32 12,
    .block 0 0 freeInput] ++
  collectAndReply

/-- The guard that separates the decoder `Ok` from the decoder `Err`.  The
first word of the output slot is `0x80000001` exactly when the decode
succeeded.  WAT lines 5431 to 5441. -/
def okGuard : Program :=
  [.localGet 0, .load32 288, .localTee 1, .const 2147483649, .eq, .br_if 0,
    .localGet 4, .localSet 5, .br 1]

/-- The `Ok` block: the guard and the path that follows it.  WAT lines 5431
to 5571. -/
def okBlock : Program :=
  .block 0 0 okGuard :: okPath

/-- The drop of the error string.  An error word whose high bit is already
set carries no allocation, so nothing is freed.  WAT lines 5573 to 5584. -/
def freeErrString : Program :=
  [.localGet 1, .const 2147483648, .or, .const 2147483648, .eq, .br_if 0,
    .localGet 5, .localGet 1, .const 1, .call 60]

/-- The error epilogue.  It frees the error string, then frees the input
byte vector.  WAT lines 5573 to 5591. -/
def errEpilogue : Program :=
  .block 0 0 freeErrString ::
    [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1,
      .call 60]

/-- The body of the outer block: the `Ok` block, then the error epilogue.
WAT lines 5430 to 5591. -/
def outerBody : Program :=
  .block 0 0 okBlock :: errEpilogue

/-! ## The tail -/

/-- The store of the slice header and the call of the borsh decoder.  Local
1 holds the input length and local 3 holds the input pointer, both left by
the read phase.  WAT lines 5413 to 5428. -/
def decodeCall : Program :=
  [.localGet 0, .localGet 1, .store32 284, .localGet 0, .localGet 3,
    .store32 280, .localGet 0, .const 288, .add, .localGet 0, .const 280,
    .add, .call 4, .localGet 0, .load32 292, .localSet 4]

/-- The restore of the stack pointer.  Every path reaches it.  WAT lines
5593 to 5596. -/
def stackEpilogue : Program :=
  [.localGet 0, .const 304, .add, .globalSet 0]

/-- The tail of the driver is the decode call, the outer block, and the
stack epilogue. -/
theorem func19AfterRead_shape :
    ReadAll.func19AfterRead =
      decodeCall ++ .block 0 0 outerBody :: stackEpilogue := by
  rfl

end Project.RustHashMap.DriverTail
