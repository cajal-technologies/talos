import Project.RustHashMap.InsertReadLoop

/-!
# The read phase of `map_insert`

The `map_insert` driver is local `func0`, absolute function 3.  WAT lines
30 to 469 hold it.  It takes a frame of 368 bytes below the entry stack
top.  This file proves the frame setup, the first chunk read and the read
loop, up to the two exits of the read block.  The frame base is concrete,
so every address fact is decidable.

The driver declares seven locals.  Locals 0 to 5 are `i32` and local 6 is
`i64`, so the read-loop core of `Project.RustHashMap.InsertRead` gets a
local tail of two slots.  The read phase never writes the two slots, so
they hold zero throughout.

## The frame

The frame map is `insertMap`, which is `<368, 56, 24>`.  The frame has
five regions:

- the head, 24 bytes at offset 0,
- the vector header, 12 bytes at offset 24,
- the middle, 20 bytes at offset 36,
- the chunk buffer, 256 bytes at offset 56,
- the top, 56 bytes at offset 312.

The `map_get` frame has three regions, because its vector header sits
next to its chunk buffer.  This frame keeps 20 dead bytes between them
and 56 dead bytes above the buffer, so this file splits five ways.

## The shape of the code

The driver differs from `map_get` and `map_remove` in three ways:

- Seven blocks open in a row at WAT 51 to 57.  Their ends are at WAT 464,
  359, 340, 286, 234, 180 and 172.  The read phase is the body of the
  seventh block.
- The first read has no block of its own.  WAT 58 to 65 read the first
  chunk, write the count to local 2, and test the count with `i32.eqz`.
- The branch sense is inverted.  The `br_if 0` at WAT 65 leaves the
  seventh block when the first read gives zero bytes.  The `map_get`
  driver branches on a non-zero count instead.

## What this file proves and what it hands over

The theorem `twp_insert_read_phase` starts at function entry and stops at
the two exits of the seventh block:

- The non-empty arm stops at WAT 123, the reload of the vector registers.
  The reload writes the capacity to local 2 and the pointer to local 1,
  which the core does not do, so this file leaves WAT 123 to 171 to the
  caller as `insRest7`.
- The empty arm stops at WAT 173, the first instruction after the end of
  the seventh block.  This file leaves WAT 173 to 179 to the caller as
  `insAfter7`.

See `Project.RustHashMap.InsertReadLoop` for the loop fragments and the
loop invariant, and `Project.RustHashMap.ReadAllDefs` for the frame map
and the prologue.
-/

namespace Project.RustHashMap.InsertRead

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.ReadAll (FrameMap insertMap insertMap_wf
  readPrologue ByteSlice_split_at ByteSlice_header_as_words
  pointsTo_u32_pair_as_u64 pointsTo_u32_address_eq vec_addr)
open scoped Wasm.SmallStep.Outcome

/-! ## Slices of the frame -/

/-- The five regions of the 368-byte driver frame: the head, the vector
header, the middle, the chunk buffer, and the top. -/
theorem ByteSlice_frame368 [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (hlen : bytes.length = 368) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop(∃ head header mid chunk top : List UInt8,
        ⌜head.length = 24 ∧ header.length = 12 ∧ mid.length = 20 ∧
          chunk.length = 256 ∧ top.length = 56⌝ ∗
        Slices.ByteSlice 0 ptr head ∗
        Slices.ByteSlice 0 (ptr + 24) header ∗
        Slices.ByteSlice 0 (ptr + 36) mid ∗
        Slices.ByteSlice 0 (ptr + 56) chunk ∗
        Slices.ByteSlice 0 (ptr + 312) top) := by
  iintro Hbytes
  icases (ByteSlice_split_at ptr 24 bytes (by simp [hlen])).mp $$ Hbytes
    with ⟨Hhead, Hrest⟩
  isimp only [UInt32.reduceToNat] at Hhead
  isimp only [UInt32.reduceToNat] at Hrest
  icases (ByteSlice_split_at (ptr + 24) 12 (bytes.drop 24)
    (by simp [hlen])).mp $$ Hrest with ⟨Hheader, Hrest⟩
  isimp only [UInt32.reduceToNat] at Hheader
  isimp only [UInt32.reduceToNat, UInt32.add_assoc, UInt32.reduceAdd]
    at Hrest
  icases (ByteSlice_split_at (ptr + 36) 20 ((bytes.drop 24).drop 12)
    (by simp [hlen])).mp $$ Hrest with ⟨Hmid, Hrest⟩
  isimp only [UInt32.reduceToNat] at Hmid
  isimp only [UInt32.reduceToNat, UInt32.add_assoc, UInt32.reduceAdd]
    at Hrest
  icases (ByteSlice_split_at (ptr + 56) 256
    (((bytes.drop 24).drop 12).drop 20)
    (by simp [hlen])).mp $$ Hrest with ⟨Hchunk, Htop⟩
  isimp only [UInt32.reduceToNat] at Hchunk
  isimp only [UInt32.reduceToNat, UInt32.add_assoc, UInt32.reduceAdd]
    at Htop
  iexists (bytes.take 24), ((bytes.drop 24).take 12),
    (((bytes.drop 24).drop 12).take 20),
    ((((bytes.drop 24).drop 12).drop 20).take 256),
    ((((bytes.drop 24).drop 12).drop 20).drop 256)
  isplitl_pureexact (by simp [hlen])
  iframe

/-! ## The frame of `map_insert` -/

/-- The frame base of the `map_insert` driver: 368 bytes below the entry
stack top. -/
def func0Base : UInt32 := entryStackTop - 368

theorem func0Base_eq : func0Base = 1048208 := by decide

/-! ## The program fragments

Each fragment names its WAT span.  The body of a block is not a suffix of
the enclosing list, so `blockBody` takes it from the head instruction.
The `raw` fragments come from `func0` this way.  The public fragments are
then built from the head down, so that each one is a cons cell whose tail
is another public fragment.  `func0_shape` proves that the two agree. -/

/-- The body of the block that starts a program fragment. -/
def blockBody (p : Program) : Program :=
  match p with
  | .block _ _ body :: _ => body
  | _ => []

private def raw1 : Program := blockBody (Project.RustHashMap.func0.drop 19)
private def raw2 : Program := blockBody raw1
private def raw3 : Program := blockBody raw2
private def raw4 : Program := blockBody raw3
private def raw5 : Program := blockBody raw4
private def raw6 : Program := blockBody raw5
private def raw7 : Program := blockBody raw6

/-- The epilogue of the driver: WAT 465 to 468. -/
@[reducible] def insEpilogue : Program :=
  Project.RustHashMap.func0.drop 20

/-- The code after the second block, WAT 360 to 463. -/
@[reducible] def insAfter2 : Program := raw1.drop 1

/-- The code after the third block, WAT 341 to 358. -/
@[reducible] def insAfter3 : Program := raw2.drop 1

/-- The code after the fourth block, WAT 287 to 339. -/
@[reducible] def insAfter4 : Program := raw3.drop 1

/-- The code after the fifth block, WAT 235 to 285. -/
@[reducible] def insAfter5 : Program := raw4.drop 1

/-- The code after the sixth block, WAT 181 to 233. -/
@[reducible] def insAfter6 : Program := raw5.drop 1

/-- The code after the seventh block, WAT 173 to 179.  The empty arm of
the read phase runs it: it writes the empty key and value slice, sets
local 1 to one, and sets local 2 to zero. -/
def insAfter7 : Program :=
  [.localGet 0, .constI64 1, .store64 312, .const 1, .localSet 1,
    .const 0, .localSet 2]

/-- The first read, WAT 58 to 65.  The `br_if 0` leaves the seventh block
when the read gives zero bytes. -/
def insFirstRead : Program :=
  [.localGet 0, .const insertMap.chunkOff, .add, .const 256, .call 63,
    .localTee 2, .eqz, .br_if 0]

/-- The rest of the seventh block, WAT 123 to 171: the reload of the
vector registers and the inline decode of the key and the value. -/
@[reducible] def insRest7 : Program := raw7.drop 9

/-- The body of the seventh block, WAT 58 to 171.  The first read is
written out, so that the head of the list is a cons cell. -/
@[reducible] def insBlock7Body : Program :=
  .localGet 0 :: .const insertMap.chunkOff :: .add :: .const 256 ::
    .call 63 :: .localTee 2 :: .eqz :: .br_if 0 ::
    .loop 0 0 readLoopBody :: insRest7

/-- The body of the sixth block, WAT 57 to 179. -/
@[reducible] def insBlock6Body : Program :=
  .block 0 0 insBlock7Body :: insAfter7

/-- The body of the fifth block, WAT 56 to 233. -/
@[reducible] def insBlock5Body : Program :=
  .block 0 0 insBlock6Body :: insAfter6

/-- The body of the fourth block, WAT 55 to 285. -/
@[reducible] def insBlock4Body : Program :=
  .block 0 0 insBlock5Body :: insAfter5

/-- The body of the third block, WAT 54 to 339. -/
@[reducible] def insBlock3Body : Program :=
  .block 0 0 insBlock4Body :: insAfter4

/-- The body of the second block, WAT 53 to 358. -/
@[reducible] def insBlock2Body : Program :=
  .block 0 0 insBlock3Body :: insAfter3

/-- The body of the first block, WAT 52 to 463. -/
@[reducible] def insOuterBody : Program :=
  .block 0 0 insBlock2Body :: insAfter2

/-- The whole driver: the frame setup, the seven nested blocks, and the
epilogue.  This lemma pins every fragment above to the generated code. -/
theorem func0_shape :
    Project.RustHashMap.func0 =
      readPrologue insertMap ++
        .block 0 0 insOuterBody :: insEpilogue := by
  rfl

theorem insOuterBody_shape :
    insOuterBody = .block 0 0 insBlock2Body :: insAfter2 := by
  rfl

theorem insBlock2Body_shape :
    insBlock2Body = .block 0 0 insBlock3Body :: insAfter3 := by
  rfl

theorem insBlock3Body_shape :
    insBlock3Body = .block 0 0 insBlock4Body :: insAfter4 := by
  rfl

theorem insBlock4Body_shape :
    insBlock4Body = .block 0 0 insBlock5Body :: insAfter5 := by
  rfl

theorem insBlock5Body_shape :
    insBlock5Body = .block 0 0 insBlock6Body :: insAfter6 := by
  rfl

theorem insBlock6Body_shape :
    insBlock6Body = .block 0 0 insBlock7Body :: insAfter7 := by
  rfl

theorem insBlock7Body_shape :
    insBlock7Body =
      insFirstRead ++ .loop 0 0 readLoopBody :: insRest7 := by
  rfl

/-! ## The control frames of the seven blocks -/

/-- One of the seven block frames.  Every block has no parameter and no
result, and the operand stack below it is empty. -/
def insFrame (body continuation : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := body, continuation := continuation, belowStack := [] }

/-- The seven frames inside the seventh block, innermost first. -/
def insControls7 (afterRead : Program) : List ControlFrame :=
  [insFrame insBlock7Body insAfter7,
    insFrame insBlock6Body insAfter6,
    insFrame insBlock5Body insAfter5,
    insFrame insBlock4Body insAfter4,
    insFrame insBlock3Body insAfter3,
    insFrame insBlock2Body insAfter2,
    insFrame insOuterBody afterRead]

/-- The six frames that stay after the branch out of the seventh
block. -/
def insControls6 (afterRead : Program) : List ControlFrame :=
  (insControls7 afterRead).drop 1

/-! ## The locals -/

/-- The locals after the read loop.  The reload of WAT 123 belongs to the
caller, so the capacity and the pointer are not in registers yet.  Local
1 and local 2 hold zero, local 3 holds the last chunk byte, and local 4
holds the vector length that the last push wrote.  Local 5 and local 6
hold the zero that the frame setup left. -/
def afterReadLocalsIns (byte length : UInt32) : Locals :=
  ⟨[], [.i32 func0Base, .i32 0, .i32 0, .i32 byte, .i32 length,
    .i32 0, .i64 0], []⟩

/-- The locals at WAT 173.  The first read gave zero bytes, so local 2
holds zero, and every other local still holds the zero that the frame
setup left. -/
def emptyArmLocals : Locals :=
  ⟨[], [.i32 func0Base, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0],
    []⟩

/-! ## The two exits of the read block -/

/-- The resources after the read loop: the whole input is in the vector,
and the input stream is empty. -/
def AfterReadIns [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (input reserve head mid chunk top : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8) : HeapIProp :=
  iprop(
    RuntimeContext ∗
    StackPointer func0Base ∗
    StackReserve (func0Base - 16) reserve ∗
    Slices.ByteSlice 0 func0Base head ∗
    VecU8 heapId (func0Base + 24) capacity ptr input ∗
    Slices.ByteSlice 0 (func0Base + 36) mid ∗
    Slices.ByteSlice 0 (func0Base + 56) chunk ∗
    Slices.ByteSlice 0 (func0Base + 312) top ∗
    BumpHeap heapId storedCursor frontier history ∗
    Streams [] output false ∗
    ⌜head.length = 24 ∧ mid.length = 20 ∧ chunk.length = 256 ∧
      top.length = 56 ∧ PushVecFacts capacity ptr frontier⌝)

/-- The resources at WAT 173.  The input was empty, so the vector still
holds the empty allocation that the frame setup wrote, and the chunk
buffer still holds the 256 zero bytes of the `memory.fill`. -/
def EmptyArmIns [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (reserve head mid top : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8) : HeapIProp :=
  iprop(
    RuntimeContext ∗
    StackPointer func0Base ∗
    StackReserve (func0Base - 16) reserve ∗
    Slices.ByteSlice 0 func0Base head ∗
    VecU8 heapId (func0Base + 24) 0 1 [] ∗
    Slices.ByteSlice 0 (func0Base + 36) mid ∗
    Slices.ByteSlice 0 (func0Base + 56) (List.replicate 256 0) ∗
    Slices.ByteSlice 0 (func0Base + 312) top ∗
    BumpHeap heapId storedCursor frontier history ∗
    Streams [] output false ∗
    ⌜head.length = 24 ∧ mid.length = 20 ∧ top.length = 56⌝)

private theorem func0_initialLocals :
    Project.RustHashMap.func0Def.toLocals [] =
      ⟨[], [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0],
        []⟩ := by
  rfl

private theorem ofNat_ne_zero (n : Nat) (h : 0 < n)
    (hlt : n < 4294967296) : UInt32.ofNat n ≠ 0 := by
  have hsize : UInt32.size = 4294967296 := rfl
  intro h0
  have := congrArg UInt32.toNat h0
  rw [UInt32.toNat_ofNat_of_lt' (by rw [hsize]; omega)] at this
  simp at this; omega

set_option maxHeartbeats 2000000 in
/-- The read phase of the `map_insert` driver: the frame setup, the seven
blocks, the first read and the read loop.  The caller owns the 384 bytes
from the reserve base to the entry stack top.  The non-empty arm stops at
the reload of WAT 123 and the empty arm at WAT 173. -/
theorem twp_insert_read_phase [WasmSmallStepGS hlc Universal.State]
    (hfunc98 : Func98Spec (hlc := hlc))
    (heapId : GName) (input output frameBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterRead : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hframe : frameBytes.length = 384) :
    iprop(
      RuntimeContext ∗
      StackPointer entryStackTop ∗
      Slices.ByteSlice 0 (func0Base - 16) frameBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output false ∗
      ((∀ capacity : UInt32, ∀ ptr : UInt32, ∀ storedCursor' : UInt32,
        ∀ frontier' : Nat, ∀ history' : AllocationHistory,
        ∀ reserve : List UInt8, ∀ head : List UInt8, ∀ mid : List UInt8,
        ∀ chunk : List UInt8, ∀ top : List UInt8,
        ∀ byte : UInt32, ∀ length : UInt32,
        ⌜input ≠ []⌝ -∗
        AfterReadIns heapId capacity ptr input reserve head mid chunk top
          storedCursor' frontier' history' output -∗
        WP (.running
          ⟨afterReadLocalsIns byte length, insRest7, arity, remainder,
            insControls7 afterRead ++ controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }]) ∧
      ((∀ reserve : List UInt8, ∀ head : List UInt8, ∀ mid : List UInt8,
        ∀ top : List UInt8,
        ⌜input = []⌝ -∗
        EmptyArmIns heapId reserve head mid top storedCursor frontier
          history output -∗
        WP (.running
          ⟨emptyArmLocals, insAfter7, arity, remainder,
            insControls6 afterRead ++ controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }]) ∧
      (∀ remaining' : List UInt8,
        Streams remaining' output true -∗
          Φ (.trapped (.host OOM.trapMessage)))))) ⊢
      WP (.running
        ⟨Project.RustHashMap.func0Def.toLocals [],
          readPrologue insertMap ++
            .block 0 0 insOuterBody :: afterRead,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hframe, Hbump, Hstreams, Hcont⟩
  rw [func0_initialLocals]
  -- the reserve and the five frame regions
  icases (ByteSlice_split_at (func0Base - 16) 16 frameBytes
    (by simp [hframe])).mp $$ Hframe with ⟨Hreserve, Hframe⟩
  isimp only [UInt32.reduceToNat] at Hreserve
  isimp only [UInt32.reduceToNat,
    show func0Base - 16 + 16 = func0Base by decide] at Hframe
  ihave Hframe := ByteSlice_frame368 func0Base (frameBytes.drop 16)
    (by simp [hframe]) $$ Hframe
  icases Hframe with ⟨%head, %header, %mid, %chunk, %top, %hlens,
    Hhead, Hheader, Hmid, Hchunk, Htop⟩
  isimp only [show func0Base + 56 = func0Base + insertMap.chunkOff
    by decide] at Hchunk
  isimp only [show func0Base + 24 = func0Base + insertMap.vecOff
    by decide] at Hheader
  ihave Hreserve : StackReserve (func0Base - 16) (frameBytes.take 16) $$
      [Hreserve]
  · unfold StackReserve
    isplitl_pureexact (by simp [hframe])
    iexact Hreserve
  ihave Hwords := ByteSlice_header_as_words
    (func0Base + insertMap.vecOff) header hlens.2.1 (by decide) $$ Hheader
  icases Hwords with ⟨%oldCapacity, %oldPtr, %oldLength, HoldCapacity,
    HoldPtr, HoldLength⟩
  ihave HoldPair := (pointsTo_u32_pair_as_u64
    (func0Base + insertMap.vecOff) oldCapacity oldPtr).mp $$
    [HoldCapacity HoldPtr]
  · iframe
  isimp only [UInt32.add_assoc] at HoldLength
  -- the frame setup
  isimp only [StackPointer] at Hsp
  simp only [readPrologue, List.cons_append, List.nil_append]
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
    rewriting [show entryStackTop - insertMap.frame = func0Base by decide]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer func0Base $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind twp_store32 (address := func0Base)
    (offset := insertMap.vecOff + 8) oldLength (by decide) (by decide)
    (by decide) (by decide) with HoldLength
  wasm_twp_pures [twp_localGet]
  iapply twp_pureStep _ _ _ (fun _ => Step.constI64)
  wasm_twp_bind twp_store64 (address := func0Base)
    (offset := insertMap.vecOff)
    (oldCapacity.toUInt64 ||| (oldPtr.toUInt64 <<< 32))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) with HoldPair => Hpair
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show insertMap.chunkOff + func0Base = func0Base + insertMap.chunkOff
    by decide]
  wasm_twp_pures [twp_const twp_const]
  isimp only [Slices.ByteSlice] at Hchunk
  icases Hchunk with ⟨%_hchunkNowrap, HchunkBytes⟩
  iapply twp_memoryFill32 chunk (by simp [hlens.2.2.2.1]) (by decide)
    (by decide) $$ HchunkBytes
  iintro HchunkBytes
  isimp only [hlens.2.2.2.1,
    show (0 : UInt32).toUInt8 = 0 from rfl] at HchunkBytes
  ihave Hchunk : Slices.ByteSlice 0 (func0Base + insertMap.chunkOff)
      (List.replicate 256 0) $$ [HchunkBytes]
  · unfold Slices.ByteSlice
    isplitl_pureexact (by simp only [List.length_replicate]; decide)
    iexact HchunkBytes
  ihave HpairWords : iprop(
      pointsTo_u32 0 (func0Base + insertMap.vecOff) 0 ∗
      pointsTo_u32 0 (func0Base + insertMap.vecOff + 4) 1) $$ [Hpair]
  · iapply (pointsTo_u32_pair_as_u64 (func0Base + insertMap.vecOff) 0 1).mpr
    rw [show (0 : UInt32).toUInt64 ||| ((1 : UInt32).toUInt64 <<< 32) =
      (4294967296 : UInt64) by decide]
    iexact Hpair
  icases HpairWords with ⟨Hcapacity, Hptr⟩
  ihave HoldLength := pointsTo_u32_address_eq
    (vec_addr insertMap func0Base 8).symm $$ HoldLength
  ihave Hvec : VecU8 heapId (func0Base + insertMap.vecOff) 0 1 [] $$
      [Hcapacity Hptr HoldLength]
  · unfold VecU8 RawVecHeader VecStorage
    isimp only [List.length_nil,
      show UInt32.ofNat 0 = (0 : UInt32) from rfl]
    isplitl [Hcapacity Hptr]
    · isplitl [Hcapacity]
      · iexact Hcapacity
      · iexact Hptr
    · isplitl [HoldLength]
      · iexact HoldLength
      · ileft
        ipureintro
        trivial
  -- the seven blocks
  wasm_twp_pures [twp_block twp_block twp_block twp_block twp_block
    twp_block twp_block]
  simp only [List.drop_zero]
  -- the first read
  iapply twp_read_chunk func0Base (List.replicate 256 0)
    input output []
    [.i32 func0Base, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0]
    (stack := []) (code := .localTee 2 :: .eqz :: .br_if 0 ::
      .loop 0 0 readLoopBody :: insRest7)
    rfl (by rw [List.length_replicate])
  isplitl_exacts [Hruntime Hstreams Hchunk]
  iintro Hruntime Hstreams Hchunk %hcount
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hempty : input = []
  · -- an empty input: leave the seventh block at once
    subst hempty
    isimp only [List.length_nil, Nat.min_zero, List.take_zero,
      List.drop_zero, List.nil_append] at Hchunk
    isimp only [List.length_nil, Nat.min_zero, List.drop_zero] at Hstreams
    simp only [List.length_nil, Nat.min_zero,
      show UInt32.ofNat 0 = (0 : UInt32) from rfl]
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (depth := 0) (targetCode := insAfter7)
      (targetControl := insControls6 afterRead ++ controls)
      (targetValues := []) (by decide)
      (by simp only [insControls6, insControls7, insFrame, List.drop_succ_cons,
        List.drop_zero]; rfl)
    ihave Hempty := BI.and_elim_r $$ Hcont
    ihave Hempty := BI.and_elim_l $$ Hempty
    isimp only [emptyArmLocals] at Hempty
    isimp only [show func0Base + insertMap.chunkOff = func0Base + 56
      by decide] at Hchunk
    isimp only [show func0Base + insertMap.vecOff = func0Base + 24
      by decide] at Hvec
    iapply_pure Hempty $$ %(frameBytes.take 16) %head %mid %top => trivial
    unfold EmptyArmIns
    isplitl_exacts [Hruntime Hsp Hreserve Hhead Hvec Hmid Hchunk Htop
      Hbump Hstreams]
    ipureexact ⟨hlens.1, hlens.2.2.1, hlens.2.2.2.2⟩
  · -- a nonempty input: run the loop
    have hpos : 0 < input.length := List.length_pos_of_ne_nil hempty
    have hcountPos : 0 < min 256 input.length := by omega
    have hcountLe : min 256 input.length ≤ input.length :=
      Nat.min_le_right _ _
    iapply twp_eqz (result := 0)
      (by rw [if_neg (ofNat_ne_zero _ hcountPos (by omega))])
    iapply twp_brIfZero
    let initial : LoopState :=
      { pushed := []
        chunk := input.take (min 256 input.length)
        index := 0
        chunkTail := (List.replicate 256 0).drop (min 256 input.length)
        remaining := input.drop (min 256 input.length)
        capacity := 0
        ptr := 1
        shadow := frameBytes.take 16
        storedCursor := storedCursor
        frontier := frontier
        history := history
        aux3 := 0
        aux4 := 0 }
    have htakeLen : (input.take (min 256 input.length)).length - 0 =
        min 256 input.length := by
      simp only [List.length_take, Nat.sub_zero]
      exact Nat.min_eq_left hcountLe
    have Hloop := twp_read_loop hfunc98 func0Base heapId
      input output [.i32 0, .i64 0] insRest7 arity remainder
      (insControls7 afterRead ++ controls) calls s E Φ (by decide) initial
    simp only [loopLocals, initial, htakeLen, insControls7,
      insFrame, List.cons_append, List.nil_append,
      show UInt32.ofNat 0 = (0 : UInt32) from rfl] at Hloop
    iapply Hloop
    unfold LoopInv
    simp only [List.take_zero, List.append_nil, List.nil_append]
    isplitl_exacts [Hruntime Hsp Hreserve Hchunk Hvec Hbump Hstreams]
    isplitl_pureexact (by
      refine ⟨(List.take_append_drop _ input).symm, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
      · simp only [List.length_take]; omega
      · simp only [List.length_take, List.length_drop, List.length_replicate]
        omega)
    unfold LoopContinuation
    isplit
    · iintro %finalCapacity %finalPtr %finalStoredCursor %finalFrontier
        %finalHistory %finalShadow %finalChunk %aux3 %aux4
        Hruntime Hsp Hreserve Hchunk Hvec Hbump Hstreams %hfinal
      simp only [afterLoopLocals]
      ihave Hnormal := BI.and_elim_l $$ Hcont
      isimp only [afterReadLocalsIns, insControls7, insControls6, insFrame,
        List.cons_append, List.nil_append] at Hnormal
      isimp only [show func0Base + insertMap.chunkOff = func0Base + 56
        by decide] at Hchunk
      isimp only [show func0Base + insertMap.vecOff = func0Base + 24
        by decide] at Hvec
      iapply_pure Hnormal $$ %finalCapacity %finalPtr %finalStoredCursor
        %finalFrontier %finalHistory %finalShadow %head %mid %finalChunk
        %top %aux3 %aux4 => exact hempty
      unfold AfterReadIns
      isplitl_exacts [Hruntime Hsp Hreserve Hhead Hvec Hmid Hchunk Htop
        Hbump Hstreams]
      ipureexact ⟨hlens.1, hlens.2.2.1, hfinal.1, hlens.2.2.2.2, hfinal.2⟩
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := BI.and_elim_r $$ Hoom
      iapply Hoom $$ %remaining' Hstreams

end Project.RustHashMap.InsertRead
