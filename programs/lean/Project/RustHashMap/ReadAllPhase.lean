import Project.RustHashMap.ReadAllLoop

/-!
# The input loop of the hash map drivers: the read phase of `map_len`

The `map_len` driver takes a frame of 304 bytes below the entry stack top.
This file proves the frame setup, the first chunk read, the read loop, and
the reload of the vector registers, up to the exit of the read block.  The
frame base is concrete, so every address fact is decidable.

The core is parameterised by a `FrameMap`.  This file is the instance of
the core at `lenMap`, the frame map of absolute function 22.

See `Project.RustHashMap.ReadAllDefs` for the fragments, the frame map,
and the loop invariant.
-/

namespace Project.RustHashMap.ReadAll

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open scoped Wasm.SmallStep.Outcome

/-! ## Slices of the frame -/

/-- The five regions of the 304-byte driver frame: the head, the chunk
buffer, the eight-byte slice, the vector header, and the tail. -/
theorem ByteSlice_frame304 [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (hlen : bytes.length = 304) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop(∃ head chunk slice header tail : List UInt8,
        ⌜head.length = 24 ∧ chunk.length = 256 ∧ slice.length = 8 ∧
          header.length = 12 ∧ tail.length = 4⌝ ∗
        Slices.ByteSlice 0 ptr head ∗
        Slices.ByteSlice 0 (ptr + 24) chunk ∗
        Slices.ByteSlice 0 (ptr + 280) slice ∗
        Slices.ByteSlice 0 (ptr + 288) header ∗
        Slices.ByteSlice 0 (ptr + 300) tail) := by
  iintro Hbytes
  icases (ByteSlice_split_at ptr 24 bytes (by simp [hlen])).mp $$ Hbytes
    with ⟨Hhead, Hrest⟩
  isimp only [UInt32.reduceToNat] at Hhead
  isimp only [UInt32.reduceToNat] at Hrest
  icases (ByteSlice_split_at (ptr + 24) 256 (bytes.drop 24)
    (by simp [hlen])).mp $$ Hrest with ⟨Hchunk, Hrest⟩
  isimp only [UInt32.reduceToNat] at Hchunk
  isimp only [UInt32.reduceToNat, UInt32.add_assoc, UInt32.reduceAdd] at Hrest
  icases (ByteSlice_split_at (ptr + 280) 8 ((bytes.drop 24).drop 256)
    (by simp [hlen])).mp $$ Hrest with ⟨Hslice, Hrest⟩
  isimp only [UInt32.reduceToNat] at Hslice
  isimp only [UInt32.reduceToNat, UInt32.add_assoc, UInt32.reduceAdd] at Hrest
  icases (ByteSlice_split_at (ptr + 288) 12 (((bytes.drop 24).drop 256).drop 8)
    (by simp [hlen])).mp $$ Hrest with ⟨Hheader, Htail⟩
  isimp only [UInt32.reduceToNat] at Hheader
  isimp only [UInt32.reduceToNat, UInt32.add_assoc, UInt32.reduceAdd] at Htail
  iexists (bytes.take 24), ((bytes.drop 24).take 256),
    (((bytes.drop 24).drop 256).take 8),
    ((((bytes.drop 24).drop 256).drop 8).take 12),
    ((((bytes.drop 24).drop 256).drop 8).drop 12)
  isplitl_pureexact (by simp [hlen])
  iframe

/-! ## The frame of `map_len` -/

/-- The frame base of the `map_len` driver: 304 bytes below the entry
stack top. -/
def func19Base : UInt32 := entryStackTop - 304

/-- The locals of the driver after the read phase.  Local 1 holds the
input length, local 2 the capacity, and local 3 the data pointer. -/
def afterReadLocals (length capacity ptr aux4 : UInt32) : Locals :=
  ⟨[], [.i32 func19Base, .i32 length, .i32 capacity, .i32 ptr, .i32 aux4,
    .i32 0, .i32 0, .i32 0, .i32 0], []⟩

/-- The resources of the driver after the read phase: the whole input is
in the vector, and the input stream is empty. -/
def AfterRead [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (input reserve head chunk slice tail : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8) : HeapIProp :=
  iprop(
    RuntimeContext ∗
    StackPointer func19Base ∗
    StackReserve (func19Base - 16) reserve ∗
    Slices.ByteSlice 0 func19Base head ∗
    Slices.ByteSlice 0 (func19Base + 24) chunk ∗
    Slices.ByteSlice 0 (func19Base + 280) slice ∗
    VecU8 heapId (func19Base + 288) capacity ptr input ∗
    Slices.ByteSlice 0 (func19Base + 300) tail ∗
    BumpHeap heapId storedCursor frontier history ∗
    Streams [] output false ∗
    ⌜head.length = 24 ∧ chunk.length = 256 ∧ slice.length = 8 ∧
      tail.length = 4 ∧ PushVecFacts capacity ptr frontier⌝)

/-- The control frame of the read block. -/
def phaseFrame (afterRead : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := .block 0 0 (firstReadBody lenMap) :: .const 0 :: .localSet 1 ::
      .loop 0 0 (readLoopBody lenMap) :: reloadVec lenMap,
    continuation := afterRead, belowStack := [] }

private theorem func19_initialLocals :
    Project.RustHashMap.func19Def.toLocals [] =
      ⟨[], [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
        .i32 0], []⟩ := by
  rfl

private theorem ofNat_ne_zero (n : Nat) (h : 0 < n) (hlt : n < 4294967296) :
    UInt32.ofNat n ≠ 0 := by
  have hsize : UInt32.size = 4294967296 := rfl
  intro h0
  have := congrArg UInt32.toNat h0
  rw [UInt32.toNat_ofNat_of_lt' (by rw [hsize]; omega)] at this
  simp at this; omega

/-- The read phase of the `map_len` driver: the frame setup, the reads,
and the register reload.  The caller owns the 320 bytes from the reserve
base to the entry stack top. -/
theorem twp_read_phase [WasmSmallStepGS hlc Universal.State]
    (hfunc98 : Func98Spec (hlc := hlc))
    (heapId : GName) (input output frameBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterRead : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hframe : frameBytes.length = 320) :
    iprop(
      RuntimeContext ∗
      StackPointer entryStackTop ∗
      Slices.ByteSlice 0 (func19Base - 16) frameBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output false ∗
      ((∀ capacity : UInt32, ∀ ptr : UInt32, ∀ storedCursor' : UInt32,
        ∀ frontier' : Nat, ∀ history' : AllocationHistory,
        ∀ reserve : List UInt8, ∀ head : List UInt8, ∀ chunk : List UInt8,
        ∀ slice : List UInt8, ∀ tail : List UInt8, ∀ aux4 : UInt32,
        AfterRead heapId capacity ptr input reserve head chunk slice tail
          storedCursor' frontier' history' output -∗
        WP (.running
          ⟨afterReadLocals (UInt32.ofNat input.length) capacity ptr aux4,
            afterRead, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }]) ∧
      (∀ remaining' : List UInt8,
        Streams remaining' output true -∗
          Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨Project.RustHashMap.func19Def.toLocals [],
          readPrologue ++ .block 0 0 readPhaseBody :: afterRead,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hframe, Hbump, Hstreams, Hcont⟩
  rw [func19_initialLocals]
  -- the reserve and the five frame regions
  icases (ByteSlice_split_at (func19Base - 16) 16 frameBytes
    (by simp [hframe])).mp $$ Hframe with ⟨Hreserve, Hframe⟩
  isimp only [UInt32.reduceToNat] at Hreserve
  isimp only [UInt32.reduceToNat,
    show func19Base - 16 + 16 = func19Base by decide] at Hframe
  ihave Hframe := ByteSlice_frame304 func19Base (frameBytes.drop 16)
    (by simp [hframe]) $$ Hframe
  icases Hframe with ⟨%head, %chunk, %slice, %header, %tail, %hlens,
    Hhead, Hchunk, Hslice, Hheader, Htail⟩
  isimp only [show func19Base + 24 = func19Base + lenMap.chunkOff by decide]
    at Hchunk
  isimp only [show func19Base + 288 = func19Base + lenMap.vecOff by decide]
    at Hheader
  ihave Hreserve : StackReserve (func19Base - 16) (frameBytes.take 16) $$
      [Hreserve]
  · unfold StackReserve
    isplitl_pureexact (by simp [hframe])
    iexact Hreserve
  ihave Hwords := ByteSlice_header_as_words (func19Base + lenMap.vecOff)
    header hlens.2.2.2.1 (by decide) $$ Hheader
  icases Hwords with ⟨%oldCapacity, %oldPtr, %oldLength, HoldCapacity,
    HoldPtr, HoldLength⟩
  ihave HoldPair := (pointsTo_u32_pair_as_u64 (func19Base + lenMap.vecOff)
    oldCapacity oldPtr).mp $$ [HoldCapacity HoldPtr]
  · iframe
  isimp only [UInt32.add_assoc] at HoldLength
  -- the frame setup
  isimp only [StackPointer] at Hsp
  simp only [readPrologue, List.cons_append, List.nil_append]
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
    rewriting [show entryStackTop - lenMap.frame = func19Base by decide]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer func19Base $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind twp_store32 (address := func19Base)
    (offset := lenMap.vecOff + 8) oldLength (by decide) (by decide)
    (by decide) (by decide) with HoldLength
  wasm_twp_pures [twp_localGet]
  iapply twp_pureStep _ _ _ (fun _ => Step.constI64)
  wasm_twp_bind twp_store64 (address := func19Base) (offset := lenMap.vecOff)
    (oldCapacity.toUInt64 ||| (oldPtr.toUInt64 <<< 32))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) with HoldPair => Hpair
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show lenMap.chunkOff + func19Base = func19Base + lenMap.chunkOff
    by decide]
  wasm_twp_pures [twp_const twp_const]
  isimp only [Slices.ByteSlice] at Hchunk
  icases Hchunk with ⟨%_hchunkNowrap, HchunkBytes⟩
  iapply twp_memoryFill32 chunk (by simp [hlens.2.1]) (by decide)
    (by decide) $$ HchunkBytes
  iintro HchunkBytes
  isimp only [hlens.2.1, show (0 : UInt32).toUInt8 = 0 from rfl] at HchunkBytes
  ihave Hchunk : Slices.ByteSlice 0 (func19Base + lenMap.chunkOff)
      (List.replicate 256 0) $$ [HchunkBytes]
  · unfold Slices.ByteSlice
    isplitl_pureexact (by simp only [List.length_replicate]; decide)
    iexact HchunkBytes
  ihave HpairWords : iprop(pointsTo_u32 0 (func19Base + lenMap.vecOff) 0 ∗
      pointsTo_u32 0 (func19Base + lenMap.vecOff + 4) 1) $$ [Hpair]
  · iapply (pointsTo_u32_pair_as_u64 (func19Base + lenMap.vecOff) 0 1).mpr
    rw [show (0 : UInt32).toUInt64 ||| ((1 : UInt32).toUInt64 <<< 32) =
      (4294967296 : UInt64) by decide]
    iexact Hpair
  icases HpairWords with ⟨Hcapacity, Hptr⟩
  ihave HoldLength := pointsTo_u32_address_eq
    (vec_addr lenMap func19Base 8).symm $$ HoldLength
  ihave Hvec : VecU8 heapId (func19Base + lenMap.vecOff) 0 1 [] $$
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
  -- the read block and the first read
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  unfold readPhaseBody
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  unfold firstReadBody
  iapply twp_read_chunk lenMap func19Base (List.replicate 256 0) input
    output []
    [.i32 func19Base, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
      .i32 0]
    (stack := []) (code := [.localTee 2, .br_if 0, .const 1, .localSet 3,
      .const 0, .localSet 2, .br 1]) rfl (by rw [List.length_replicate])
  isplitl_exacts [Hruntime Hstreams Hchunk]
  iintro Hruntime Hstreams Hchunk %hcount
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hempty : input = []
  · -- an empty input: leave the read block at once
    subst hempty
    isimp only [List.length_nil, Nat.min_zero, List.take_zero, List.drop_zero,
      List.nil_append] at Hchunk
    isimp only [List.length_nil, Nat.min_zero, List.drop_zero] at Hstreams
    simp only [List.length_nil, Nat.min_zero,
      show UInt32.ofNat 0 = (0 : UInt32) from rfl]
    iapply twp_brIfZero
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    iapply twp_br (depth := 1) (targetCode := afterRead)
      (targetControl := controls) (targetValues := []) (by rfl)
    isimp only [afterReadLocals] at Hcont
    ihave Hnormal := BI.and_elim_l $$ Hcont
    iapply Hnormal $$ %0 %1 %storedCursor %frontier %history
      %(frameBytes.take 16) %head %(List.replicate 256 0) %slice %tail %0
    isimp only [show func19Base + lenMap.chunkOff = func19Base + 24
      by decide] at Hchunk
    isimp only [show func19Base + lenMap.vecOff = func19Base + 288
      by decide] at Hvec
    unfold AfterRead
    isplitl_exacts [Hruntime Hsp Hreserve Hhead Hchunk Hslice Hvec Htail
      Hbump Hstreams]
    ipureexact ⟨hlens.1, by rw [List.length_replicate], hlens.2.2.1,
      hlens.2.2.2.2,
      Or.inl ⟨rfl, rfl⟩⟩
  · -- a nonempty input: run the loop
    have hpos : 0 < input.length := List.length_pos_of_ne_nil hempty
    have hcountPos : 0 < min 256 input.length := by omega
    have hcountLe : min 256 input.length ≤ input.length :=
      Nat.min_le_right _ _
    iapply twp_brIf (ofNat_ne_zero _ hcountPos (by omega)) (by rfl)
    simp only [List.take_zero, List.nil_append]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
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
    have Hloop := twp_read_loop hfunc98 lenMap func19Base heapId input output
      [.i32 0, .i32 0, .i32 0, .i32 0] (reloadVec lenMap) arity remainder
      (phaseFrame afterRead :: controls) calls s E Φ (by decide) lenMap_wf
      initial
    simp only [loopLocals, initial, htakeLen, phaseFrame, firstReadBody,
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
      unfold reloadVec
      isimp only [VecU8, RawVecHeader] at Hvec
      icases Hvec with ⟨⟨Hcapacity, Hptr⟩, Hlength, Hstorage⟩
      isimp only [UInt32.add_assoc] at Hptr
      isimp only [UInt32.add_assoc] at Hlength
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func19Base)
        (offset := lenMap.vecOff + 8)
        (UInt32.ofNat input.length) (by decide) (by decide) (by decide)
        (by decide) with Hlength
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func19Base)
        (offset := lenMap.vecOff + 4)
        finalPtr (by decide) (by decide) (by decide) (by decide) with Hptr
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func19Base)
        (offset := lenMap.vecOff)
        finalCapacity (by decide) (by decide) (by decide) (by decide)
        with Hcapacity
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
      ihave Hvec : VecU8 heapId (func19Base + lenMap.vecOff) finalCapacity
          finalPtr input $$ [Hcapacity Hptr Hlength Hstorage]
      · unfold VecU8 RawVecHeader
        isimp only [UInt32.add_assoc]
        isplitl [Hcapacity Hptr]
        · isplitl [Hcapacity]
          · iexact Hcapacity
          · iexact Hptr
        · isplitl [Hlength]
          · iexact Hlength
          · iexact Hstorage
      isimp only [afterReadLocals] at Hcont
      ihave Hnormal := BI.and_elim_l $$ Hcont
      iapply Hnormal $$ %finalCapacity %finalPtr %finalStoredCursor
        %finalFrontier %finalHistory %finalShadow %head %finalChunk %slice
        %tail %aux4
      isimp only [show func19Base + lenMap.chunkOff = func19Base + 24
        by decide] at Hchunk
      isimp only [show func19Base + lenMap.vecOff = func19Base + 288
        by decide] at Hvec
      unfold AfterRead
      isplitl_exacts [Hruntime Hsp Hreserve Hhead Hchunk Hslice Hvec Htail
        Hbump Hstreams]
      ipureexact ⟨hlens.1, hfinal.1, hlens.2.2.1, hlens.2.2.2.2, hfinal.2⟩
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      iapply Hoom $$ %remaining' Hstreams

end Project.RustHashMap.ReadAll
