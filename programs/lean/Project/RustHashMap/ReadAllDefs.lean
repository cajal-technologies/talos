import Project.RustHashMap.VecGrow
import Project.RustHashMap.ImportProofs

/-!
# The input loop of the hash map drivers: fragments and definitions

Each driver of the hash map program starts with the inlined `read_all` of the
crate: it reads the input stream in chunks of 256 bytes and pushes each byte
of a chunk into a `Vec<u8>` through the generated `grow_one`.  This file
states the loop as a family of thread states and proves it with
`twp_loop_wf_family`.  The measure is the unread stream length, counted
twice, plus the bytes of the current chunk that the loop has not pushed
yet.  The file follows the read phase of `Project.Mergesort.DriverProof`.

The core is parameterised by a `FrameMap`: the frame size, the offset of
the 256-byte chunk buffer, and the offset of the vector header.  Five
drivers run the same instruction shape with five frame maps.

The `map_len` driver is local `func19`, absolute index 22.  It uses the
instance `lenMap`.  Its frame has 304 bytes.  The chunk buffer starts at
offset 24, and the vector header starts at offset 288.  The generated
`grow_one` uses 16 bytes below the frame.
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

/-! ## The frame map -/

/-- The frame layout of one driver's read loop. -/
structure FrameMap where
  frame : UInt32
  chunkOff : UInt32
  vecOff : UInt32

/-- A frame map is well formed when the chunk buffer and the vector
header fit in the frame and do not overlap. -/
def FrameMap.WF (fm : FrameMap) : Prop :=
  fm.chunkOff.toNat + 256 ≤ fm.frame.toNat ∧
  fm.vecOff.toNat + 12 ≤ fm.frame.toNat ∧ fm.frame.toNat ≤ 368 ∧
  (fm.vecOff.toNat + 12 ≤ fm.chunkOff.toNat ∨
    fm.chunkOff.toNat + 256 ≤ fm.vecOff.toNat)

/-- The frame map of `map_len`, absolute function 22. -/
def lenMap : FrameMap := ⟨304, 24, 288⟩

/-- The frame map of `map_contains_key`, absolute function 19. -/
def containsKeyMap : FrameMap := ⟨304, 48, 36⟩

/-- The frame map of `map_get`, absolute function 21. -/
def getMap : FrameMap := ⟨320, 64, 52⟩

/-- The frame map of `map_remove`, absolute function 9. -/
def removeMap : FrameMap := ⟨320, 64, 52⟩

/-- The frame map of `map_insert`, absolute function 3. -/
def insertMap : FrameMap := ⟨368, 56, 24⟩

theorem lenMap_wf : lenMap.WF := by
  unfold FrameMap.WF lenMap; decide

theorem containsKeyMap_wf : containsKeyMap.WF := by
  unfold FrameMap.WF containsKeyMap; decide

theorem getMap_wf : getMap.WF := by
  unfold FrameMap.WF getMap; decide

theorem removeMap_wf : removeMap.WF := by
  unfold FrameMap.WF removeMap; decide

theorem insertMap_wf : insertMap.WF := by
  unfold FrameMap.WF insertMap; decide

/-! ## Frame addresses -/

/-- An offset inside the frame does not wrap. -/
theorem addr_toNat (base off : UInt32)
    (h : base.toNat + off.toNat < UInt32.size) :
    (base + off).toNat = base.toNat + off.toNat := by
  simpa only [UInt32.ofNat_toNat] using
    Slices.byteOffset_toNat base off.toNat h

/-- The four address facts of one 32-bit cell of the frame. -/
theorem cell_facts (base off : UInt32)
    (h : base.toNat + off.toNat + 4 < UInt32.size) :
    (base + off).toNat = base.toNat + off.toNat ∧
      (base + off + 1).toNat = (base + off).toNat + 1 ∧
      (base + off + 2).toNat = (base + off).toNat + 2 ∧
      (base + off + 3).toNat = (base + off).toNat + 3 := by
  have hsize : UInt32.size = 4294967296 := rfl
  have h0 : (base + off).toNat = base.toNat + off.toNat :=
    addr_toNat base off (by omega)
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using Slices.byteOffset_toNat (base + off) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + off) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + off) 3 (by omega)

/-- Split the address of one vector word. -/
theorem vec_addr (fm : FrameMap) (base k : UInt32) :
    base + fm.vecOff + k = base + (fm.vecOff + k) :=
  UInt32.add_assoc base fm.vecOff k

/-- The two vector words above the header do not wrap. -/
theorem vec_facts (fm : FrameMap) (hwf : fm.WF) :
    (fm.vecOff + 4).toNat = fm.vecOff.toNat + 4 ∧
      (fm.vecOff + 8).toNat = fm.vecOff.toNat + 8 := by
  have hsize : UInt32.size = 4294967296 := rfl
  unfold FrameMap.WF at hwf
  obtain ⟨_, hvec, hframe, _⟩ := hwf
  constructor
  · simpa using Slices.byteOffset_toNat fm.vecOff 4 (by omega)
  · simpa using Slices.byteOffset_toNat fm.vecOff 8 (by omega)

/-! ## The generated program fragments -/

/-- The frame setup of the read phase. -/
def readPrologue (fm : FrameMap := lenMap) : Program :=
  [.globalGet 0, .const fm.frame, .sub, .localTee 0, .globalSet 0, .const 0,
    .localSet 1, .localGet 0, .const 0, .store32 (fm.vecOff + 8),
    .localGet 0, .constI64 4294967296, .store64 fm.vecOff, .localGet 0,
    .const fm.chunkOff, .add, .const 0, .const 256, .memoryFill]

/-- The first read.  An empty stream leaves the empty vector. -/
def firstReadBody (fm : FrameMap) : Program :=
  [.localGet 0, .const fm.chunkOff, .add, .const 256, .call 63, .localTee 2,
    .br_if 0, .const 1, .localSet 3, .const 0, .localSet 2, .br 1]

/-- The capacity guard of one push, with the call of `grow_one`. -/
def growBody (fm : FrameMap) : Program :=
  [.localGet 0, .load32 (fm.vecOff + 8), .localTee 3, .localGet 0,
    .load32 fm.vecOff, .ne, .br_if 0, .localGet 0, .const fm.vecOff, .add,
    .call 101]

/-- The store of one byte after the capacity guard. -/
def storeTail (fm : FrameMap) : Program :=
  [.localGet 1, .const 1, .add, .localSet 1, .localGet 0,
    .load32 (fm.vecOff + 4), .localGet 3, .add, .localGet 4, .store8 0,
    .localGet 0, .localGet 3, .const 1, .add, .store32 (fm.vecOff + 8)]

/-- One push of the current chunk byte, then the branch back to the loop
head while chunk bytes remain. -/
def pushBody (fm : FrameMap) : Program :=
  [.localGet 1, .const 256, .eq, .br_if 0, .localGet 0, .const fm.chunkOff,
    .add, .localGet 1, .add, .load8U 0, .localSet 4,
    .block 0 0 (growBody fm)] ++
  storeTail fm ++
  [.localGet 2, .const 4294967295, .add, .localTee 2, .br_if 1]

/-- The next read after a chunk is pushed. -/
def nextRead (fm : FrameMap) : Program :=
  [.const 0, .localSet 1, .localGet 0, .const fm.chunkOff, .add, .const 256,
    .call 63, .localTee 2, .br_if 0]

/-- The body of the read loop. -/
def readLoopBody (fm : FrameMap) : Program :=
  .block 0 0 (pushBody fm) :: nextRead fm

/-- The reload of the vector fields after the loop. -/
def reloadVec (fm : FrameMap) : Program :=
  [.localGet 0, .load32 (fm.vecOff + 8), .localSet 1, .localGet 0,
    .load32 (fm.vecOff + 4), .localSet 3, .localGet 0, .load32 fm.vecOff,
    .localSet 2]

/-- The whole read phase inside the outer block. -/
def readPhaseBody (fm : FrameMap := lenMap) : Program :=
  .block 0 0 (firstReadBody fm) :: .const 0 :: .localSet 1 ::
    .loop 0 0 (readLoopBody fm) :: reloadVec fm

/-- The code of the `map_len` driver after the read phase. -/
def func19AfterRead : Program := Project.RustHashMap.func19.drop 20

theorem func19_shape :
    Project.RustHashMap.func19 =
      readPrologue lenMap ++
        .block 0 0 (readPhaseBody lenMap) :: func19AfterRead := by
  rfl

/-! ## Byte ownership helpers -/

/-- Cut a slice at a word offset. -/
theorem ByteSlice_split_at [WasmHeapGS Universal.State]
    (ptr k : UInt32) (bytes : List UInt8) (hk : k.toNat ≤ bytes.length) :
    Slices.ByteSlice 0 ptr bytes ⊣⊢
      iprop(Slices.ByteSlice 0 ptr (bytes.take k.toNat) ∗
        Slices.ByteSlice 0 (ptr + k) (bytes.drop k.toNat)) := by
  have h := Slices.ByteSlice_append (α := Universal.State) 0 ptr
    (bytes.take k.toNat) (bytes.drop k.toNat)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hk,
    UInt32.ofNat_toNat] at h
  exact h

/-- Twelve raw bytes as three words. -/
theorem ByteSlice_header_as_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (hlen : bytes.length = 12)
    (hnowrap : ptr.toNat + 12 < UInt32.size) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop(∃ a b c : UInt32,
        pointsTo_u32 0 ptr a ∗ pointsTo_u32 0 (ptr + 4) b ∗
          pointsTo_u32 0 (ptr + 8) c) := by
  iintro Hbytes
  have hb4 : (ptr + 4).toNat = ptr.toNat + 4 := by
    simpa using Slices.byteOffset_toNat ptr 4 (by omega)
  have hb8 : (ptr + 8).toNat = ptr.toNat + 8 := by
    simpa using Slices.byteOffset_toNat ptr 8 (by omega)
  icases (ByteSlice_split_at ptr 4 bytes (by simp [hlen])).mp $$ Hbytes
    with ⟨H0, Hrest⟩
  isimp only [UInt32.reduceToNat] at H0
  isimp only [UInt32.reduceToNat] at Hrest
  icases (ByteSlice_split_at (ptr + 4) 4 (bytes.drop 4) (by simp [hlen])).mp
    $$ Hrest with ⟨H1, H2⟩
  isimp only [UInt32.reduceToNat] at H1
  isimp only [UInt32.reduceToNat, UInt32.add_assoc, UInt32.reduceAdd] at H2
  ihave H0 := (Slices.ByteSlice_four_as_word 0 ptr (bytes.take 4)
    (by simp [hlen]) (by omega)).mp $$ H0
  ihave H1 := (Slices.ByteSlice_four_as_word 0 (ptr + 4)
    ((bytes.drop 4).take 4) (by simp [hlen]) (by omega)).mp $$ H1
  ihave H2 := (Slices.ByteSlice_four_as_word 0 (ptr + 8)
    ((bytes.drop 4).drop 4) (by simp [hlen]) (by omega)).mp $$ H2
  iexists (WordCodec.decodeU32 (bytes.take 4)),
    (WordCodec.decodeU32 ((bytes.drop 4).take 4)),
    (WordCodec.decodeU32 ((bytes.drop 4).drop 4))
  iframe

/-- Focus on one byte of a slice, given as an explicit split. -/
private theorem ByteSlice_byteFocus_split [WasmHeapGS Universal.State]
    (ptr : UInt32) (left : List UInt8) (byte : UInt8) (right : List UInt8)
    (index : Nat) (hleft : left.length = index) :
    Slices.ByteSlice 0 ptr (left ++ byte :: right) ⊢
      iprop((⟨0, ptr + UInt32.ofNat index⟩ ↦w byte) ∗
        ((⟨0, ptr + UInt32.ofNat index⟩ ↦w byte) -∗
          Slices.ByteSlice 0 ptr (left ++ byte :: right))) := by
  iintro Hbytes
  icases (Slices.ByteSlice_append 0 ptr left (byte :: right)).mp $$ Hbytes
    with ⟨Hleft, Hright⟩
  isimp only [hleft] at Hright
  isimp only [Slices.ByteSlice] at Hright
  icases Hright with ⟨%hnowrap, Hright⟩
  isimp only [pointsToBytes] at Hright
  icases Hright with ⟨Hbyte, Hrest⟩
  isplitl [Hbyte]
  · iexact Hbyte
  · iintro Hbyte
    iapply (Slices.ByteSlice_append 0 ptr left (byte :: right)).mpr
    rw [hleft]
    isplitl [Hleft]
    · iexact Hleft
    · unfold Slices.ByteSlice
      isplitl_pureexact hnowrap
      isimp only [pointsToBytes]
      isplitl [Hbyte]
      · iexact Hbyte
      · iexact Hrest

/-- Focus on one byte of a slice for a read.  The wand takes the same byte
back. -/
theorem ByteSlice_byteFocus [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (index : Nat)
    (hindex : index < bytes.length) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop((⟨0, ptr + UInt32.ofNat index⟩ ↦w bytes[index]) ∗
        ((⟨0, ptr + UInt32.ofNat index⟩ ↦w bytes[index]) -∗
          Slices.ByteSlice 0 ptr bytes)) := by
  have hsplit : bytes =
      bytes.take index ++ bytes[index] :: bytes.drop (index + 1) := by
    have := List.take_append_drop index bytes
    rw [List.drop_eq_getElem_cons hindex] at this
    exact this.symm
  have htake : (bytes.take index).length = index := by
    simp [List.length_take, Nat.min_eq_left hindex.le]
  have key := ByteSlice_byteFocus_split ptr (bytes.take index) bytes[index]
    (bytes.drop (index + 1)) index htake
  rw [← hsplit] at key
  exact key

/-- The initialized bytes of a vector fit in its capacity. -/
theorem VecStorage_length_le [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32) (initialized : List UInt8) :
    VecStorage heapId capacity ptr initialized ⊢
      iprop(VecStorage heapId capacity ptr initialized ∗
        ⌜initialized.length ≤ capacity.toNat⌝) := by
  iintro Hstorage
  unfold VecStorage
  icases Hstorage with ⟨%hempty | ⟨%allocationId, %allBytes, %spare, %hfacts,
    Hblock⟩⟩
  · isplitl []
    · ileft
      ipureexact hempty
    · ipureintro
      rw [hempty.2.2]
      exact Nat.zero_le _
  · isplitl [Hblock]
    · iright
      iexists allocationId
      iexists allBytes
      iexists spare
      isplitl_pureexact hfacts
      iexact Hblock
    · ipureexact hfacts.2.1

/-- Two adjacent 32-bit cells are one 64-bit cell.  A copy of the private
lemma of `Project.Mergesort.DriverProof`. -/
theorem pointsTo_u32_pair_as_u64 [WasmHeapGS Universal.State]
    (ptr lo hi : UInt32) :
    iprop(pointsTo_u32 0 ptr lo ∗ pointsTo_u32 0 (ptr + 4) hi) ⊣⊢
      pointsTo_u64 0 ptr (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) := by
  let combined : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
  have h0 : u64Byte combined 0 = u32Byte lo 0 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte0 lo hi
  have h1 : u64Byte combined 1 = u32Byte lo 1 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte1 lo hi
  have h2 : u64Byte combined 2 = u32Byte lo 2 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte2 lo hi
  have h3 : u64Byte combined 3 = u32Byte lo 3 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte3 lo hi
  have h4 : u64Byte combined 4 = u32Byte hi 0 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte4 lo hi
  have h5 : u64Byte combined 5 = u32Byte hi 1 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte5 lo hi
  have h6 : u64Byte combined 6 = u32Byte hi 2 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte6 lo hi
  have h7 : u64Byte combined 7 = u32Byte hi 3 := by
    simpa [combined, u64Byte, u32Byte] using UInt64.pack32_byte7 lo hi
  change iprop(pointsTo_u32 0 ptr lo ∗ pointsTo_u32 0 (ptr + 4) hi) ⊣⊢
    pointsTo_u64 0 ptr combined
  unfold pointsTo_u32 pointsTo_u64
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [show ptr + 4 + 1 = ptr + 5 by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]]
  rw [show ptr + 4 + 2 = ptr + 6 by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]]
  rw [show ptr + 4 + 3 = ptr + 7 by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]]
  constructor
  · iintro ⟨Hlo, Hhi⟩
    icases Hlo with ⟨H0, H1, H2, H3⟩
    icases Hhi with ⟨H4, H5, H6, H7⟩; iframe
  · iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩; iframe

/-! ## The loop family -/

/-- The state of the read loop at its head.  `chunk` is the last chunk the
stream gave, `index` counts its pushed bytes, and `chunkTail` is the stale
rest of the 256-byte buffer. -/
structure LoopState where
  pushed : List UInt8
  chunk : List UInt8
  index : Nat
  chunkTail : List UInt8
  remaining : List UInt8
  capacity : UInt32
  ptr : UInt32
  shadow : List UInt8
  storedCursor : UInt32
  frontier : Nat
  history : AllocationHistory
  aux3 : UInt32
  aux4 : UInt32

/-- The locals at the loop head.  Local 1 is the chunk index, local 2 the
count of chunk bytes still to push. -/
def loopLocals (base aux5 aux6 aux7 aux8 : UInt32) (st : LoopState) :
    Locals :=
  ⟨[], [.i32 base, .i32 (UInt32.ofNat st.index),
    .i32 (UInt32.ofNat (st.chunk.length - st.index)), .i32 st.aux3,
    .i32 st.aux4, .i32 aux5, .i32 aux6, .i32 aux7, .i32 aux8], []⟩

/-- The locals after the loop: the index and the count are zero. -/
def afterLoopLocals (base aux3 aux4 aux5 aux6 aux7 aux8 : UInt32) :
    Locals :=
  ⟨[], [.i32 base, .i32 0, .i32 0, .i32 aux3, .i32 aux4, .i32 aux5,
    .i32 aux6, .i32 aux7, .i32 aux8], []⟩

/-- The loop measure: each push and each read makes it smaller. -/
def loopMeasure (st : LoopState) : Nat :=
  2 * st.remaining.length + (st.chunk.length - st.index)

/-- The continuation of the read loop.  The normal arm runs the code after
the loop with the whole input in the vector.  The OOM arm is the trap. -/
def LoopContinuation [WasmSmallStepGS hlc Universal.State]
    (fm : FrameMap) (base : UInt32)
    (heapId : GName) (input output : List UInt8)
    (aux5 aux6 aux7 aux8 : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
    ∀ finalStoredCursor : UInt32, ∀ finalFrontier : Nat,
    ∀ finalHistory : AllocationHistory,
    ∀ finalShadow : List UInt8, ∀ finalChunk : List UInt8,
    ∀ aux3 : UInt32, ∀ aux4 : UInt32,
      RuntimeContext -∗
      StackPointer base -∗
      StackReserve (base - 16) finalShadow -∗
      Slices.ByteSlice 0 (base + fm.chunkOff) finalChunk -∗
      VecU8 heapId (base + fm.vecOff) finalCapacity finalPtr input -∗
      BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
      Streams [] output false -∗
      ⌜finalChunk.length = 256 ∧
        PushVecFacts finalCapacity finalPtr finalFrontier⌝ -∗
      WP (.running
        ⟨afterLoopLocals base aux3 aux4 aux5 aux6 aux7 aux8, afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) ∧
  (∀ remaining' : List UInt8,
    Streams remaining' output true -∗
      Φ (.trapped (.host OOM.trapMessage))))

/-- The loop invariant at the loop head. -/
def LoopInv [WasmSmallStepGS hlc Universal.State]
    (fm : FrameMap) (base : UInt32)
    (heapId : GName) (input output : List UInt8)
    (aux5 aux6 aux7 aux8 : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (st : LoopState) : HeapIProp := iprop(
  RuntimeContext ∗
  StackPointer base ∗
  StackReserve (base - 16) st.shadow ∗
  Slices.ByteSlice 0 (base + fm.chunkOff) (st.chunk ++ st.chunkTail) ∗
  VecU8 heapId (base + fm.vecOff) st.capacity st.ptr
    (st.pushed ++ st.chunk.take st.index) ∗
  BumpHeap heapId st.storedCursor st.frontier st.history ∗
  Streams st.remaining output false ∗
  ⌜input = st.pushed ++ st.chunk ++ st.remaining ∧
    st.index < st.chunk.length ∧
    st.chunk.length + st.chunkTail.length = 256 ∧
    PushVecFacts st.capacity st.ptr st.frontier⌝ ∗
  LoopContinuation fm base heapId input output aux5 aux6 aux7 aux8 afterLoop
    arity remainder controls calls s E Φ)

/-! ## One chunk read -/

/-- One read of up to 256 bytes into the chunk buffer through the proved
read contract. -/
theorem twp_read_chunk [WasmSmallStepGS hlc Universal.State]
    (fm : FrameMap) (base : UInt32) (buffer input output : List UInt8)
    (params localValues : List Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hlocal0 : (⟨params, localValues, stack⟩ : Locals).get 0 =
      some (.i32 base))
    (hbuffer : buffer.length = 256) :
    iprop(
      RuntimeContext ∗
      Streams input output false ∗
      Slices.ByteSlice 0 (base + fm.chunkOff) buffer ∗
      (RuntimeContext -∗
        Streams (input.drop (min 256 input.length)) output false -∗
        Slices.ByteSlice 0 (base + fm.chunkOff)
          (input.take (min 256 input.length) ++
            buffer.drop (min 256 input.length)) -∗
        ⌜min 256 input.length ≤ 256⌝ -∗
        WP (.running
          ⟨⟨params, localValues,
              .i32 (UInt32.ofNat (min 256 input.length)) :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨params, localValues, stack⟩,
          .localGet 0 :: .const fm.chunkOff :: .add :: .const 256 ::
            .call 63 :: code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hstreams, Hchunk, Hcont⟩
  iapply twp_localGet hlocal0
  wasm_twp_pures [twp_const twp_add]
    rewriting [UInt32.add_comm fm.chunkOff base]
  wasm_twp_pures [twp_const]
  have Hread := Project.RustHashMap.ImportProofs.func60_correct (hlc := hlc)
  unfold Func60Spec readContractAt CallContract callExpr at Hread
  have Hread' := Hread (base + fm.chunkOff) 256 buffer input output false
    (callerLocals := ⟨params, localValues, stack⟩) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  dsimp only at Hread'
  simp only [UInt32.reduceToNat, List.cons_append, List.nil_append] at Hread'
  iapply Hread'
  isplitl_exacts [Hruntime Hstreams Hchunk]
  isplitl_pureexact ⟨hbuffer.symm, by decide⟩
  iintro Hruntime Hstreams Hchunk %hcount
  unfold ResumeWP resumeExpr
  simp only [List.cons_append, List.nil_append]
  iapply_pure Hcont $$ Hruntime Hstreams Hchunk => exact hcount

/-- Move a word to an equal address. -/
theorem pointsTo_u32_address_eq
    [WasmSmallStepGS hlc Universal.State]
    {address address' value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 0 address value ⊢ pointsTo_u32 0 address' value := by
  rw [haddress]

/-- Move a vector to an equal list of initialized bytes. -/
theorem VecU8_initialized_eq [WasmHeapGS Universal.State]
    {heapId : GName} {header capacity ptr : UInt32}
    {bytes bytes' : List UInt8} (h : bytes = bytes') :
    VecU8 heapId header capacity ptr bytes ⊢
      VecU8 heapId header capacity ptr bytes' := by
  rw [h]

end Project.RustHashMap.ReadAll
