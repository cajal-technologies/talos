import Project.RustHashMap.ReadAllLoop

/-!
# The read loop of the `map_insert` driver

The `map_insert` driver is local `func0`, absolute function 3.  WAT lines
66 to 122 hold its read loop.  The loop runs the same opcodes as the core
read loop of `Project.RustHashMap.ReadAll`, but the compiler gave the two
scratch registers the other order:

- In the core, local 3 holds the vector length and local 4 holds the
  chunk byte.
- In this driver, local 3 holds the chunk byte and local 4 holds the
  vector length.

The core hard-codes the two indices in its fragments and in its locals
lists, so this file copies the loop parts of the core and swaps them.
The four core files stay unchanged.  Every name below is the core name,
so the phase file of this driver can follow `GetRead.lean` line by line.

The copy also fixes the frame map to `insertMap`, the frame map of
absolute function 3.  The parameters `fm` and `hwf` of the core are
therefore gone.  A comparison of WAT 66 to 122 against WAT 5095 to 5150,
the same loop in absolute function 21, shows that the two loops agree
instruction by instruction after two renamings: the offset map 64 to 56,
52 to 24, 56 to 28 and 60 to 32, and the local swap of 3 and 4.

## Where each part comes from

- `growBody`, `storeTail`, `pushBody`, `nextRead` and `readLoopBody`:
  `ReadAllDefs.lean` lines 137 to 165.
- `LoopState`, `loopLocals`, `afterLoopLocals`, `loopMeasure`,
  `LoopContinuation` and `LoopInv`: `ReadAllDefs.lean` lines 348 to 444.
- `twp_read_chunk`: `ReadAllDefs.lean` lines 446 to 500.
- `twp_store_tail`, `PushContinuation` and `twp_push_byte`:
  `ReadAllPush.lean` lines 26 to 307.
- `ofNat_succ_wrap`, `ofNat_ne_256`, `ofNat_ne_zero`,
  `twp_loop_iteration` and `twp_read_loop`: `ReadAllLoop.lean` lines 25
  to 295.

## The swapped positions

Each item gives the core line and the change:

- `ReadAllDefs.lean` 139: `.localTee 3` writes the length.  It becomes
  `.localTee 4`.
- `ReadAllDefs.lean` 146: `.localGet 3` reads the length and becomes
  `.localGet 4`; `.localGet 4` reads the byte and becomes `.localGet 3`.
- `ReadAllDefs.lean` 147: `.localGet 3` reads the length.  It becomes
  `.localGet 4`.
- `ReadAllDefs.lean` 153: `.localSet 4` writes the byte.  It becomes
  `.localSet 3`.
- `ReadAllPush.lean` 45 and 46, 51 and 52, 151 and 152, 186 and 187,
  242 and 243: slot 3 and slot 4 of a locals list change places.  The
  binder `aux3` of `twp_push_byte` becomes `aux4`, because the stale
  register of that step is now local 4.
- `ReadAllLoop.lean` 107: `twp_push_byte` gets `st.aux4`, not `st.aux3`.
- `ReadAllLoop.lean` 149 and 150, 176 and 177, 201 and 202, 240 and 241:
  the length and the byte change places.

## The positions that keep their digits

The digits 3 and 4 also appear where they are not local indices.  These
positions do not change:

- `insertMap.vecOff + 4` and `insertMap.vecOff + 8` are frame offsets,
  and so are the arguments of `cell_facts` and `vec_facts`.
- The `0` of `.store8 0` and `.load8U 0` is a memory offset.
- `4294967295`, `4294967296` and `UInt32.size` are constants.
- `LoopState.aux3` is the value of local 3 and `LoopState.aux4` the value
  of local 4.  Both are free at the loop head, so `loopLocals` and
  `afterLoopLocals` keep the shape of the core.  What changes is which of
  the two the loop proof fills with the byte and which with the length.
- `firstReadBody` at `ReadAllDefs.lean` 135 and `reloadVec` at
  `ReadAllDefs.lean` 170 are not loop parts.  The driver reads the first
  chunk without a block and reloads other registers, so the phase file
  states them, not this file.

Every helper of `ReadAllDefs.lean` that does not name a local is reused
and not copied.
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
  cell_facts vec_addr vec_facts ByteSlice_byteFocus VecStorage_length_le
  pointsTo_u32_address_eq VecU8_initialized_eq)
open scoped Wasm.SmallStep.Outcome

/-! ## The generated program fragments -/

/-- The capacity guard of one push, with the call of `grow_one`. -/
def growBody : Program :=
  [.localGet 0, .load32 (insertMap.vecOff + 8), .localTee 4, .localGet 0,
    .load32 insertMap.vecOff, .ne, .br_if 0, .localGet 0,
    .const insertMap.vecOff, .add, .call 101]

/-- The store of one byte after the capacity guard. -/
def storeTail : Program :=
  [.localGet 1, .const 1, .add, .localSet 1, .localGet 0,
    .load32 (insertMap.vecOff + 4), .localGet 4, .add, .localGet 3, .store8 0,
    .localGet 0, .localGet 4, .const 1, .add, .store32 (insertMap.vecOff + 8)]

/-- One push of the current chunk byte, then the branch back to the loop
head while chunk bytes remain. -/
def pushBody : Program :=
  [.localGet 1, .const 256, .eq, .br_if 0, .localGet 0,
    .const insertMap.chunkOff, .add, .localGet 1, .add, .load8U 0,
    .localSet 3,
    .block 0 0 growBody] ++
  storeTail ++
  [.localGet 2, .const 4294967295, .add, .localTee 2, .br_if 1]

/-- The next read after a chunk is pushed. -/
def nextRead : Program :=
  [.const 0, .localSet 1, .localGet 0, .const insertMap.chunkOff, .add,
    .const 256, .call 63, .localTee 2, .br_if 0]

/-- The body of the read loop. -/
def readLoopBody : Program :=
  .block 0 0 pushBody :: nextRead

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
count of chunk bytes still to push.  The read loop uses locals 0 to 4 only.
`auxTail` holds the locals above them, which the driver declares but the
read phase does not touch.  Each driver gives its own tail. -/
def loopLocals (base : UInt32) (auxTail : List Value) (st : LoopState) :
    Locals :=
  ⟨[], .i32 base :: .i32 (UInt32.ofNat st.index) ::
    .i32 (UInt32.ofNat (st.chunk.length - st.index)) :: .i32 st.aux3 ::
    .i32 st.aux4 :: auxTail, []⟩

/-- The locals after the loop: the index and the count are zero.  The tail
is the same one that `loopLocals` carries. -/
def afterLoopLocals (base aux3 aux4 : UInt32) (auxTail : List Value) :
    Locals :=
  ⟨[], .i32 base :: .i32 0 :: .i32 0 :: .i32 aux3 :: .i32 aux4 :: auxTail,
    []⟩

/-- The loop measure: each push and each read makes it smaller. -/
def loopMeasure (st : LoopState) : Nat :=
  2 * st.remaining.length + (st.chunk.length - st.index)

/-- The continuation of the read loop.  The normal arm runs the code after
the loop with the whole input in the vector.  The OOM arm is the trap. -/
def LoopContinuation [WasmSmallStepGS hlc Universal.State]
    (base : UInt32)
    (heapId : GName) (input output : List UInt8)
    (auxTail : List Value)
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
      Slices.ByteSlice 0 (base + insertMap.chunkOff) finalChunk -∗
      VecU8 heapId (base + insertMap.vecOff) finalCapacity finalPtr input -∗
      BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
      Streams [] output false -∗
      ⌜finalChunk.length = 256 ∧
        PushVecFacts finalCapacity finalPtr finalFrontier⌝ -∗
      WP (.running
        ⟨afterLoopLocals base aux3 aux4 auxTail, afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) ∧
  (∀ remaining' : List UInt8,
    Streams remaining' output true -∗
      Φ (.trapped (.host OOM.trapMessage))))

/-- The loop invariant at the loop head. -/
def LoopInv [WasmSmallStepGS hlc Universal.State]
    (base : UInt32)
    (heapId : GName) (input output : List UInt8)
    (auxTail : List Value)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (st : LoopState) : HeapIProp := iprop(
  RuntimeContext ∗
  StackPointer base ∗
  StackReserve (base - 16) st.shadow ∗
  Slices.ByteSlice 0 (base + insertMap.chunkOff) (st.chunk ++ st.chunkTail) ∗
  VecU8 heapId (base + insertMap.vecOff) st.capacity st.ptr
    (st.pushed ++ st.chunk.take st.index) ∗
  BumpHeap heapId st.storedCursor st.frontier st.history ∗
  Streams st.remaining output false ∗
  ⌜input = st.pushed ++ st.chunk ++ st.remaining ∧
    st.index < st.chunk.length ∧
    st.chunk.length + st.chunkTail.length = 256 ∧
    PushVecFacts st.capacity st.ptr st.frontier⌝ ∗
  LoopContinuation base heapId input output auxTail afterLoop
    arity remainder controls calls s E Φ)

/-! ## One chunk read -/

/-- One read of up to 256 bytes into the chunk buffer through the proved
read contract. -/
theorem twp_read_chunk [WasmSmallStepGS hlc Universal.State]
    (base : UInt32) (buffer input output : List UInt8)
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
      Slices.ByteSlice 0 (base + insertMap.chunkOff) buffer ∗
      (RuntimeContext -∗
        Streams (input.drop (min 256 input.length)) output false -∗
        Slices.ByteSlice 0 (base + insertMap.chunkOff)
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
          .localGet 0 :: .const insertMap.chunkOff :: .add :: .const 256 ::
            .call 63 :: code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hstreams, Hchunk, Hcont⟩
  iapply twp_localGet hlocal0
  wasm_twp_pures [twp_const twp_add]
    rewriting [UInt32.add_comm insertMap.chunkOff base]
  wasm_twp_pures [twp_const]
  have Hread := Project.RustHashMap.ImportProofs.func60_correct (hlc := hlc)
  unfold Func60Spec readContractAt CallContract callExpr at Hread
  have Hread' := Hread (base + insertMap.chunkOff) 256 buffer input output
    false
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

/-! ## One push -/

/-- The store of one byte into a vector with room, then the length update.
Local 3 holds the length and local 4 the byte. -/
theorem twp_store_tail [WasmSmallStepGS hlc Universal.State]
    (base index count : UInt32) (byte : UInt8)
    (auxTail : List Value)
    (heapId : GName) (capacity ptr : UInt32) (initialized : List UInt8)
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hbase : base.toNat + insertMap.frame.toNat < UInt32.size)
    (hroom : initialized.length < capacity.toNat) :
    iprop(
      VecU8 heapId (base + insertMap.vecOff) capacity ptr initialized ∗
      (VecU8 heapId (base + insertMap.vecOff) capacity ptr
        (initialized ++ [byte]) -∗
        WP (.running
          ⟨⟨[], .i32 base :: .i32 (index + 1) :: .i32 count ::
              .i32 byte.toUInt32 ::
              .i32 (UInt32.ofNat initialized.length) :: auxTail, []⟩,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨[], .i32 base :: .i32 index :: .i32 count ::
            .i32 byte.toUInt32 ::
            .i32 (UInt32.ofNat initialized.length) :: auxTail, []⟩,
          storeTail ++ code, arity, remainder, controls, calls⟩ :
            Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hvec, Hcont⟩
  have hsize : UInt32.size = 4294967296 := rfl
  have hbounds := insertMap_wf
  unfold FrameMap.WF at hbounds
  obtain ⟨_, hvecFits, hframeLe, _⟩ := hbounds
  obtain ⟨hq4, hq8⟩ := vec_facts insertMap insertMap_wf
  have h292 : base + insertMap.vecOff + 4 = base + (insertMap.vecOff + 4) :=
    vec_addr insertMap base 4
  have h296 : base + insertMap.vecOff + 8 = base + (insertMap.vecOff + 8) :=
    vec_addr insertMap base 8
  obtain ⟨hb292, hb292_1, hb292_2, hb292_3⟩ :=
    cell_facts base (insertMap.vecOff + 4) (by omega)
  obtain ⟨hb296, hb296_1, hb296_2, hb296_3⟩ :=
    cell_facts base (insertMap.vecOff + 8) (by omega)
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapacity, Hptr⟩, Hlength, Hstorage⟩
  ihave Hptr := pointsTo_u32_address_eq h292 $$ Hptr
  ihave Hlength := pointsTo_u32_address_eq h296 $$ Hlength
  unfold storeTail
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm 1 index]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := base)
    (offset := insertMap.vecOff + 4) ptr
    hb292 hb292_1 hb292_2 hb292_3 with Hptr
  wasm_twp_pures [twp_localGet twp_add]
    rewriting [UInt32.add_comm (UInt32.ofNat initialized.length) ptr]
  wasm_twp_pures [twp_localGet]
  ihave Hfocus := VecStorage_appendFocus heapId capacity ptr initialized
    [byte] (by simp) (by simp only [List.length_singleton]; omega) $$
    Hstorage
  icases Hfocus with ⟨%oldChunk, %holdLength, Hold, Hclose⟩
  have holdLength' : oldChunk.length = 1 := by simpa using holdLength
  obtain ⟨old, hold⟩ := List.length_eq_one_iff.mp holdLength'
  subst hold
  isimp only [Slices.ByteSlice] at Hold
  icases Hold with ⟨%hnowrap, Hold⟩
  isimp only [pointsToBytes] at Hold
  icases Hold with ⟨Hold, _⟩
  wasm_twp_rebind twp_store8_addr_gen old with Hold
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm 1 (UInt32.ofNat initialized.length)]
  wasm_twp_rebind twp_store32 (address := base)
    (offset := insertMap.vecOff + 8)
    (UInt32.ofNat initialized.length) hb296 hb296_1
    hb296_2 hb296_3 with Hlength
  ihave Hstorage : VecStorage heapId capacity ptr (initialized ++ [byte]) $$
      [Hold Hclose]
  · iapply Hclose
    unfold Slices.ByteSlice
    isplitl_pureexact hnowrap
    isimp only [pointsToBytes]
    isplitl [Hold]
    · simp only [UInt8.toUInt8_toUInt32]
      iexact Hold
    · itrivial
  ihave Hvec : VecU8 heapId (base + insertMap.vecOff) capacity ptr
      (initialized ++ [byte]) $$
      [Hcapacity Hptr Hlength Hstorage]
  · unfold VecU8 RawVecHeader
    isplitl [Hcapacity Hptr]
    · isplitl [Hcapacity]
      · iexact Hcapacity
      · iapply pointsTo_u32_address_eq h292.symm $$ Hptr
    · isplitl [Hlength]
      · ihave Hlength := pointsTo_u32_address_eq h296.symm $$ Hlength
        rw [List.length_append, List.length_singleton, UInt32.ofNat_add,
          show UInt32.ofNat 1 = (1 : UInt32) from rfl]
        iexact Hlength
      · iexact Hstorage
  iapply Hcont $$ Hvec

/-- The continuation of one push: the normal arm runs `code` with the
byte appended and with local 1 stepped, the OOM arm is the trap. -/
def PushContinuation [WasmSmallStepGS hlc Universal.State]
    (base index count : UInt32) (byte : UInt8)
    (auxTail : List Value)
    (heapId : GName) (initialized remaining output : List UInt8)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ capacity' : UInt32, ∀ ptr' : UInt32, ∀ storedCursor' : UInt32,
    ∀ frontier' : Nat, ∀ history' : AllocationHistory,
    ∀ shadow' : List UInt8,
      RuntimeContext -∗
      StackPointer base -∗
      StackReserve (base - 16) shadow' -∗
      VecU8 heapId (base + insertMap.vecOff) capacity' ptr'
        (initialized ++ [byte]) -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams remaining output false -∗
      ⌜PushVecFacts capacity' ptr' frontier'⌝ -∗
      WP (.running
        ⟨⟨[], .i32 base :: .i32 (index + 1) :: .i32 count ::
            .i32 byte.toUInt32 ::
            .i32 (UInt32.ofNat initialized.length) :: auxTail, []⟩,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) ∧
  (∀ remaining' : List UInt8,
    Streams remaining' output true -∗
      Φ (.trapped (.host OOM.trapMessage))))

/-- One push: the capacity guard, the possible `grow_one`, and the store.
Local 4 holds the byte. -/
theorem twp_push_byte [WasmSmallStepGS hlc Universal.State]
    (hfunc98 : Func98Spec (hlc := hlc))
    (base index count : UInt32) (byte : UInt8)
    (aux4 : UInt32) (auxTail : List Value)
    (heapId : GName) (capacity ptr : UInt32)
    (initialized shadow remaining output : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hbase : 16 ≤ base.toNat ∧
      base.toNat + insertMap.frame.toNat < UInt32.size)
    (hpush : PushVecFacts capacity ptr frontier) :
    iprop(
      RuntimeContext ∗
      StackPointer base ∗
      StackReserve (base - 16) shadow ∗
      VecU8 heapId (base + insertMap.vecOff) capacity ptr initialized ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output false ∗
      PushContinuation base index count byte auxTail heapId
        initialized remaining output code arity remainder controls calls
        s E Φ) ⊢
      WP (.running
        ⟨⟨[], .i32 base :: .i32 index :: .i32 count ::
            .i32 byte.toUInt32 :: .i32 aux4 :: auxTail, []⟩,
          .block 0 0 growBody :: (storeTail ++ code), arity,
          remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hvec, Hbump, Hstreams, Hcont⟩
  isimp only [PushContinuation] at Hcont
  have hsize : UInt32.size = 4294967296 := rfl
  have hbounds := insertMap_wf
  unfold FrameMap.WF at hbounds
  obtain ⟨_, hvecFits, hframeLe, _⟩ := hbounds
  obtain ⟨hq4, hq8⟩ := vec_facts insertMap insertMap_wf
  have h296 : base + insertMap.vecOff + 8 = base + (insertMap.vecOff + 8) :=
    vec_addr insertMap base 8
  obtain ⟨hb288, hb288_1, hb288_2, hb288_3⟩ :=
    cell_facts base insertMap.vecOff (by omega)
  obtain ⟨hb296, hb296_1, hb296_2, hb296_3⟩ :=
    cell_facts base (insertMap.vecOff + 8) (by omega)
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapacity, Hptr⟩, Hlength, Hstorage⟩
  ihave ⟨Hstorage, %hfits⟩ := VecStorage_length_le heapId capacity ptr
    initialized $$ Hstorage
  ihave Hlength := pointsTo_u32_address_eq h296 $$ Hlength
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  unfold growBody
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := base) (offset := insertMap.vecOff + 8)
    (UInt32.ofNat initialized.length) hb296 hb296_1
    hb296_2 hb296_3 with Hlength
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := base)
    (offset := insertMap.vecOff) capacity
    hb288 hb288_1 hb288_2 hb288_3 with Hcapacity
  ihave Hvec : VecU8 heapId (base + insertMap.vecOff) capacity ptr
      initialized $$ [Hcapacity Hptr Hlength Hstorage]
  · unfold VecU8 RawVecHeader
    isplitl [Hcapacity Hptr]
    · isplitl [Hcapacity]
      · iexact Hcapacity
      · iexact Hptr
    · isplitl [Hlength]
      · iapply pointsTo_u32_address_eq h296.symm $$ Hlength
      · iexact Hstorage
  by_cases hfull : UInt32.ofNat initialized.length = capacity
  · -- the vector is full: grow first
    iapply twp_ne (result := 0) (by simp [hfull])
    iapply twp_brIfZero
    wasm_twp_pures [twp_localGet twp_const twp_add]
      rewriting [UInt32.add_comm insertMap.vecOff base]
    have Hgrow := hfunc98 (base + insertMap.vecOff) base capacity ptr
      initialized shadow
      heapId storedCursor frontier history remaining output false
      (callerLocals :=
        ⟨[], .i32 base :: .i32 index :: .i32 count ::
          .i32 byte.toUInt32 ::
          .i32 (UInt32.ofNat initialized.length) :: auxTail, []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .block, paramArity := 0, resultArity := 0,
          body := growBody, continuation := storeTail ++ code,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hgrow
    simp only [List.cons_append, List.nil_append] at Hgrow
    simp only [growBody] at Hgrow
    iapply Hgrow
    isplitl_exacts [Hruntime Hsp Hreserve Hvec Hbump Hstreams]
    isplitl_pureexact ⟨hbase.1, by omega, hpush⟩
    obtain ⟨_, hnewBound, _, holdNew, _⟩ := hpush.layout
    cases hdecision : classifyBump frontier
        { size := pushCapacity capacity.toNat, alignment := 1 } with
    | oom =>
        isimp only [GrowOneContinuation, hdecision]
        iintro Hsp Hreserve Hvec Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ %remaining Hstreams
    | success newPtr finish =>
        isimp only [GrowOneContinuation, hdecision]
        isplit
        · iintro %finalHistory Hruntime Hsp Hreserve Hvec Hbump %hpush'
            Hstreams
          isimp only [ResumeWP, resumeExpr, List.nil_append,
            List.append_nil]
          wasm_twp_pures [twp_exitControl] using [List.take_zero,
            List.nil_append]
          have hroom : initialized.length <
              (UInt32.ofNat (pushCapacity capacity.toNat)).toNat := by
            rw [UInt32.toNat_ofNat_of_lt' hnewBound]
            omega
          iapply twp_store_tail base index count byte auxTail
            heapId (UInt32.ofNat (pushCapacity capacity.toNat)) newPtr
            initialized hbase.2 hroom
          isplitl_exacts [Hvec]
          iintro Hvec
          ihave Hnormal := BI.and_elim_l $$ Hcont
          iapply Hnormal $$ %(UInt32.ofNat (pushCapacity capacity.toNat))
            %newPtr %finish %finish.toNat %finalHistory
            %(reserveSuccessShadow shadow newPtr
              (UInt32.ofNat (pushCapacity capacity.toNat)))
            Hruntime Hsp Hreserve Hvec Hbump Hstreams
          ipureexact hpush'
        · iintro Hsp Hreserve Hvec Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          iapply Hoom $$ %remaining Hstreams
  · -- the vector has room
    iapply twp_ne (result := 1) (by simp [hfull])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    have hroom : initialized.length < capacity.toNat := by
      rcases Nat.lt_or_eq_of_le hfits with hlt | heq
      · exact hlt
      · exact absurd (by rw [heq]; exact UInt32.ofNat_toNat) hfull
    iapply twp_store_tail base index count byte auxTail
      heapId capacity ptr initialized hbase.2 hroom
    isplitl_exacts [Hvec]
    iintro Hvec
    ihave Hnormal := BI.and_elim_l $$ Hcont
    iapply Hnormal $$ %capacity %ptr %storedCursor %frontier %history
      %shadow Hruntime Hsp Hreserve Hvec Hbump Hstreams
    ipureexact hpush

/-! ## One loop iteration -/

private theorem ofNat_succ_wrap (k : Nat) :
    UInt32.ofNat (k + 1) + 4294967295 = UInt32.ofNat k := by
  rw [UInt32.ofNat_add]
  change UInt32.ofNat k + 1 + 4294967295 = _
  rw [UInt32.add_assoc, show (1 : UInt32) + 4294967295 = 0 from rfl,
    UInt32.add_zero]

private theorem ofNat_ne_256 (n : Nat) (h : n < 256) :
    UInt32.ofNat n ≠ 256 := by
  have hsize : UInt32.size = 4294967296 := rfl
  intro h0
  have := congrArg UInt32.toNat h0
  rw [UInt32.toNat_ofNat_of_lt' (by rw [hsize]; omega)] at this
  simp at this; omega

private theorem ofNat_ne_zero (n : Nat) (h : 0 < n) (hlt : n < 4294967296) :
    UInt32.ofNat n ≠ 0 := by
  have hsize : UInt32.size = 4294967296 := rfl
  intro h0
  have := congrArg UInt32.toNat h0
  rw [UInt32.toNat_ofNat_of_lt' (by rw [hsize]; omega)] at this
  simp at this; omega

/-- One iteration of the read loop: one push, then either the branch back,
or the next read and its classification. -/
theorem twp_loop_iteration [WasmSmallStepGS hlc Universal.State]
    (hfunc98 : Func98Spec (hlc := hlc))
    (base : UInt32) (heapId : GName) (input output : List UInt8)
    (auxTail : List Value)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hbase : 16 ≤ base.toNat ∧
      base.toNat + insertMap.frame.toNat < UInt32.size)
    (st : LoopState) :
    iprop(
      LoopInv base heapId input output auxTail afterLoop arity
        remainder controls calls s E Φ st ∗
      (∀ j : LoopState, ⌜loopMeasure j < loopMeasure st⌝ -∗
        LoopInv base heapId input output auxTail afterLoop
          arity remainder controls calls s E Φ j -∗
        WP (loopBodyExpr (α := Universal.State)
          (loopLocals base auxTail j) 0 0 arity readLoopBody
          afterLoop remainder [] controls calls) @ s; E [{ Φ }])) ⊢
      WP (loopBodyExpr (α := Universal.State)
        (loopLocals base auxTail st) 0 0 arity readLoopBody
        afterLoop remainder [] controls calls) @ s; E [{ Φ }] := by
  iintro ⟨Hinv, Hrec⟩
  isimp only [LoopInv] at Hinv
  icases Hinv with
    ⟨Hruntime, Hsp, Hreserve, Hchunk, Hvec, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨hinput, hindex, hbuffer, hpush⟩ := hfacts
  have hsize : UInt32.size = 4294967296 := rfl
  have hindexLt : st.index < 256 := by omega
  have hbufferIndex : st.index < (st.chunk ++ st.chunkTail).length := by
    simp only [List.length_append]; omega
  have hbyte : (st.chunk ++ st.chunkTail)[st.index] = st.chunk[st.index] :=
    List.getElem_append_left hindex
  simp only [Wasm.SmallStep.loopBodyExpr, loopLocals, readLoopBody]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  unfold pushBody
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const]
  iapply twp_eq (result := 0) (by rw [if_neg (ofNat_ne_256 st.index hindexLt)])
  iapply twp_brIfZero
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm insertMap.chunkOff base]
  wasm_twp_pures [twp_localGet twp_add]
    rewriting [UInt32.add_comm (UInt32.ofNat st.index)
      (base + insertMap.chunkOff)]
  ihave ⟨Hbyte, Hclose⟩ := ByteSlice_byteFocus (base + insertMap.chunkOff)
    (st.chunk ++ st.chunkTail) st.index hbufferIndex $$ Hchunk
  wasm_twp_rebind twp_load8U_addr_gen ((st.chunk ++ st.chunkTail)[st.index])
    with Hbyte
  ihave Hchunk := Hclose $$ Hbyte
  rw [hbyte]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_push_byte hfunc98 base (UInt32.ofNat st.index)
    (UInt32.ofNat (st.chunk.length - st.index)) (st.chunk[st.index])
    st.aux4 auxTail heapId st.capacity st.ptr
    (st.pushed ++ st.chunk.take st.index) st.shadow st.remaining output
    st.storedCursor st.frontier st.history hbase hpush
  isplitl_exacts [Hruntime Hsp Hreserve Hvec Hbump Hstreams]
  unfold PushContinuation
  isplit
  · iintro %capacity' %ptr' %storedCursor' %frontier' %history' %shadow'
      Hruntime Hsp Hreserve Hvec Hbump Hstreams %hpush'
    wasm_twp_pures [twp_localGet twp_const twp_add]
      rewriting [UInt32.add_comm 4294967295
        (UInt32.ofNat (st.chunk.length - st.index))]
    have hcount' : UInt32.ofNat (st.chunk.length - st.index) + 4294967295 =
        UInt32.ofNat (st.chunk.length - (st.index + 1)) := by
      rw [show st.chunk.length - st.index =
        (st.chunk.length - (st.index + 1)) + 1 by omega]
      exact ofNat_succ_wrap _
    rw [hcount']
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    have hvecStep : st.pushed ++ st.chunk.take st.index ++
        [st.chunk[st.index]] =
        st.pushed ++ st.chunk.take (st.index + 1) := by
      rw [List.take_succ_eq_append_getElem hindex, List.append_assoc]
    by_cases hlast : st.index + 1 = st.chunk.length
    · -- the chunk is consumed: read the next chunk
      have hzero : UInt32.ofNat (st.chunk.length - (st.index + 1)) = 0 := by
        rw [show st.chunk.length - (st.index + 1) = 0 by omega]; rfl
      rw [hzero]
      iapply twp_brIfZero
      wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
      unfold nextRead
      wasm_twp_pures [twp_const]
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      have hvecFull : st.pushed ++ st.chunk.take st.index ++
          [st.chunk[st.index]] =
          st.pushed ++ st.chunk := by
        rw [hvecStep, hlast, List.take_length]
      iapply twp_read_chunk base (st.chunk ++ st.chunkTail) st.remaining
        output
        []
        (.i32 base :: .i32 0 :: .i32 0 ::
          .i32 (st.chunk[st.index]).toUInt32 ::
          .i32 (UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length) ::
          auxTail)
        (stack := []) (code := [.localTee 2, .br_if 0]) rfl
        (by simp only [List.length_append]; omega)
      isplitl_exacts [Hruntime Hstreams Hchunk]
      iintro Hruntime Hstreams Hchunk %hcount
      wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      by_cases hempty : st.remaining = []
      · -- the stream is empty: leave the loop
        have hcount0 : min 256 st.remaining.length = 0 := by
          rw [hempty]; rfl
        rw [hcount0, show UInt32.ofNat 0 = (0 : UInt32) from rfl]
        iapply twp_brIfZero
        wasm_twp_pures [twp_exitControl] using [List.take_zero,
          List.nil_append]
        isimp only [hcount0, hempty, List.take_zero, List.drop_zero,
          List.nil_append, List.drop_nil] at Hstreams
        isimp only [hcount0, hempty, List.take_zero, List.drop_zero,
          List.nil_append, List.drop_nil] at Hchunk
        have hinputFull : st.pushed ++ st.chunk = input := by
          rw [hinput, hempty, List.append_nil]
        ihave Hvec := VecU8_initialized_eq (hvecFull.trans hinputFull) $$ Hvec
        isimp only [LoopContinuation, afterLoopLocals] at Hcont
        ihave Hnormal := BI.and_elim_l $$ Hcont
        iapply Hnormal $$ %capacity' %ptr' %storedCursor' %frontier' %history'
          %shadow' %(st.chunk ++ st.chunkTail)
          %((st.chunk[st.index]).toUInt32)
          %(UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length)
          Hruntime Hsp Hreserve Hchunk Hvec Hbump Hstreams
        ipureintro
        exact ⟨by simp only [List.length_append]; omega, hpush'⟩
      · -- the stream has more bytes: branch back with the next chunk
        have hremainingPos : 0 < st.remaining.length :=
          List.length_pos_of_ne_nil hempty
        have hcountPos : 0 < min 256 st.remaining.length := by omega
        have hcountLe : min 256 st.remaining.length ≤ st.remaining.length :=
          Nat.min_le_right _ _
        iapply twp_brIf (ofNat_ne_zero _ hcountPos (by omega)) (by rfl)
        let next : LoopState :=
          { pushed := st.pushed ++ st.chunk
            chunk := st.remaining.take (min 256 st.remaining.length)
            index := 0
            chunkTail :=
              (st.chunk ++ st.chunkTail).drop (min 256 st.remaining.length)
            remaining := st.remaining.drop (min 256 st.remaining.length)
            capacity := capacity'
            ptr := ptr'
            shadow := shadow'
            storedCursor := storedCursor'
            frontier := frontier'
            history := history'
            aux3 := (st.chunk[st.index]).toUInt32
            aux4 :=
              UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length }
        have htakeLen :
            (st.remaining.take (min 256 st.remaining.length)).length - 0 =
              min 256 st.remaining.length := by
          simp only [List.length_take, Nat.sub_zero]
          exact Nat.min_eq_left hcountLe
        have hmeasure : loopMeasure next < loopMeasure st := by
          simp only [loopMeasure, next, List.length_drop, List.length_take]
          omega
        ihave Hback := Hrec $$ %next %hmeasure
        isimp only [Wasm.SmallStep.loopBodyExpr, loopLocals, next, htakeLen,
          show UInt32.ofNat 0 = (0 : UInt32) from rfl] at Hback
        simp only [List.take_zero, List.nil_append]
        iapply Hback
        unfold LoopInv
        simp only [List.take_zero, List.append_nil]
        ihave Hvec := VecU8_initialized_eq hvecFull $$ Hvec
        isplitl_exacts [Hruntime Hsp Hreserve Hchunk Hvec Hbump Hstreams]
        isplitl_pureexact (by
          refine ⟨?_, ?_, ?_, hpush'⟩
          · rw [hinput, List.append_assoc, List.append_assoc,
              List.take_append_drop, List.append_assoc]
          · simp only [List.length_take]; omega
          · simp only [List.length_take, List.length_drop, List.length_append]
            omega)
        iexact Hcont
    · -- chunk bytes remain: branch back
      have hmore : st.index + 1 < st.chunk.length := by omega
      iapply twp_brIf (ofNat_ne_zero _ (by omega) (by omega)) (by rfl)
      let next : LoopState :=
        { st with
          index := st.index + 1
          capacity := capacity'
          ptr := ptr'
          shadow := shadow'
          storedCursor := storedCursor'
          frontier := frontier'
          history := history'
          aux3 := (st.chunk[st.index]).toUInt32
          aux4 :=
            UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length }
      have hmeasure : loopMeasure next < loopMeasure st := by
        simp only [loopMeasure, next]
        omega
      ihave Hback := Hrec $$ %next %hmeasure
      isimp only [Wasm.SmallStep.loopBodyExpr, loopLocals, next] at Hback
      simp only [List.take_zero, List.nil_append]
      rw [show UInt32.ofNat st.index + 1 = UInt32.ofNat (st.index + 1) by
        rw [UInt32.ofNat_add]; rfl]
      iapply Hback
      unfold LoopInv
      ihave Hvec := VecU8_initialized_eq hvecStep $$ Hvec
      isplitl_exacts [Hruntime Hsp Hreserve Hchunk Hvec Hbump Hstreams]
      isplitl_pureexact ⟨hinput, hmore, hbuffer, hpush'⟩
      iexact Hcont
  · iintro %remaining' Hstreams
    isimp only [LoopContinuation] at Hcont
    ihave Hoom := BI.and_elim_r $$ Hcont
    iapply Hoom $$ %remaining' Hstreams

/-- The read loop, closed by well-founded recursion on the measure. -/
theorem twp_read_loop [WasmSmallStepGS hlc Universal.State]
    (hfunc98 : Func98Spec (hlc := hlc))
    (base : UInt32) (heapId : GName) (input output : List UInt8)
    (auxTail : List Value)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hbase : 16 ≤ base.toNat ∧
      base.toNat + insertMap.frame.toNat < UInt32.size)
    (initial : LoopState) :
    LoopInv base heapId input output auxTail afterLoop arity
        remainder controls calls s E Φ initial ⊢
      WP (.running
        ⟨loopLocals base auxTail initial,
          .loop 0 0 readLoopBody :: afterLoop, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LoopState) (measure := loopMeasure)
    (locals := loopLocals base auxTail)
    (I := LoopInv base heapId input output auxTail afterLoop
      arity remainder controls calls s E Φ)
    (initial := initial)
    (initialLocals := loopLocals base auxTail initial)
    (body := readLoopBody) (code := afterLoop)
    (paramArity := 0) (resultArity := 0)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (belowStack := []) rfl rfl
  · intro st
    iintro Hrec Hinv
    iapply twp_loop_iteration hfunc98 base heapId input output auxTail
      afterLoop arity remainder controls calls s E Φ hbase st
    isplitl [Hinv]
    · iexact Hinv
    · iexact Hrec
end Project.RustHashMap.InsertRead
