import Project.Mergesort.DriverInputProof

/-!
# Generated buffered-I/O sub-constructors

This file closes the two constructor calls that `DriverInputProof.lean`
deliberately left open inside `func135` (the buffered-I/O constructor at
absolute index 137):

* local `func136` (`BufReader::new`, absolute call 138) allocates its
  8192-byte read buffer through absolute call 141 (local `func139`, the
  `Vec::with_capacity` reservation path into the zeroed allocator) and then
  builds the 20-byte `BufReader` descriptor in the caller-provided slot;
* local `func137` (`BufWriter::new`, absolute call 139) allocates its
  8192-byte write buffer through absolute call 142 (local `func140`, the
  iterator-collect reservation path into the same allocator) and then builds
  the 13-byte `BufWriter` descriptor in the caller-provided slot.

Neither allocation goes through the plain-malloc forwarder at absolute 133
that `AllocatorProof.lean` closes on the singleton small-bin path, and an
8192-byte request would not take the small-bin path anyway.  Both allocator
calls therefore stay as explicit seam boundaries in the same idiom as the
committed `.call 138`/`.call 139` boundaries they replace: every rule here
stops exactly at the generated `.call 141` / `.call 142`, and the epilogue
rules resume right after it, assuming only the two descriptor words the
reservation shim writes into the constructor frame.

The final section composes the committed `func135` segments with the rules
here, reducing the driver-facing absolute `.call 137` to exactly the two
allocator-core boundaries.
-/

namespace Project.Mergesort.BufferedCtorProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.DriverProof
open Project.Mergesort.RangeProof
open Project.Mergesort.SplitAtProof
open Project.Mergesort.FormatProof
open Project.Mergesort.MemoryFillProof
open Project.Mergesort.DriverInputProof

/-! ## Stable names for the allocator-side callees left open here -/

theorem readerAlloc_index : «module».funcs[139]? = some func139Def := by rfl
theorem writerAlloc_index : «module».funcs[140]? = some func140Def := by rfl

/-! ## `BufReader::new` (`func136`, absolute call 138)

`func136` installs a 32-byte frame, reserves the 8192-byte buffer through
absolute call 141 (which writes `(pointer, capacity)` to `frame + 0` and
`frame + 4`), assembles the five-word descriptor scratch at `frame + 12`, and
copies the 20-byte `BufReader` descriptor `(pointer, capacity, 0, 0, 0)` into
the caller-provided destination. -/

def bufReaderAtAlloc : Program := func136.drop 8
def bufReaderAfterAlloc : Program := func136.drop 9

theorem func136_eq_allocPrefix :
    func136 =
      [.globalGet 0, .const 32, .sub, .localSet 1, .localGet 1, .globalSet 0,
       .localGet 1, .const 8192] ++ bufReaderAtAlloc := by
  rfl

theorem bufReaderAtAlloc_eq :
    bufReaderAtAlloc = .call 141 :: bufReaderAfterAlloc := by
  rfl

theorem bufReaderAfterAlloc_eq :
    bufReaderAfterAlloc =
      [.localGet 1, .load32 4, .localSet 2,
       .localGet 1, .localGet 1, .load32 0, .store32 12,
       .localGet 1, .localGet 2, .store32 16,
       .localGet 1, .const 0, .store32 20,
       .localGet 1, .const 0, .store32 24,
       .localGet 1, .const 0, .store32 28,
       .localGet 0, .localGet 1, .load32 28, .store32 16,
       .localGet 0, .localGet 1, .load64 20, .store64 8,
       .localGet 0, .localGet 1, .load64 12, .store64 0,
       .localGet 1, .const 32, .add, .globalSet 0] ++ [.ret] := by
  rfl

/-- Exact prefix of `BufReader::new`: install the 32-byte frame and stop right
before the buffer reservation at absolute index 141 with `(frame, 8192)` on
the stack. -/
theorem bufReader_to_alloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 (stackTop - 32), .i32 0],
              [.i32 8192, .i32 (stackTop - 32)]⟩,
            bufReaderAtAlloc, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 0, .i32 0], []⟩,
        func136, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hcont⟩
  rw [func136_eq_allocPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply Hcont $$ Hglobal

/-! Exact epilogue of `BufReader::new`, resuming right after the buffer
reservation at absolute 141 returned.  The reservation seam is assumed to
have written the buffer pointer to `frame + 0` and the capacity to
`frame + 4`; the rule assembles the descriptor scratch and copies the
20-byte `BufReader` descriptor into `dst`, leaving exactly the field layout
`buffered_epilogue_twp` consumes at `frame135 + 12`. -/
set_option maxHeartbeats 4000000 in
theorem bufReader_after_alloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst frame bufPtr bufCap : UInt32)
    (old12 old16 old20 old24 old28 : UInt32)
    (oldDst0 oldDst8 : UInt64) (oldDst16 : UInt32)
    (hframeRoom : frame.toNat + 32 ≤ UInt32.size)
    (hdstRoom : dst.toNat + 20 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 (frame + 0) bufPtr ∗
      pointsTo_u32 (frame + 4) bufCap ∗
      pointsTo_u32 (frame + 12) old12 ∗
      pointsTo_u32 (frame + 16) old16 ∗
      pointsTo_u32 (frame + 20) old20 ∗
      pointsTo_u32 (frame + 24) old24 ∗
      pointsTo_u32 (frame + 28) old28 ∗
      pointsTo_u64 (dst + 0) oldDst0 ∗
      pointsTo_u64 (dst + 8) oldDst8 ∗
      pointsTo_u32 (dst + 16) oldDst16 ∗
      (globalPointsTo 0 (.i32 (32 + frame)) -∗
        pointsTo_u32 (frame + 0) bufPtr -∗
        pointsTo_u32 (frame + 4) bufCap -∗
        pointsTo_u64 (frame + 12) (packU32 bufPtr bufCap) -∗
        pointsTo_u64 (frame + 20) (packU32 0 0) -∗
        pointsTo_u32 (frame + 28) 0 -∗
        pointsTo_u64 (dst + 0) (packU32 bufPtr bufCap) -∗
        pointsTo_u64 (dst + 8) (packU32 0 0) -∗
        pointsTo_u32 (dst + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 frame, .i32 bufCap], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 frame, .i32 0], []⟩,
        bufReaderAfterAlloc, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf00, hf01, hf02, hf03⟩ :=
    descriptorSlot32Facts frame 0 32 hframeRoom (by decide)
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts frame 4 32 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 32 hframeRoom (by decide)
  obtain ⟨hf160, hf161, hf162, hf163⟩ :=
    descriptorSlot32Facts frame 16 32 hframeRoom (by decide)
  obtain ⟨hf200, hf201, hf202, hf203⟩ :=
    descriptorSlot32Facts frame 20 32 hframeRoom (by decide)
  obtain ⟨hf240, hf241, hf242, hf243⟩ :=
    descriptorSlot32Facts frame 24 32 hframeRoom (by decide)
  obtain ⟨hf280, hf281, hf282, hf283⟩ :=
    descriptorSlot32Facts frame 28 32 hframeRoom (by decide)
  obtain ⟨hw120, hw121, hw122, hw123, hw124, hw125, hw126, hw127⟩ :=
    descriptorSlot64Facts frame 12 32 hframeRoom (by decide)
  obtain ⟨hw200, hw201, hw202, hw203, hw204, hw205, hw206, hw207⟩ :=
    descriptorSlot64Facts frame 20 32 hframeRoom (by decide)
  obtain ⟨hd00, hd01, hd02, hd03, hd04, hd05, hd06, hd07⟩ :=
    descriptorSlot64Facts dst 0 20 hdstRoom (by decide)
  obtain ⟨hd80, hd81, hd82, hd83, hd84, hd85, hd86, hd87⟩ :=
    descriptorSlot64Facts dst 8 20 hdstRoom (by decide)
  obtain ⟨hd160, hd161, hd162, hd163⟩ :=
    descriptorSlot32Facts dst 16 20 hdstRoom (by decide)
  iintro ⟨Hglobal, H0, H4, H12, H16, H20, H24, H28, Hd0, Hd8, Hd16, Hcont⟩
  rw [bufReaderAfterAlloc_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 bufCap hf40 hf41 hf42 hf43 $$ H4
  iintro H4
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 bufPtr hf00 hf01 hf02 hf03 $$ H0
  iintro H0
  iapply twp_store32 old12 hf120 hf121 hf122 hf123 $$ H12
  iintro H12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old16 hf160 hf161 hf162 hf163 $$ H16
  iintro H16
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old20 hf200 hf201 hf202 hf203 $$ H20
  iintro H20
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old24 hf240 hf241 hf242 hf243 $$ H24
  iintro H24
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old28 hf280 hf281 hf282 hf283 $$ H28
  iintro H28
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 0 hf280 hf281 hf282 hf283 $$ H28
  iintro H28
  iapply twp_store32 oldDst16 hd160 hd161 hd162 hd163 $$ Hd16
  iintro Hd16
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave H20word : pointsTo_u64 (frame + 20) (packU32 0 0) $$ [H20 H24]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 20) 0 0).mp
    isimp only [sliceDescriptorAt]
    isplitl [H20]
    · iexact H20
    rw [show (frame + 20) + 4 = frame + 24 from by bv_decide]
    iexact H24
  iapply twp_load64 (packU32 0 0)
    hw200 hw201 hw202 hw203 hw204 hw205 hw206 hw207 $$ H20word
  iintro H20word
  iapply twp_store64 oldDst8 hd80 hd81 hd82 hd83 hd84 hd85 hd86 hd87 $$ Hd8
  iintro Hd8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave H12word : pointsTo_u64 (frame + 12) (packU32 bufPtr bufCap) $$
      [H12 H16]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 12) bufPtr bufCap).mp
    isimp only [sliceDescriptorAt]
    isplitl [H12]
    · iexact H12
    rw [show (frame + 12) + 4 = frame + 16 from by bv_decide]
    iexact H16
  iapply twp_load64 (packU32 bufPtr bufCap)
    hw120 hw121 hw122 hw123 hw124 hw125 hw126 hw127 $$ H12word
  iintro H12word
  iapply twp_store64 oldDst0 hd00 hd01 hd02 hd03 hd04 hd05 hd06 hd07 $$ Hd0
  iintro Hd0
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hcont $$ Hglobal H0 H4 H12word H20word H28 Hd0 Hd8 Hd16

/-- Composable entry rule for `BufReader::new` at absolute index 138,
stopping at the buffer-reservation boundary (absolute call 141) inside the
freshly pushed callee frame. -/
theorem bufReaderCtor_call_to_alloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 (stackTop - 32), .i32 0],
              [.i32 8192, .i32 (stackTop - 32)]⟩,
            bufReaderAtAlloc, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 dst :: stack },
        .call 138 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 138 func136Def
      (by decide) bufReaderCtor_index $$ Hruntime
  iintro Hruntime
  simp [func136Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := bufReader_to_alloc_twp (α := α)
    dst stackTop (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hcont $$ Hruntime Hglobal

/-! ## `BufWriter::new` (`func137`, absolute call 139)

`func137` installs a 32-byte frame, reserves its 8192-byte buffer through
absolute call 142 (which writes `(pointer, capacity)` to `frame + 8` and
`frame + 12`), and builds the 13-byte `BufWriter` descriptor in the
caller-provided slot: the `(pointer, capacity)` word at `dst + 0`, the fill
length `0` at `dst + 8`, and the panicked-flag byte `0` at `dst + 12`. -/

def bufWriterAtAlloc : Program := func137.drop 16
def bufWriterAfterAlloc : Program := func137.drop 17

theorem func137_eq_allocPrefix :
    func137 =
      [.globalGet 0, .const 32, .sub, .localSet 1, .localGet 1, .globalSet 0,
       .const 1, .localSet 2, .const 8192, .localSet 3,
       .localGet 1, .const 8, .add, .localGet 3, .localGet 2, .localGet 2] ++
      bufWriterAtAlloc := by
  rfl

theorem bufWriterAtAlloc_eq :
    bufWriterAtAlloc = .call 142 :: bufWriterAfterAlloc := by
  rfl

theorem bufWriterAfterAlloc_eq :
    bufWriterAfterAlloc =
      [.localGet 1, .load32 12, .localSet 4,
       .localGet 1, .localGet 1, .load32 8, .store32 20,
       .localGet 1, .localGet 4, .store32 24,
       .localGet 1, .const 0, .store32 28,
       .localGet 0, .localGet 1, .load32 28, .store32 8,
       .localGet 0, .localGet 1, .load64 20, .store64 0,
       .localGet 0, .const 0, .store8 12,
       .localGet 1, .const 32, .add, .globalSet 0] ++ [.ret] := by
  rfl

/-- Exact prefix of `BufWriter::new`: install the 32-byte frame and stop
right before the buffer reservation at absolute index 142 with
`(frame + 8, 8192, 1, 1)` on the stack. -/
theorem bufWriter_to_alloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 (stackTop - 32), .i32 1, .i32 8192, .i32 0],
              [.i32 1, .i32 1, .i32 8192, .i32 (8 + (stackTop - 32))]⟩,
            bufWriterAtAlloc, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func137, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hcont⟩
  rw [func137_eq_allocPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (8 : UInt32) + (stackTop - 32) = 8 + (stackTop - 32) from rfl]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Hcont $$ Hglobal

/-! ## Byte-granular view of the `BufWriter` length/flag word

The generated code writes the second `BufWriter` descriptor word with an
`i32.store` at `dst + 8` followed by an `i8.store` at `dst + 12`, while the
`func135` epilogue later copies it back with one `i64.load` at `dst + 8`.
The lemmas below split an owned u64 cell into its low u32 cell plus four raw
bytes and reassemble it, and `bufWriterTag` is the exact value the reassembled
word carries: length `0`, flag byte `0`, and the three untouched high bytes
of the previous contents. -/

/-- Value of the `BufWriter` length/flag word after the constructor: the low
five bytes are zeroed, the high three bytes keep their previous contents. -/
def bufWriterTag (old : UInt64) : UInt64 :=
  old &&& 0xFFFFFF0000000000

private theorem u32Byte_toUInt32_eq (v : UInt64) (n : Nat) (hn : n < 4) :
    u32Byte v.toUInt32 n = u64Byte v n := by
  interval_cases n <;> simp [u32Byte, u64Byte] <;> bv_decide

/-- An owned u64 cell is exactly its low u32 cell plus the four raw high
bytes. -/
theorem pointsTo_u64_low32_split [WasmHeapGS]
    (addr : UInt32) (v : UInt64) :
    pointsTo_u64 addr v ⊣⊢
      pointsTo_u32 addr v.toUInt32 ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (addr + 4) (DFrac.own 1) (some (u64Byte v 4)) ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (addr + 5) (DFrac.own 1) (some (u64Byte v 5)) ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (addr + 6) (DFrac.own 1) (some (u64Byte v 6)) ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (addr + 7) (DFrac.own 1) (some (u64Byte v 7)) := by
  simp only [pointsTo_u64, pointsTo_u32]
  rw [u32Byte_toUInt32_eq v 0 (by decide), u32Byte_toUInt32_eq v 1 (by decide),
    u32Byte_toUInt32_eq v 2 (by decide), u32Byte_toUInt32_eq v 3 (by decide)]
  constructor
  · iintro ⟨Ha, Hb, Hc, Hd, He, Hf, Hg, Hh⟩
    iframe
  · iintro ⟨⟨Ha, Hb, Hc, Hd⟩, He, Hf, Hg, Hh⟩
    iframe

private theorem bufWriterTag_low (v : UInt64) :
    (bufWriterTag v).toUInt32 = 0 := by
  simp only [bufWriterTag]
  bv_decide

private theorem bufWriterTag_byte4 (v : UInt64) :
    u64Byte (bufWriterTag v) 4 = (0 : UInt32).toUInt8 := by
  simp only [bufWriterTag, u64Byte]
  bv_decide

private theorem bufWriterTag_byte5 (v : UInt64) :
    u64Byte (bufWriterTag v) 5 = u64Byte v 5 := by
  simp only [bufWriterTag, u64Byte]
  bv_decide

private theorem bufWriterTag_byte6 (v : UInt64) :
    u64Byte (bufWriterTag v) 6 = u64Byte v 6 := by
  simp only [bufWriterTag, u64Byte]
  bv_decide

private theorem bufWriterTag_byte7 (v : UInt64) :
    u64Byte (bufWriterTag v) 7 = u64Byte v 7 := by
  simp only [bufWriterTag, u64Byte]
  bv_decide

/-! Exact epilogue of `BufWriter::new`, resuming right after the buffer
reservation at absolute 142 returned.  The reservation seam is assumed to
have written the buffer pointer to `frame + 8` and the capacity to
`frame + 12`; the rule builds the descriptor and leaves exactly the field
layout `buffered_epilogue_twp` consumes at `frame135 + 32`: the
`(pointer, capacity)` word at `dst + 0` and the zeroed length/flag word
`bufWriterTag oldDst8` at `dst + 8`. -/
set_option maxHeartbeats 4000000 in
theorem bufWriter_after_alloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst frame bufPtr bufCap : UInt32)
    (old20 old24 old28 : UInt32)
    (oldDst0 oldDst8 : UInt64)
    (hframeRoom : frame.toNat + 32 ≤ UInt32.size)
    (hdstRoom : dst.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 (frame + 8) bufPtr ∗
      pointsTo_u32 (frame + 12) bufCap ∗
      pointsTo_u32 (frame + 20) old20 ∗
      pointsTo_u32 (frame + 24) old24 ∗
      pointsTo_u32 (frame + 28) old28 ∗
      pointsTo_u64 (dst + 0) oldDst0 ∗
      pointsTo_u64 (dst + 8) oldDst8 ∗
      (globalPointsTo 0 (.i32 (32 + frame)) -∗
        pointsTo_u32 (frame + 8) bufPtr -∗
        pointsTo_u32 (frame + 12) bufCap -∗
        pointsTo_u64 (frame + 20) (packU32 bufPtr bufCap) -∗
        pointsTo_u32 (frame + 28) 0 -∗
        pointsTo_u64 (dst + 0) (packU32 bufPtr bufCap) -∗
        pointsTo_u64 (dst + 8) (bufWriterTag oldDst8) -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 frame, .i32 1, .i32 8192, .i32 bufCap], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 frame, .i32 1, .i32 8192, .i32 0], []⟩,
        bufWriterAfterAlloc, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 32 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 32 hframeRoom (by decide)
  obtain ⟨hf200, hf201, hf202, hf203⟩ :=
    descriptorSlot32Facts frame 20 32 hframeRoom (by decide)
  obtain ⟨hf240, hf241, hf242, hf243⟩ :=
    descriptorSlot32Facts frame 24 32 hframeRoom (by decide)
  obtain ⟨hf280, hf281, hf282, hf283⟩ :=
    descriptorSlot32Facts frame 28 32 hframeRoom (by decide)
  obtain ⟨hw200, hw201, hw202, hw203, hw204, hw205, hw206, hw207⟩ :=
    descriptorSlot64Facts frame 20 32 hframeRoom (by decide)
  obtain ⟨hd00, hd01, hd02, hd03, hd04, hd05, hd06, hd07⟩ :=
    descriptorSlot64Facts dst 0 16 hdstRoom (by decide)
  obtain ⟨hd80, hd81, hd82, hd83⟩ :=
    descriptorSlot32Facts dst 8 16 hdstRoom (by decide)
  have hd12 : (dst + (12 : UInt32)).toNat = dst.toNat + (12 : UInt32).toNat :=
    (descriptorSlot32Facts dst 12 16 hdstRoom (by decide)).1
  iintro ⟨Hglobal, H8, H12, H20, H24, H28, Hd0, Hd8, Hcont⟩
  ihave Hd8parts := (pointsTo_u64_low32_split (dst + 8) oldDst8).mp $$ Hd8
  icases Hd8parts with ⟨Hd8lo, Hb4, Hb5, Hb6, Hb7⟩
  rw [bufWriterAfterAlloc_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 bufCap hf120 hf121 hf122 hf123 $$ H12
  iintro H12
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 bufPtr hf80 hf81 hf82 hf83 $$ H8
  iintro H8
  iapply twp_store32 old20 hf200 hf201 hf202 hf203 $$ H20
  iintro H20
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old24 hf240 hf241 hf242 hf243 $$ H24
  iintro H24
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old28 hf280 hf281 hf282 hf283 $$ H28
  iintro H28
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 0 hf280 hf281 hf282 hf283 $$ H28
  iintro H28
  iapply twp_store32 oldDst8.toUInt32 hd80 hd81 hd82 hd83 $$ Hd8lo
  iintro Hd8lo
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave H20word : pointsTo_u64 (frame + 20) (packU32 bufPtr bufCap) $$
      [H20 H24]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 20) bufPtr bufCap).mp
    isimp only [sliceDescriptorAt]
    isplitl [H20]
    · iexact H20
    rw [show (frame + 20) + 4 = frame + 24 from by bv_decide]
    iexact H24
  iapply twp_load64 (packU32 bufPtr bufCap)
    hw200 hw201 hw202 hw203 hw204 hw205 hw206 hw207 $$ H20word
  iintro H20word
  iapply twp_store64 oldDst0 hd00 hd01 hd02 hd03 hd04 hd05 hd06 hd07 $$ Hd0
  iintro Hd0
  iapply twp_localGet rfl
  iapply twp_const
  ihave Hb12 : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (dst + 12) (DFrac.own 1) (some (u64Byte oldDst8 4)) $$ [Hb4]
  · rw [show dst + 12 = (dst + 8) + 4 from by bv_decide]
    iexact Hb4
  iapply twp_store8_owned (u64Byte oldDst8 4) hd12 $$ Hb12
  iintro Hb12
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave Hd8new : pointsTo_u64 (dst + 8) (bufWriterTag oldDst8) $$
      [Hd8lo Hb12 Hb5 Hb6 Hb7]
  · iapply (pointsTo_u64_low32_split (dst + 8) (bufWriterTag oldDst8)).mpr
    rw [bufWriterTag_low, bufWriterTag_byte4, bufWriterTag_byte5,
      bufWriterTag_byte6, bufWriterTag_byte7]
    isplitl [Hd8lo]
    · iexact Hd8lo
    isplitl [Hb12]
    · rw [show (dst + 8) + 4 = dst + 12 from by bv_decide]
      iexact Hb12
    isplitl [Hb5]
    · iexact Hb5
    isplitl [Hb6]
    · iexact Hb6
    iexact Hb7
  iapply Hcont $$ Hglobal H8 H12 H20word H28 Hd0 Hd8new

/-- Composable entry rule for `BufWriter::new` at absolute index 139,
stopping at the buffer-reservation boundary (absolute call 142) inside the
freshly pushed callee frame. -/
theorem bufWriterCtor_call_to_alloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 (stackTop - 32), .i32 1, .i32 8192, .i32 0],
              [.i32 1, .i32 1, .i32 8192, .i32 (8 + (stackTop - 32))]⟩,
            bufWriterAtAlloc, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 dst :: stack },
        .call 139 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 139 func137Def
      (by decide) bufWriterCtor_index $$ Hruntime
  iintro Hruntime
  simp [func137Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := bufWriter_to_alloc_twp (α := α)
    dst stackTop (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hcont $$ Hruntime Hglobal

/-! ## Composed driver-facing rules for absolute `.call 137`

A fully closed rule for the buffered-I/O constructor is not yet possible: the
two buffer reservations (absolute 141 and 142) are allocator-owned and both
funnel into the zeroed-allocation path at absolute 146, not into the
plain-malloc forwarder at absolute 133 whose singleton path is already
closed.  The three rules below are the honest composition: together they
reduce `.call 137` to exactly those two reservation boundaries, with every
other generated instruction of `func135`, `func136`, and `func137` proven. -/

/-- Composed entry rule for the buffered-I/O constructor at absolute index
137: runs the committed `func135` prefix and the whole `BufReader::new`
prefix, stopping at the first buffer-reservation boundary (absolute call 141)
with both constructor frames pushed. -/
theorem buffered_call_to_readerAlloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 ((stackTop - 48) - 32)) -∗
        WP (.running
          ⟨⟨[.i32 (12 + (stackTop - 48))],
              [.i32 ((stackTop - 48) - 32), .i32 0],
              [.i32 8192, .i32 ((stackTop - 48) - 32)]⟩,
            bufReaderAtAlloc, 0, [], [],
            { locals := ⟨[.i32 dst], [.i32 (stackTop - 48), .i32 0], []⟩
              continuation := bufferedAfterReaderCtor
              resultArity := 0
              callerRemainder := []
              control := [] } ::
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 dst :: stack },
        .call 137 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hcont⟩
  iapply buffered_call_to_readerCtor_twp (α := α) dst stackTop
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hruntime Hglobal
  rw [bufferedAtReaderCtor_eq]
  have Hcall := bufReaderCtor_call_to_alloc_twp (α := α)
    (12 + (stackTop - 48)) (stackTop - 48) (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[.i32 dst], [.i32 (stackTop - 48), .i32 0], []⟩)
    (stack := []) (code := bufferedAfterReaderCtor) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hruntime Hglobal
  iapply Hcont $$ Hruntime Hglobal

/-! Composed middle stretch: resume right after the `BufReader` buffer
reservation (absolute 141) returned, run the `BufReader::new` epilogue,
return to `func135`, run the committed between-constructors segment, enter
`BufWriter::new`, and stop at its buffer-reservation boundary (absolute call
142).  `f` is the `func135` frame; both sub-constructors reuse the same
32-byte frame `f - 32` below it.  The reader descriptor lands at
`f + 12`/`f + 20`/`f + 28`, exactly where `buffered_epilogue_twp` reads it
back. -/
set_option maxHeartbeats 4000000 in
theorem buffered_readerAlloc_to_writerAlloc_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst f bufPtr bufCap : UInt32)
    (old12 old16 old20 old24 old28 : UInt32)
    (oldR0 oldR8 : UInt64) (oldR16 : UInt32)
    (hctorFrameRoom : (f - 32).toNat + 32 ≤ UInt32.size)
    (hreaderDstRoom : (12 + f).toNat + 20 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 (f - 32)) ∗
      pointsTo_u32 ((f - 32) + 0) bufPtr ∗
      pointsTo_u32 ((f - 32) + 4) bufCap ∗
      pointsTo_u32 ((f - 32) + 12) old12 ∗
      pointsTo_u32 ((f - 32) + 16) old16 ∗
      pointsTo_u32 ((f - 32) + 20) old20 ∗
      pointsTo_u32 ((f - 32) + 24) old24 ∗
      pointsTo_u32 ((f - 32) + 28) old28 ∗
      pointsTo_u64 (f + 12) oldR0 ∗
      pointsTo_u64 (f + 20) oldR8 ∗
      pointsTo_u32 (f + 28) oldR16 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (f - 32)) -∗
        pointsTo_u32 ((f - 32) + 0) bufPtr -∗
        pointsTo_u32 ((f - 32) + 4) bufCap -∗
        pointsTo_u64 ((f - 32) + 12) (packU32 bufPtr bufCap) -∗
        pointsTo_u64 ((f - 32) + 20) (packU32 0 0) -∗
        pointsTo_u32 ((f - 32) + 28) 0 -∗
        pointsTo_u64 (f + 12) (packU32 bufPtr bufCap) -∗
        pointsTo_u64 (f + 20) (packU32 0 0) -∗
        pointsTo_u32 (f + 28) 0 -∗
        WP (.running
          ⟨⟨[.i32 (32 + f)], [.i32 (f - 32), .i32 1, .i32 8192, .i32 0],
              [.i32 1, .i32 1, .i32 8192, .i32 (8 + (f - 32))]⟩,
            bufWriterAtAlloc, 0, [], [],
            { locals := ⟨[.i32 dst], [.i32 f, .i32 0], []⟩
              continuation := bufferedAfterWriterCtor
              resultArity := 0
              callerRemainder := []
              control := [] } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (12 + f)], [.i32 (f - 32), .i32 0], []⟩,
        bufReaderAfterAlloc, 0, [], [],
        { locals := ⟨[.i32 dst], [.i32 f, .i32 0], []⟩
          continuation := bufferedAfterReaderCtor
          resultArity := 0
          callerRemainder := []
          control := [] } :: calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, H0, H4, H12, H16, H20, H24, H28, HR0, HR8,
    HR16, Hcont⟩
  ihave HR0' : pointsTo_u64 ((12 + f) + 0) oldR0 $$ [HR0]
  · rw [show (12 + f) + 0 = f + 12 from by bv_decide]
    iexact HR0
  ihave HR8' : pointsTo_u64 ((12 + f) + 8) oldR8 $$ [HR8]
  · rw [show (12 + f) + 8 = f + 20 from by bv_decide]
    iexact HR8
  ihave HR16' : pointsTo_u32 ((12 + f) + 16) oldR16 $$ [HR16]
  · rw [show (12 + f) + 16 = f + 28 from by bv_decide]
    iexact HR16
  have Hepi := bufReader_after_alloc_twp (α := α)
    (12 + f) (f - 32) bufPtr bufCap old12 old16 old20 old24 old28
    oldR0 oldR8 oldR16 hctorFrameRoom hreaderDstRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := ⟨[.i32 dst], [.i32 f, .i32 0], []⟩
        continuation := bufferedAfterReaderCtor
        resultArity := 0
        callerRemainder := []
        control := [] } :: calls)
  iapply Hepi
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H0]
  · iexact H0
  isplitl [H4]
  · iexact H4
  isplitl [H12]
  · iexact H12
  isplitl [H16]
  · iexact H16
  isplitl [H20]
  · iexact H20
  isplitl [H24]
  · iexact H24
  isplitl [H28]
  · iexact H28
  isplitl [HR0']
  · iexact HR0'
  isplitl [HR8']
  · iexact HR8'
  isplitl [HR16']
  · iexact HR16'
  iintro Hglobal H0 H4 H12w H20w H28 HD0 HD8 HD16
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave Hglobal' : globalPointsTo 0 (.i32 f) $$ [Hglobal]
  · rw [show (32 : UInt32) + (f - 32) = f from by bv_decide]
    iexact Hglobal
  have Hbetween := buffered_between_ctors_twp (α := α)
    dst f (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hbetween
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  rw [bufferedAtWriterCtor_eq]
  have Hcall := bufWriterCtor_call_to_alloc_twp (α := α)
    (32 + f) f (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[.i32 dst], [.i32 f, .i32 0], []⟩)
    (stack := []) (code := bufferedAfterWriterCtor) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal']
  · iexact Hglobal'
  iintro Hruntime Hglobal
  ihave HD0' : pointsTo_u64 (f + 12) (packU32 bufPtr bufCap) $$ [HD0]
  · rw [show f + 12 = (12 + f) + 0 from by bv_decide]
    iexact HD0
  ihave HD8' : pointsTo_u64 (f + 20) (packU32 0 0) $$ [HD8]
  · rw [show f + 20 = (12 + f) + 8 from by bv_decide]
    iexact HD8
  ihave HD16' : pointsTo_u32 (f + 28) 0 $$ [HD16]
  · rw [show f + 28 = (12 + f) + 16 from by bv_decide]
    iexact HD16
  iapply Hcont $$ Hruntime Hglobal H0 H4 H12w H20w H28 HD0' HD8' HD16'

/-! Composed tail: resume right after the `BufWriter` buffer reservation
(absolute 142) returned, run the `BufWriter::new` epilogue, return to
`func135`, run the committed descriptor-copy epilogue, and return to the
original caller of absolute `.call 137`.  The continuation receives the
complete 36-byte buffered-I/O descriptor at `dst`: the `BufReader` triple
`(reader0, reader8, reader16)` at `dst + 0`/`dst + 8`/`dst + 16` and the
`BufWriter` pair at `dst + 20`/`dst + 28`, with the stack pointer restored
to `48 + f`. -/
set_option maxHeartbeats 4000000 in
theorem buffered_writerAlloc_to_return_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst f bufPtr bufCap : UInt32)
    (old20 old24 old28 : UInt32)
    (oldW0 oldW8 : UInt64)
    (reader0 reader8 : UInt64) (reader16 : UInt32)
    (oldDst0 oldDst8 oldDst20 oldDst28 : UInt64) (oldDst16 : UInt32)
    (hframeRoom : f.toNat + 48 ≤ UInt32.size)
    (hdstRoom : dst.toNat + 36 ≤ UInt32.size)
    (hctorFrameRoom : (f - 32).toNat + 32 ≤ UInt32.size)
    (hwriterDstRoom : (32 + f).toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 (f - 32)) ∗
      pointsTo_u32 ((f - 32) + 8) bufPtr ∗
      pointsTo_u32 ((f - 32) + 12) bufCap ∗
      pointsTo_u32 ((f - 32) + 20) old20 ∗
      pointsTo_u32 ((f - 32) + 24) old24 ∗
      pointsTo_u32 ((f - 32) + 28) old28 ∗
      pointsTo_u64 (f + 12) reader0 ∗
      pointsTo_u64 (f + 20) reader8 ∗
      pointsTo_u32 (f + 28) reader16 ∗
      pointsTo_u64 (f + 32) oldW0 ∗
      pointsTo_u64 (f + 40) oldW8 ∗
      pointsTo_u64 (dst + 0) oldDst0 ∗
      pointsTo_u64 (dst + 8) oldDst8 ∗
      pointsTo_u32 (dst + 16) oldDst16 ∗
      pointsTo_u64 (dst + 20) oldDst20 ∗
      pointsTo_u64 (dst + 28) oldDst28 ∗
      (globalPointsTo 0 (.i32 (48 + f)) -∗
        pointsTo_u32 ((f - 32) + 8) bufPtr -∗
        pointsTo_u32 ((f - 32) + 12) bufCap -∗
        pointsTo_u64 ((f - 32) + 20) (packU32 bufPtr bufCap) -∗
        pointsTo_u32 ((f - 32) + 28) 0 -∗
        pointsTo_u64 (f + 12) reader0 -∗
        pointsTo_u64 (f + 20) reader8 -∗
        pointsTo_u32 (f + 28) reader16 -∗
        pointsTo_u64 (f + 32) (packU32 bufPtr bufCap) -∗
        pointsTo_u64 (f + 40) (bufWriterTag oldW8) -∗
        pointsTo_u64 (dst + 0) reader0 -∗
        pointsTo_u64 (dst + 8) reader8 -∗
        pointsTo_u32 (dst + 16) reader16 -∗
        pointsTo_u64 (dst + 20) (packU32 bufPtr bufCap) -∗
        pointsTo_u64 (dst + 28) (bufWriterTag oldW8) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (32 + f)], [.i32 (f - 32), .i32 1, .i32 8192, .i32 0], []⟩,
        bufWriterAfterAlloc, 0, [], [],
        { locals := ⟨[.i32 dst], [.i32 f, .i32 0], []⟩
          continuation := bufferedAfterWriterCtor
          resultArity := 0
          callerRemainder := []
          control := [] } ::
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls } :: calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, H8, H12, H20, H24, H28, HR0, HR8, HR16, HW0, HW8,
    Hd0, Hd8, Hd16, Hd20, Hd28, Hcont⟩
  ihave HW0' : pointsTo_u64 ((32 + f) + 0) oldW0 $$ [HW0]
  · rw [show (32 + f) + 0 = f + 32 from by bv_decide]
    iexact HW0
  ihave HW8' : pointsTo_u64 ((32 + f) + 8) oldW8 $$ [HW8]
  · rw [show (32 + f) + 8 = f + 40 from by bv_decide]
    iexact HW8
  have Hepi := bufWriter_after_alloc_twp (α := α)
    (32 + f) (f - 32) bufPtr bufCap old20 old24 old28
    oldW0 oldW8 hctorFrameRoom hwriterDstRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := ⟨[.i32 dst], [.i32 f, .i32 0], []⟩
        continuation := bufferedAfterWriterCtor
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hepi
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H8]
  · iexact H8
  isplitl [H12]
  · iexact H12
  isplitl [H20]
  · iexact H20
  isplitl [H24]
  · iexact H24
  isplitl [H28]
  · iexact H28
  isplitl [HW0']
  · iexact HW0'
  isplitl [HW8']
  · iexact HW8'
  iintro Hglobal H8 H12 H20w H28 HW0 HW8
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave Hglobal' : globalPointsTo 0 (.i32 f) $$ [Hglobal]
  · rw [show (32 : UInt32) + (f - 32) = f from by bv_decide]
    iexact Hglobal
  ihave HW0f : pointsTo_u64 (f + 32) (packU32 bufPtr bufCap) $$ [HW0]
  · rw [show f + 32 = (32 + f) + 0 from by bv_decide]
    iexact HW0
  ihave HW8f : pointsTo_u64 (f + 40) (bufWriterTag oldW8) $$ [HW8]
  · rw [show f + 40 = (32 + f) + 8 from by bv_decide]
    iexact HW8
  have Hcopy := buffered_epilogue_twp (α := α)
    dst f reader0 reader8 (packU32 bufPtr bufCap) (bufWriterTag oldW8)
    reader16 oldDst0 oldDst8 oldDst20 oldDst28 oldDst16
    hframeRoom hdstRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hcopy
  isplitl [Hglobal']
  · iexact Hglobal'
  isplitl [HR0]
  · iexact HR0
  isplitl [HR8]
  · iexact HR8
  isplitl [HR16]
  · iexact HR16
  isplitl [HW0f]
  · iexact HW0f
  isplitl [HW8f]
  · iexact HW8f
  isplitl [Hd0]
  · iexact Hd0
  isplitl [Hd8]
  · iexact Hd8
  isplitl [Hd16]
  · iexact Hd16
  isplitl [Hd20]
  · iexact Hd20
  isplitl [Hd28]
  · iexact Hd28
  iintro Hglobal HR0 HR8 HR16 HW0 HW8 Hd0 Hd8 Hd16 Hd20 Hd28
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hcont $$ Hglobal H8 H12 H20w H28 HR0 HR8 HR16 HW0 HW8 Hd0 Hd8
    Hd16 Hd20 Hd28

end Project.Mergesort.BufferedCtorProof
