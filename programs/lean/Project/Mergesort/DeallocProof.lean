import Project.Mergesort.DropProof

/-!
# The shared dlmalloc deallocation routine on the driver's free pattern

`DropProof` stops every generated destructor chain at two seams: the shared
deallocation entry `.call 113` (local `func111`, reached from the `RawVec`
shims with `(self, 1, 1)` / `(self, 8, 8)` staged) and the sized forwarder
`.call 115` (local `func113`, reached directly by the `BufReader` buffer
release `func57`).  This file verifies the generated free path behind those
seams on the pattern the driver actually exercises: freeing a block that was
produced by the verified singleton small-bin allocation path of
`AllocatorProof`.

The generated call graph (local indices; call immediates are two larger
because of the two StdIO imports) is:

* `func111` (absolute 113) — `__rust_dealloc` wrapper: pushes a 16-byte
  frame, computes the layout triple `(data, align, byteSize)` through
  `func112` (absolute 114, a pure red-zone computation below the already
  moved stack pointer), and, when the computed alignment word is non-zero,
  forwards `(self + 8, data, align, byteSize)` to `func113`;
* `func113` (absolute 115) — returns immediately when the byte size is
  zero, otherwise forwards `(data, byteSize, align)` to `func129`;
* `func129` (absolute 131) — pure forwarder to `func164`;
* `func164` (absolute 166) — reads the chunk header at `data - 4` and
  traps unless `size + 4 ≤ (header &&& ~7) ≤ size + 39` for an in-use
  header, then calls the free core `func165`;
* `func165` (absolute 167) — the dlmalloc `free`.  For the blocks the
  driver frees the header has both low bits set (the singleton small-bin
  allocation wrote `chunkSize ||| 3`), the successor chunk is in use
  (header bit 1 set), and the chunk size is below 256, so the code takes
  exactly one path: clear the successor's previous-in-use bit, write the
  free chunk's boundary tags, and push the chunk onto its (empty) small
  bin, setting the bin's bitmap bit and making the chunk both head and
  tail of the doubly-linked bin list.

Every rule in this file is a composable total call rule in the style of
`DropProof`: it enters the generated function from an arbitrary caller and
returns to it, exposing the exact memory footprint of the executed path.
No path other than the one described is claimed: consolidation with free
neighbours, the designated victim, the top chunk, and the tree bins are
outside the driver's free pattern and remain unproven.
-/

set_option linter.unusedSimpArgs false

namespace Project.Mergesort.DeallocProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.FormatProof
open Project.Mergesort.RangeProof
open Project.Mergesort.DropProof
open Project.Mergesort.SplitAtProof

/-! ## Local function indices of the deallocation chain -/

theorem dealloc_index : «module».funcs[111]? = some func111Def := by rfl
theorem deallocLayout_index : «module».funcs[112]? = some func112Def := by rfl
theorem deallocSized_index : «module».funcs[113]? = some func113Def := by rfl
theorem freeForward_index : «module».funcs[129]? = some func129Def := by rfl
theorem freeCheck_index : «module».funcs[164]? = some func164Def := by rfl
theorem freeCore_index : «module».funcs[165]? = some func165Def := by rfl

/-! ## The path arithmetic of the free core

`func165` derives everything from the chunk header word it reads at
`data - 4`.  The definitions below name the exact expressions the generated
code computes so that the rules can be stated without re-deriving them. -/

/-- The chunk size stored in a dlmalloc header: the header with its two
low status bits (and the unused third bit) masked off. -/
def freeChunkSize (hdr : UInt32) : UInt32 := hdr &&& 4294967288

/-- The successor chunk address, exactly as the generated code computes it
(`psize + p`). -/
def freeNextChunk (chunk psize : UInt32) : UInt32 := psize + chunk

/-- The small-bin bitmap bit for a chunk size, exactly as the generated
code computes it (`1 <<< (psize >>> 3)`). -/
def freeBinBit (psize : UInt32) : UInt32 :=
  (1 : UInt32) <<< ((psize >>> ((3 : UInt32) % 32)) % 32)

/-- The small-bin sentinel node for a chunk size, exactly as the generated
code computes it (`1056344 + (psize &&& 248)`). -/
def freeBinSentinel (psize : UInt32) : UInt32 :=
  1056344 + (psize &&& 248)

/-- Allocator-owned state left behind by freeing a small chunk into its
empty small bin: the chunk carries a free header with boundary tag, its
link words point at the bin sentinel, the successor chunk lost its
previous-in-use bit and gained the previous-size field, the bin bitmap bit
is set, and the sentinel's head and tail links both point at the chunk. -/
def freeSmallChunkAt [WasmHeapGS] (chunk hdr nh map : UInt32) :
    IProp WasmHeapGF :=
  iprop% pointsTo_u32 (chunk + 4) (freeChunkSize hdr ||| 1) ∗
    pointsTo_u32 (chunk + 8) (freeBinSentinel (freeChunkSize hdr)) ∗
    pointsTo_u32 (chunk + 12) (freeBinSentinel (freeChunkSize hdr)) ∗
    pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr))
      (freeChunkSize hdr) ∗
    pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4)
      (nh &&& 4294967294) ∗
    pointsTo_u32 1056608 (map ||| freeBinBit (freeChunkSize hdr)) ∗
    pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) chunk ∗
    pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) chunk

private theorem pointsTo_u32_add_zero [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 base value ⊢ pointsTo_u32 (base + 0) value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u32_zero_add [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 (base + 0) value ⊢ pointsTo_u32 base value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u32_mul_one [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 base (value * 1) ⊢ pointsTo_u32 base value := by
  rw [show value * 1 = value from by bv_decide]

/-! ## The free core (`func165`, absolute 167) -/

set_option maxHeartbeats 4000000 in
/-- Composable total call rule for the dlmalloc free core at absolute
index 167, on the small-chunk path: the freed chunk's header has its
previous-in-use bit set, the successor chunk is in use, the chunk size is
below 256, and the chunk's small bin is empty.  The rule consumes the
chunk's header word, first two payload words, the successor chunk's
boundary words, the small-bin bitmap, and the bin sentinel's link words,
and returns them reassembled as `freeSmallChunkAt`. -/
theorem freeCore_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (chunk hdr nh oldPrevSize map oldHead oldPrev oldNext oldPrevLink :
      UInt32)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 (chunk + 8) :: stack⟩,
        .call 167 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hc40, hc41, hc42, hc43⟩ :=
    descriptorSlot32Facts chunk 4 16 hchunkRoom (by decide)
  obtain ⟨hc80, hc81, hc82, hc83⟩ :=
    descriptorSlot32Facts chunk 8 16 hchunkRoom (by decide)
  obtain ⟨hc120, hc121, hc122, hc123⟩ :=
    descriptorSlot32Facts chunk 12 16 hchunkRoom (by decide)
  obtain ⟨hn00, hn01, hn02, hn03⟩ :=
    descriptorSlot32Facts (freeNextChunk chunk (freeChunkSize hdr)) 0 8
      hnextRoom (by decide)
  obtain ⟨hn40, hn41, hn42, hn43⟩ :=
    descriptorSlot32Facts (freeNextChunk chunk (freeChunkSize hdr)) 4 8
      hnextRoom (by decide)
  obtain ⟨hm0, hm1, hm2, hm3⟩ :=
    descriptorSlot32Facts 0 1056608 1056612 (by decide) (by decide)
  obtain ⟨hs80, hs81, hs82, hs83⟩ :=
    descriptorSlot32Facts (freeBinSentinel (freeChunkSize hdr)) 8 16
      hsentRoom (by decide)
  obtain ⟨hs120, hs121, hs122, hs123⟩ :=
    descriptorSlot32Facts (freeBinSentinel (freeChunkSize hdr)) 12 16
      hsentRoom (by decide)
  have hhdrRoom : (chunk + 4).toNat + 4 ≤ UInt32.size := by
    have h0 : (chunk + (4 : UInt32)).toNat = chunk.toNat + 4 := hc40
    omega
  obtain ⟨hh0, hh1, hh2, hh3⟩ :=
    descriptorSlot32Facts (chunk + 4) 0 4 hhdrRoom (by decide)
  iintro ⟨Hruntime, Hheader, Hlink8, Hlink12, Hnext0, Hnext4, Hmap,
    Hsent8, Hsent12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 167 func165Def
      (by decide) freeCore_index $$ Hruntime
  iintro Hruntime
  simp [func165Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func165]
  -- Prologue: p := ptr - 8, hdr := [ptr - 4], psize := hdr &&& ~7,
  -- next := p + psize.
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (4294967288 : UInt32) + (chunk + 8) = chunk from by bv_decide]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (4294967292 : UInt32) + (chunk + 8) = chunk + 4 from by
    bv_decide]
  ihave HheaderAt : pointsTo_u32 ((chunk + 4) + 0) hdr $$ [Hheader]
  · iapply pointsTo_u32_add_zero
    iexact Hheader
  iapply twp_load32 hdr hh0 hh1 hh2 hh3 $$ HheaderAt
  iintro HheaderAt
  ihave Hheader : pointsTo_u32 (chunk + 4) hdr $$ [HheaderAt]
  · iapply pointsTo_u32_zero_add
    iexact HheaderAt
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show hdr &&& 4294967288 = freeChunkSize hdr from rfl]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_add
  rw [show freeChunkSize hdr + chunk =
    freeNextChunk chunk (freeChunkSize hdr) from rfl]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  -- Enter the two outer blocks; the previous chunk is in use, so the
  -- consolidation block is exited immediately.
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  iapply twp_brIf hhdr1 rfl
  simp only [List.take_zero, List.nil_append]
  -- Enter the eight-deep dispatch nest and read the successor header.
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_load32 nh hn40 hn41 hn42 hn43 $$ Hnext4
  iintro Hnext4
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  iapply twp_brIf hnh2 rfl
  simp only [List.take_zero, List.nil_append]
  -- The successor is in use: clear its previous-in-use bit and write the
  -- free chunk's boundary tags.
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  iapply twp_store32 nh hn40 hn41 hn42 hn43 $$ Hnext4
  iintro Hnext4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_or
  iapply twp_store32 hdr hc40 hc41 hc42 hc43 $$ Hheader
  iintro Hheader
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  rw [show freeChunkSize hdr + chunk =
    freeNextChunk chunk (freeChunkSize hdr) from rfl]
  iapply twp_localGet rfl
  ihave Hnext0At : pointsTo_u32
      (freeNextChunk chunk (freeChunkSize hdr) + 0) oldPrevSize $$ [Hnext0]
  · iapply pointsTo_u32_add_zero
    iexact Hnext0
  iapply twp_store32 oldPrevSize hn00 hn01 hn02 hn03 $$ Hnext0At
  iintro Hnext0At
  ihave Hnext0 : pointsTo_u32
      (freeNextChunk chunk (freeChunkSize hdr)) (freeChunkSize hdr) $$
      [Hnext0At]
  · iapply pointsTo_u32_zero_add
    iexact Hnext0At
  -- The enclosing dispatch block is exhausted; fall through to the size
  -- check and branch out to the small-bin insertion.
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := 1) (by simp [hsmall])
  iapply twp_brIf (by decide) rfl
  simp only [List.take_zero, List.nil_append]
  -- Small-bin insertion: the bin bit is clear, so set it and install the
  -- chunk as the single element of the bin.
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_const
  ihave HmapAt : pointsTo_u32 (0 + UInt32.ofNat 1056608) map $$ [Hmap]
  · rw [show (0 : UInt32) + UInt32.ofNat 1056608 = 1056608 by decide]
    iexact Hmap
  iapply twp_load32 map hm0 hm1 hm2 hm3 $$ HmapAt
  iintro HmapAt
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shrU
  iapply twp_shl
  rw [show (1 : UInt32) <<<
      ((freeChunkSize hdr >>> ((3 : UInt32) % 32)) % 32) =
    freeBinBit (freeChunkSize hdr) from rfl]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_and
  rw [hempty]
  iapply twp_brIfZero
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_or
  iapply twp_store32 map hm0 hm1 hm2 hm3 $$ HmapAt
  iintro HmapAt
  ihave Hmap : pointsTo_u32 1056608
      (map ||| freeBinBit (freeChunkSize hdr)) $$ [HmapAt]
  · rw [← show (0 : UInt32) + UInt32.ofNat 1056608 = 1056608 by decide]
    iexact HmapAt
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  iapply twp_const
  iapply twp_add
  rw [show (1056344 : UInt32) + (freeChunkSize hdr &&& 248) =
    freeBinSentinel (freeChunkSize hdr) from rfl]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  -- Link the chunk into the bin from both ends.
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldHead hs80 hs81 hs82 hs83 $$ Hsent8
  iintro Hsent8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldPrev hs120 hs121 hs122 hs123 $$ Hsent12
  iintro Hsent12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldPrevLink hc120 hc121 hc122 hc123 $$ Hlink12
  iintro Hlink12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldNext hc80 hc81 hc82 hc83 $$ Hlink8
  iintro Hlink8
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave Hstate : freeSmallChunkAt chunk hdr nh map $$
      [Hheader Hlink8 Hlink12 Hnext0 Hnext4 Hmap Hsent8 Hsent12]
  · isimp only [freeSmallChunkAt]
    iframe
  iapply Hdone $$ Hruntime Hstate

/-! ## The header sanity check (`func164`, absolute 166) -/

set_option maxHeartbeats 4000000 in
/-- Composable total call rule for the free sanity wrapper at absolute
index 166 on the small-chunk path.  The wrapper re-reads the chunk header
and traps unless `size + 4 ≤ chunkSize ≤ size + 39` for an in-use header;
the hypotheses `hfit`/`hbound` discharge exactly those generated checks,
after which the rule behaves like `freeCore_smallBin_call_twp`. -/
theorem freeCheck_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (chunk size align hdr nh oldPrevSize map oldHead oldPrev oldNext
      oldPrevLink : UInt32)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < size + 4)
    (hbound : ¬freeChunkSize hdr > 39 + size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 align :: .i32 size :: .i32 (chunk + 8) :: stack⟩,
        .call 166 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hhdr3 : hdr &&& 3 ≠ 0 := by
    intro h
    exact hhdr1 (by bv_decide)
  obtain ⟨hc40, hc41, hc42, hc43⟩ :=
    descriptorSlot32Facts chunk 4 16 hchunkRoom (by decide)
  have hhdrRoom : (chunk + 4).toNat + 4 ≤ UInt32.size := by
    have h0 : (chunk + (4 : UInt32)).toNat = chunk.toNat + 4 := hc40
    omega
  obtain ⟨hh0, hh1, hh2, hh3⟩ :=
    descriptorSlot32Facts (chunk + 4) 0 4 hhdrRoom (by decide)
  iintro ⟨Hruntime, Hheader, Hlink8, Hlink12, Hnext0, Hnext4, Hmap,
    Hsent8, Hsent12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 166 func164Def
      (by decide) freeCheck_index $$ Hruntime
  iintro Hruntime
  simp [func164Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func164]
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (4294967292 : UInt32) + (chunk + 8) = chunk + 4 from by
    bv_decide]
  ihave HheaderAt : pointsTo_u32 ((chunk + 4) + 0) hdr $$ [Hheader]
  · iapply pointsTo_u32_add_zero
    iexact Hheader
  iapply twp_load32 hdr hh0 hh1 hh2 hh3 $$ HheaderAt
  iintro HheaderAt
  ihave Hheader : pointsTo_u32 (chunk + 4) hdr $$ [HheaderAt]
  · iapply pointsTo_u32_zero_add
    iexact HheaderAt
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show hdr &&& 4294967288 = freeChunkSize hdr from rfl]
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 4) (by simp [hhdr3])
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_ltU (result := 0) (by simp [hfit])
  iapply twp_brIfZero
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [hhdr3])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_gtU (result := 0) (by simp [hbound])
  iapply twp_brIfZero
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply (freeCore_smallBin_call_twp (α := α)
    chunk hdr nh oldPrevSize map oldHead oldPrev oldNext oldPrevLink
    hhdr1 hnh2 hsmall hempty hchunkRoom hnextRoom hsentRoom
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hstate
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hstate

/-! ## The pure forwarder (`func129`, absolute 131) -/

set_option maxHeartbeats 4000000 in
/-- Composable total call rule for the free forwarder at absolute index
131 on the small-chunk path.  This is the boundary `func113` reaches when
the freed byte size is non-zero. -/
theorem freeForward_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (chunk size align hdr nh oldPrevSize map oldHead oldPrev oldNext
      oldPrevLink : UInt32)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < size + 4)
    (hbound : ¬freeChunkSize hdr > 39 + size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 align :: .i32 size :: .i32 (chunk + 8) :: stack⟩,
        .call 131 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hheader, Hlink8, Hlink12, Hnext0, Hnext4, Hmap,
    Hsent8, Hsent12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 131 func129Def
      (by decide) freeForward_index $$ Hruntime
  iintro Hruntime
  simp [func129Def, Function.toLocals, Function.numParams]
  simp only [func129]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply (freeCheck_smallBin_call_twp (α := α)
    chunk size align hdr nh oldPrevSize map oldHead oldPrev oldNext
    oldPrevLink hhdr1 hnh2 hsmall hempty hfit hbound hchunkRoom hnextRoom
    hsentRoom (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hstate
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hstate

/-! ## The sized deallocation entry (`func113`, absolute 115)

This is the exact boundary `DropProof` leaves the `BufReader` chain at,
and the target of `func111`'s interior call.  Its first parameter is an
allocator reference that the generated code never reads. -/

/-- Complete total call rule for the sized deallocation entry at absolute
index 115 when the byte size is zero: the call returns without touching
any state. -/
theorem deallocSized_zero_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (allocRef ptr align : UInt32)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 0 :: .i32 align :: .i32 ptr :: .i32 allocRef :: stack⟩,
        .call 115 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 115 func113Def
      (by decide) deallocSized_index $$ Hruntime
  iintro Hruntime
  simp [func113Def, Function.toLocals, Function.numParams]
  simp only [func113]
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_eqz (result := 1) (by simp)
  iapply twp_brIf (by decide) rfl
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime

set_option maxHeartbeats 4000000 in
/-- Composable total call rule for the sized deallocation entry at
absolute index 115 on the small-chunk path: a non-zero byte size forwards
to the free chain verified above. -/
theorem deallocSized_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (allocRef chunk size align hdr nh oldPrevSize map oldHead oldPrev
      oldNext oldPrevLink : UInt32)
    (hsize : size ≠ 0)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < size + 4)
    (hbound : ¬freeChunkSize hdr > 39 + size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 size :: .i32 align :: .i32 (chunk + 8) ::
            .i32 allocRef :: stack⟩,
        .call 115 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hheader, Hlink8, Hlink12, Hnext0, Hnext4, Hmap,
    Hsent8, Hsent12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 115 func113Def
      (by decide) deallocSized_index $$ Hruntime
  iintro Hruntime
  simp [func113Def, Function.toLocals, Function.numParams]
  simp only [func113]
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [hsize])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply (freeForward_smallBin_call_twp (α := α)
    chunk size align hdr nh oldPrevSize map oldHead oldPrev oldNext
    oldPrevLink hhdr1 hnh2 hsmall hempty hfit hbound hchunkRoom hnextRoom
    hsentRoom (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hstate
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hstate

/-! ## The layout computation (`func112`, absolute 114)

`func111` computes the freed layout triple `(data, align, byteSize)`
through this helper.  It does not move the stack pointer: it stages the
triple in the red zone sixteen bytes below the current stack pointer and
copies it into the caller-supplied result slot. -/

set_option maxHeartbeats 4000000 in
/-- Complete total call rule for the layout computation at absolute index
114 when the vector capacity is zero: only the result alignment word is
written, and it is written zero (which makes `func111` skip the free). -/
theorem deallocLayout_zero_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (out self align elemsize stackTop oldOut4 : UInt32)
    (he : elemsize ≠ 0)
    (hselfRoom : self.toNat + 8 ≤ UInt32.size)
    (houtRoom : out.toNat + 12 ≤ UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self 0 ∗
      pointsTo_u32 (out + 4) oldOut4 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self 0 -∗
        pointsTo_u32 (out + 4) 0 -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 elemsize :: .i32 align :: .i32 self :: .i32 out :: stack⟩,
        .call 114 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hself00, hself01, hself02, hself03⟩ :=
    descriptorSlot32Facts self 0 8 hselfRoom (by decide)
  obtain ⟨ho40, ho41, ho42, ho43⟩ :=
    descriptorSlot32Facts out 4 12 houtRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hself, Hout4, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 114 func112Def
      (by decide) deallocLayout_index $$ Hruntime
  iintro Hruntime
  simp [func112Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func112]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [he])
  iapply twp_brIfZero
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  ihave HselfAt : pointsTo_u32 (self + 0) 0 $$ [Hself]
  · iapply pointsTo_u32_add_zero
    iexact Hself
  iapply twp_load32 0 hself00 hself01 hself02 hself03 $$ HselfAt
  iintro HselfAt
  ihave Hself : pointsTo_u32 self 0 $$ [HselfAt]
  · iapply pointsTo_u32_zero_add
    iexact HselfAt
  iapply twp_brIfZero
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldOut4 ho40 ho41 ho42 ho43 $$ Hout4
  iintro Hout4
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hself Hout4

set_option maxHeartbeats 4000000 in
/-- Complete total call rule for the layout computation at absolute index
114 with a non-zero capacity: the result slot receives the data pointer,
the alignment, and the byte size `cap * elemsize`, staged through the red
zone sixteen bytes below the current stack pointer. -/
theorem deallocLayout_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (out self align elemsize cap dataPtr stackTop : UInt32)
    (r1 r2 r3 o0 o1 o2 : UInt32)
    (he : elemsize ≠ 0) (hcap : cap ≠ 0)
    (hselfRoom : self.toNat + 8 ≤ UInt32.size)
    (hredRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (houtRoom : out.toNat + 12 ≤ UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self cap ∗
      pointsTo_u32 (self + 4) dataPtr ∗
      pointsTo_u32 ((stackTop - 16) + 4) r1 ∗
      pointsTo_u32 ((stackTop - 16) + 8) r2 ∗
      pointsTo_u32 ((stackTop - 16) + 12) r3 ∗
      pointsTo_u32 out o0 ∗
      pointsTo_u32 (out + 4) o1 ∗
      pointsTo_u32 (out + 8) o2 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self cap -∗
        pointsTo_u32 (self + 4) dataPtr -∗
        pointsTo_u32 ((stackTop - 16) + 4) dataPtr -∗
        pointsTo_u32 ((stackTop - 16) + 8) align -∗
        pointsTo_u32 ((stackTop - 16) + 12) (cap * elemsize) -∗
        pointsTo_u32 out dataPtr -∗
        pointsTo_u32 (out + 4) align -∗
        pointsTo_u32 (out + 8) (cap * elemsize) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 elemsize :: .i32 align :: .i32 self :: .i32 out :: stack⟩,
        .call 114 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hself00, hself01, hself02, hself03⟩ :=
    descriptorSlot32Facts self 0 8 hselfRoom (by decide)
  obtain ⟨hself40, hself41, hself42, hself43⟩ :=
    descriptorSlot32Facts self 4 8 hselfRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts (stackTop - 16) 4 16 hredRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hredRoom (by decide)
  obtain ⟨hr120, hr121, hr122, hr123⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hredRoom (by decide)
  obtain ⟨hrw0, hrw1, hrw2, hrw3, hrw4, hrw5, hrw6, hrw7⟩ :=
    descriptorSlot64Facts (stackTop - 16) 4 16 hredRoom (by decide)
  obtain ⟨ho00, ho01, ho02, ho03⟩ :=
    descriptorSlot32Facts out 0 12 houtRoom (by decide)
  obtain ⟨ho40, ho41, ho42, ho43⟩ :=
    descriptorSlot32Facts out 4 12 houtRoom (by decide)
  obtain ⟨ho80, ho81, ho82, ho83⟩ :=
    descriptorSlot32Facts out 8 12 houtRoom (by decide)
  obtain ⟨how0, how1, how2, how3, how4, how5, how6, how7⟩ :=
    descriptorSlot64Facts out 0 12 houtRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hself0, Hself4, Hr4, Hr8, Hr12,
    Hout0, Hout4, Hout8, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 114 func112Def
      (by decide) deallocLayout_index $$ Hruntime
  iintro Hruntime
  simp [func112Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func112]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [he])
  iapply twp_brIfZero
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  ihave Hself0At : pointsTo_u32 (self + 0) cap $$ [Hself0]
  · iapply pointsTo_u32_add_zero
    iexact Hself0
  iapply twp_load32 cap hself00 hself01 hself02 hself03 $$ Hself0At
  iintro Hself0At
  iapply twp_brIf hcap rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 cap hself00 hself01 hself02 hself03 $$ Hself0At
  iintro Hself0At
  ihave Hself0 : pointsTo_u32 self cap $$ [Hself0At]
  · iapply pointsTo_u32_zero_add
    iexact Hself0At
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_mul
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 dataPtr hself40 hself41 hself42 hself43 $$ Hself4
  iintro Hself4
  iapply twp_store32 r1 hr40 hr41 hr42 hr43 $$ Hr4
  iintro Hr4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 r2 hr80 hr81 hr82 hr83 $$ Hr8
  iintro Hr8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 r3 hr120 hr121 hr122 hr123 $$ Hr12
  iintro Hr12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (cap * elemsize) hr120 hr121 hr122 hr123 $$ Hr12
  iintro Hr12
  iapply twp_store32 o2 ho80 ho81 ho82 ho83 $$ Hout8
  iintro Hout8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HredWord : pointsTo_u64 ((stackTop - 16) + 4)
      (packU32 dataPtr align) $$ [Hr4 Hr8]
  · iapply (sliceDescriptorAt_eq_u64 ((stackTop - 16) + 4)
      dataPtr align).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hr4]
    · iexact Hr4
    rw [show ((stackTop - 16) + 4) + 4 = (stackTop - 16) + 8 from by
      bv_decide]
    iexact Hr8
  iapply twp_load64 (packU32 dataPtr align)
    hrw0 hrw1 hrw2 hrw3 hrw4 hrw5 hrw6 hrw7 $$ HredWord
  iintro HredWord
  ihave HoutWord : pointsTo_u64 (out + 0) (packU32 o0 o1) $$ [Hout0 Hout4]
  · iapply (sliceDescriptorAt_eq_u64 (out + 0) o0 o1).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hout0]
    · iapply pointsTo_u32_add_zero
      iexact Hout0
    rw [show (out + 0) + 4 = out + 4 from by bv_decide]
    iexact Hout4
  iapply twp_store64 (packU32 o0 o1)
    how0 how1 how2 how3 how4 how5 how6 how7 $$ HoutWord
  iintro HoutWord
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave HredDesc : sliceDescriptorAt ((stackTop - 16) + 4) dataPtr align
      $$ [HredWord]
  · iapply (sliceDescriptorAt_eq_u64 ((stackTop - 16) + 4)
      dataPtr align).mpr
    iexact HredWord
  isimp only [sliceDescriptorAt] at HredDesc
  icases HredDesc with ⟨Hr4, Hr8'⟩
  ihave Hr8 : pointsTo_u32 ((stackTop - 16) + 8) align $$ [Hr8']
  · rw [show ((stackTop - 16) + 4) + 4 = (stackTop - 16) + 8 from by
      bv_decide]
    iexact Hr8'
  ihave HoutDesc : sliceDescriptorAt (out + 0) dataPtr align $$ [HoutWord]
  · iapply (sliceDescriptorAt_eq_u64 (out + 0) dataPtr align).mpr
    iexact HoutWord
  isimp only [sliceDescriptorAt] at HoutDesc
  icases HoutDesc with ⟨Hout0', Hout4'⟩
  ihave Hout0 : pointsTo_u32 out dataPtr $$ [Hout0']
  · iapply pointsTo_u32_zero_add
    iexact Hout0'
  ihave Hout4 : pointsTo_u32 (out + 4) align $$ [Hout4']
  · rw [show (out + 0) + 4 = out + 4 from by bv_decide]
    iexact Hout4'
  iapply Hdone $$ Hruntime Hglobal Hself0 Hself4 Hr4 Hr8 Hr12 Hout0
    Hout4 Hout8

/-! ## The shared deallocation entry (`func111`, absolute 113)

This is the exact boundary the `RawVec` shims of `DropProof` stop at,
with `(self, layout, layout)` staged.  The wrapper pushes a 16-byte
frame, computes the layout triple through absolute call 114, and frees
through absolute call 115 unless the computed alignment word is zero
(which happens exactly when the vector capacity is zero). -/

set_option maxHeartbeats 4000000 in
/-- Complete total call rule for the shared deallocation entry at
absolute index 113 when the vector capacity is zero: nothing is freed;
only the wrapper's frame slot at `stackTop - 8` is dirtied (with zero). -/
theorem dealloc_empty_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (self align elemsize stackTop oldFrame8 : UInt32)
    (he : elemsize ≠ 0)
    (hselfRoom : self.toNat + 8 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self 0 ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self 0 -∗
        pointsTo_u32 ((stackTop - 16) + 8) 0 -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 elemsize :: .i32 align :: .i32 self :: stack⟩,
        .call 113 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hself, Hframe8, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 113 func111Def
      (by decide) dealloc_index $$ Hruntime
  iintro Hruntime
  simp [func111Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func111]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (4 : UInt32) (stackTop - 16)]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hout4 : pointsTo_u32 (((stackTop - 16) + 4) + 4) oldFrame8 $$
      [Hframe8]
  · rw [show ((stackTop - 16) + 4) + 4 = (stackTop - 16) + 8 from by
      bv_decide]
    iexact Hframe8
  iapply (deallocLayout_zero_call_twp (α := α)
    ((stackTop - 16) + 4) self align elemsize (stackTop - 16) oldFrame8
    he hselfRoom
    (by
      have h0 : ((stackTop - 16) + (4 : UInt32)).toNat =
          (stackTop - 16).toNat + 4 :=
        (descriptorSlot32Facts (stackTop - 16) 4 16 hframeRoom
          (by decide)).1
      omega)
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself]
  · iexact Hself
  isplitl [Hout4]
  · iexact Hout4
  iintro Hruntime Hglobal Hself Hout4
  ihave Hframe8 : pointsTo_u32 ((stackTop - 16) + 8) 0 $$ [Hout4]
  · rw [← show ((stackTop - 16) + 4) + 4 = (stackTop - 16) + 8 from by
      bv_decide]
    iexact Hout4
  iapply twp_localGet rfl
  iapply twp_load32 0 hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 0) (by simp)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 from by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (by decide) rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (16 : UInt32) (stackTop - 16)]
  rw [show (stackTop - 16) + 16 = stackTop from by bv_decide]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hself Hframe8

set_option maxHeartbeats 8000000 in
/-- Complete total call rule for the shared deallocation entry at
absolute index 113 on the driver's free pattern: a non-empty vector whose
buffer is a small chunk (previous chunk in use, successor chunk in use,
chunk size below 256, small bin empty) is freed back into its small bin.
The wrapper's 16-byte frame and the 16-byte red zone below it are dirtied
with the layout triple `(chunk + 8, align, cap * elemsize)`. -/
theorem dealloc_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (self align elemsize cap chunk stackTop : UInt32)
    (hdr nh oldPrevSize map oldHead oldPrev oldNext oldPrevLink : UInt32)
    (r1 r2 r3 f4 f8 f12 : UInt32)
    (he : elemsize ≠ 0) (hcap : cap ≠ 0) (halign : align ≠ 0)
    (hbsize : cap * elemsize ≠ 0)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < cap * elemsize + 4)
    (hbound : ¬freeChunkSize hdr > 39 + cap * elemsize)
    (hselfRoom : self.toNat + 8 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hredRoom : (stackTop - 16 - 16).toNat + 16 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self cap ∗
      pointsTo_u32 (self + 4) (chunk + 8) ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 4) r1 ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 8) r2 ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 12) r3 ∗
      pointsTo_u32 ((stackTop - 16) + 4) f4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) f8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) f12 ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self cap -∗
        pointsTo_u32 (self + 4) (chunk + 8) -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 4) (chunk + 8) -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 8) align -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 12) (cap * elemsize) -∗
        pointsTo_u32 ((stackTop - 16) + 4) (chunk + 8) -∗
        pointsTo_u32 ((stackTop - 16) + 8) align -∗
        pointsTo_u32 ((stackTop - 16) + 12) (cap * elemsize) -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 elemsize :: .i32 align :: .i32 self :: stack⟩,
        .call 113 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts (stackTop - 16) 4 16 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hself0, Hself4, Hr4, Hr8, Hr12, Hf4, Hf8,
    Hf12, Hheader, Hlink8, Hlink12, Hnext0, Hnext4, Hmap, Hsent8, Hsent12,
    Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 113 func111Def
      (by decide) dealloc_index $$ Hruntime
  iintro Hruntime
  simp [func111Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func111]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (4 : UInt32) (stackTop - 16)]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hout4 : pointsTo_u32 (((stackTop - 16) + 4) + 4) f8 $$ [Hf8]
  · rw [show ((stackTop - 16) + 4) + 4 = (stackTop - 16) + 8 from by
      bv_decide]
    iexact Hf8
  ihave Hout8 : pointsTo_u32 (((stackTop - 16) + 4) + 8) f12 $$ [Hf12]
  · rw [show ((stackTop - 16) + 4) + 8 = (stackTop - 16) + 12 from by
      bv_decide]
    iexact Hf12
  iapply (deallocLayout_call_twp (α := α)
    ((stackTop - 16) + 4) self align elemsize cap (chunk + 8)
    (stackTop - 16) r1 r2 r3 f4 f8 f12 he hcap hselfRoom hredRoom
    (by
      have h0 : ((stackTop - 16) + (4 : UInt32)).toNat =
          (stackTop - 16).toNat + 4 := hf40
      omega)
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself0]
  · iexact Hself0
  isplitl [Hself4]
  · iexact Hself4
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  isplitl [Hr12]
  · iexact Hr12
  isplitl [Hf4]
  · iexact Hf4
  isplitl [Hout4]
  · iexact Hout4
  isplitl [Hout8]
  · iexact Hout8
  iintro Hruntime Hglobal Hself0 Hself4 Hr4 Hr8 Hr12 Hf4 Hout4 Hout8
  ihave Hf8 : pointsTo_u32 ((stackTop - 16) + 8) align $$ [Hout4]
  · rw [← show ((stackTop - 16) + 4) + 4 = (stackTop - 16) + 8 from by
      bv_decide]
    iexact Hout4
  ihave Hf12 : pointsTo_u32 ((stackTop - 16) + 12) (cap * elemsize) $$
      [Hout8]
  · rw [← show ((stackTop - 16) + 4) + 8 = (stackTop - 16) + 12 from by
      bv_decide]
    iexact Hout8
  iapply twp_localGet rfl
  iapply twp_load32 align hf80 hf81 hf82 hf83 $$ Hf8
  iintro Hf8
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_block
  iapply twp_block
  isimp
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 1) (by simp [halign])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 from by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_load32 (chunk + 8) hf40 hf41 hf42 hf43 $$ Hf4
  iintro Hf4
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_load32 align hf80 hf81 hf82 hf83 $$ Hf8
  iintro Hf8
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_load32 (cap * elemsize) hf120 hf121 hf122 hf123 $$ Hf12
  iintro Hf12
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply (deallocSized_smallBin_call_twp (α := α)
    (8 + self) chunk (cap * elemsize) align hdr nh oldPrevSize map
    oldHead oldPrev oldNext oldPrevLink hbsize hhdr1 hnh2 hsmall hempty
    hfit hbound hchunkRoom hnextRoom hsentRoom
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hstate
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (16 : UInt32) (stackTop - 16)]
  rw [show (stackTop - 16) + 16 = stackTop from by bv_decide]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hself0 Hself4 Hr4 Hr8 Hr12 Hf4 Hf8
    Hf12 Hstate

/-! ## Closed destructor contracts

With the deallocation chain proven, the `DropProof` seams can be closed:
the destructor contracts below run a complete generated `Drop`
implementation from call to return on the driver's free pattern. -/

set_option maxHeartbeats 8000000 in
/-- Complete total call rule for `Vec<u64>::drop` at absolute index 70 on
the driver's free pattern: the element loop counts the red-zone scratch
word up to the length, and the backing buffer (a small singleton chunk)
is freed into its small bin.  The vector descriptor itself is read but
preserved. -/
theorem dropVecU64_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (self cap len chunk stackTop : UInt32)
    (hdr nh oldPrevSize map oldHead oldPrev oldNext oldPrevLink : UInt32)
    (r1 r2 r3 f4 f8 oldScratch : UInt32)
    (hcap : cap ≠ 0)
    (hbsize : cap * 8 ≠ 0)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < cap * 8 + 4)
    (hbound : ¬freeChunkSize hdr > 39 + cap * 8)
    (hselfRoom : self.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hredRoom : (stackTop - 16 - 16).toNat + 16 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self cap ∗
      pointsTo_u32 (self + 4) (chunk + 8) ∗
      pointsTo_u32 (self + 8) len ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 4) r1 ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 8) r2 ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 12) r3 ∗
      pointsTo_u32 ((stackTop - 16) + 4) f4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) f8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self cap -∗
        pointsTo_u32 (self + 4) (chunk + 8) -∗
        pointsTo_u32 (self + 8) len -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 4) (chunk + 8) -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 8) 8 -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 12) (cap * 8) -∗
        pointsTo_u32 ((stackTop - 16) + 4) (chunk + 8) -∗
        pointsTo_u32 ((stackTop - 16) + 8) 8 -∗
        pointsTo_u32 ((stackTop - 16) + 12) (cap * 8) -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 self :: stack⟩,
        .call 70 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hself0, Hself4, Hself8, Hr4, Hr8, Hr12, Hf4,
    Hf8, Hscratch, Hheader, Hlink8, Hlink12, Hnext0, Hnext4, Hmap, Hsent8,
    Hsent12, Hdone⟩
  have Hdrop := dropVecU64_call_twp (α := α) self
    (callerLocals := ⟨params, localValues, []⟩) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hdrop
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropVecU64Seam]
  have Hloop := dropElementsU64_call_twp (α := α)
    self stackTop (chunk + 8) len oldScratch
    (by omega) hframeRoom
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.localGet 0, .call 16, .ret]) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hloop
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself4]
  · iexact Hself4
  isplitl [Hself8]
  · iexact Hself8
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hruntime Hglobal Hself4 Hself8 Hscratch
  iapply twp_localGet rfl
  have Hbuffer := dropVecBuffer_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hbuffer
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropVecBufferSeam]
  have Hshim := rawVecDeallocU64_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨[.i32 self], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hshim
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [rawVecDeallocSeam]
  iapply (dealloc_smallBin_call_twp (α := α)
    self 8 8 cap chunk stackTop hdr nh oldPrevSize map oldHead oldPrev
    oldNext oldPrevLink r1 r2 r3 f4 f8 len
    (by decide) hcap (by decide) hbsize hhdr1 hnh2 hsmall hempty hfit
    hbound (by omega) hframeRoom hredRoom hchunkRoom hnextRoom hsentRoom
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself0]
  · iexact Hself0
  isplitl [Hself4]
  · iexact Hself4
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  isplitl [Hr12]
  · iexact Hr12
  isplitl [Hf4]
  · iexact Hf4
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hscratch]
  · iexact Hscratch
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hglobal Hself0 Hself4 Hr4 Hr8 Hr12 Hf4 Hf8 Hf12 Hstate
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hself0 Hself4 Hself8 Hr4 Hr8 Hr12 Hf4
    Hf8 Hf12 Hstate

set_option maxHeartbeats 8000000 in
/-- Complete total call rule for `Vec<u64>::drop` at absolute index 70
when the vector capacity is zero (the `n = 0` driver input): the element
loop still counts the scratch word up to the length, but nothing is
freed; only the wrapper frame slot at `stackTop - 8` is dirtied. -/
theorem dropVecU64_empty_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (self data len stackTop oldFrame8 oldScratch : UInt32)
    (hselfRoom : self.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self 0 ∗
      pointsTo_u32 (self + 4) data ∗
      pointsTo_u32 (self + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self 0 -∗
        pointsTo_u32 (self + 4) data -∗
        pointsTo_u32 (self + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 8) 0 -∗
        pointsTo_u32 ((stackTop - 16) + 12) len -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 self :: stack⟩,
        .call 70 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hself0, Hself4, Hself8, Hframe8, Hscratch,
    Hdone⟩
  have Hdrop := dropVecU64_call_twp (α := α) self
    (callerLocals := ⟨params, localValues, []⟩) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hdrop
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropVecU64Seam]
  have Hloop := dropElementsU64_call_twp (α := α)
    self stackTop data len oldScratch (by omega) hframeRoom
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.localGet 0, .call 16, .ret]) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hloop
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself4]
  · iexact Hself4
  isplitl [Hself8]
  · iexact Hself8
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hruntime Hglobal Hself4 Hself8 Hscratch
  iapply twp_localGet rfl
  have Hbuffer := dropVecBuffer_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hbuffer
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropVecBufferSeam]
  have Hshim := rawVecDeallocU64_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨[.i32 self], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hshim
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [rawVecDeallocSeam]
  iapply (dealloc_empty_call_twp (α := α)
    self 8 8 stackTop oldFrame8 (by decide) (by omega) hframeRoom
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself0]
  · iexact Hself0
  isplitl [Hframe8]
  · iexact Hframe8
  iintro Hruntime Hglobal Hself0 Hframe8
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hself0 Hself4 Hself8 Hframe8 Hscratch

set_option maxHeartbeats 8000000 in
/-- Complete total call rule for `String::drop` at absolute index 64 on
the driver's free pattern: the shared `String`/`Vec<u8>` field destructor
runs the element loop and frees the byte buffer (a small singleton chunk)
into its small bin.  The string descriptor itself is read but
preserved. -/
theorem dropString_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (self cap len chunk stackTop : UInt32)
    (hdr nh oldPrevSize map oldHead oldPrev oldNext oldPrevLink : UInt32)
    (r1 r2 r3 f4 f8 oldScratch : UInt32)
    (hcap : cap ≠ 0)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < cap + 4)
    (hbound : ¬freeChunkSize hdr > 39 + cap)
    (hselfRoom : self.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hredRoom : (stackTop - 16 - 16).toNat + 16 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self cap ∗
      pointsTo_u32 (self + 4) (chunk + 8) ∗
      pointsTo_u32 (self + 8) len ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 4) r1 ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 8) r2 ∗
      pointsTo_u32 ((stackTop - 16 - 16) + 12) r3 ∗
      pointsTo_u32 ((stackTop - 16) + 4) f4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) f8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self cap -∗
        pointsTo_u32 (self + 4) (chunk + 8) -∗
        pointsTo_u32 (self + 8) len -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 4) (chunk + 8) -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 8) 1 -∗
        pointsTo_u32 ((stackTop - 16 - 16) + 12) cap -∗
        pointsTo_u32 ((stackTop - 16) + 4) (chunk + 8) -∗
        pointsTo_u32 ((stackTop - 16) + 8) 1 -∗
        pointsTo_u32 ((stackTop - 16) + 12) cap -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 self :: stack⟩,
        .call 64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hc1 : cap * 1 = cap := by bv_decide
  iintro ⟨Hruntime, Hglobal, Hself0, Hself4, Hself8, Hr4, Hr8, Hr12, Hf4,
    Hf8, Hscratch, Hheader, Hlink8, Hlink12, Hnext0, Hnext4, Hmap, Hsent8,
    Hsent12, Hdone⟩
  have Hdrop := dropString_call_twp (α := α) self
    (callerLocals := ⟨params, localValues, []⟩) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hdrop
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropStringSeam]
  have Hfields := dropStringFields_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hfields
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropStringFieldsSeam]
  have Hloop := dropElementsU8_call_twp (α := α)
    self stackTop (chunk + 8) len oldScratch
    (by omega) hframeRoom
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.localGet 0, .call 69, .ret]) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨[.i32 self], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hloop
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself4]
  · iexact Hself4
  isplitl [Hself8]
  · iexact Hself8
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hruntime Hglobal Hself4 Hself8 Hscratch
  iapply twp_localGet rfl
  have Hbuffer := dropStringBuffer_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨[.i32 self], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hbuffer
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropStringBufferSeam]
  have Hshim := rawVecDeallocU8_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨[.i32 self], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := ⟨[.i32 self], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hshim
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [rawVecDeallocSeam]
  iapply (dealloc_smallBin_call_twp (α := α)
    self 1 1 cap chunk stackTop hdr nh oldPrevSize map oldHead oldPrev
    oldNext oldPrevLink r1 r2 r3 f4 f8 len
    (by decide) hcap (by decide) (by simpa [hc1] using hcap) hhdr1 hnh2
    hsmall hempty (by simpa [hc1] using hfit) (by simpa [hc1] using hbound)
    (by omega) hframeRoom hredRoom hchunkRoom hnextRoom hsentRoom
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself0]
  · iexact Hself0
  isplitl [Hself4]
  · iexact Hself4
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  isplitl [Hr12]
  · iexact Hr12
  isplitl [Hf4]
  · iexact Hf4
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hscratch]
  · iexact Hscratch
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hglobal Hself0 Hself4 Hr4 Hr8 Hr12 Hf4 Hf8 Hf12 Hstate
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave Hr12' : pointsTo_u32 ((stackTop - 16 - 16) + 12) cap $$ [Hr12]
  · iapply pointsTo_u32_mul_one
    iexact Hr12
  ihave Hf12' : pointsTo_u32 ((stackTop - 16) + 12) cap $$ [Hf12]
  · iapply pointsTo_u32_mul_one
    iexact Hf12
  iapply Hdone $$ Hruntime Hglobal Hself0 Hself4 Hself8 Hr4 Hr8 Hr12' Hf4
    Hf8 Hf12' Hstate

/-! ## The `BufReader` buffer release (`func57`, absolute 59)

`func57` is the function behind the `.call 59` seam of
`DropProof.dropBufReaderBuffer_call_twp`: it stages the buffer layout in
its own 16-byte frame and forwards `(self + 8, data, 1, len)` to the
sized deallocation entry.  The rules below cover it on the small-chunk
pattern; note that the driver's default `BufReader` buffer is 8192 bytes,
whose free takes the (unproven) tree-bin path, so the closed contract
applies only to sub-256-byte buffers. -/

set_option maxHeartbeats 8000000 in
/-- Complete total call rule for the `BufReader` buffer release at
absolute index 59 when the buffer is a small chunk. -/
theorem bufReaderRelease_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (self len chunk stackTop : UInt32)
    (hdr nh oldPrevSize map oldHead oldPrev oldNext oldPrevLink : UInt32)
    (f8 f12 : UInt32)
    (hlen : len ≠ 0)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < len + 4)
    (hbound : ¬freeChunkSize hdr > 39 + len)
    (hselfRoom : self.toNat + 8 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self (chunk + 8) ∗
      pointsTo_u32 (self + 4) len ∗
      pointsTo_u32 ((stackTop - 16) + 8) f8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) f12 ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self (chunk + 8) -∗
        pointsTo_u32 (self + 4) len -∗
        pointsTo_u32 ((stackTop - 16) + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) 1 -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 self :: stack⟩,
        .call 59 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hself00, hself01, hself02, hself03⟩ :=
    descriptorSlot32Facts self 0 8 hselfRoom (by decide)
  obtain ⟨hself40, hself41, hself42, hself43⟩ :=
    descriptorSlot32Facts self 4 8 hselfRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hself0, Hself4, Hf8, Hf12, Hheader, Hlink8,
    Hlink12, Hnext0, Hnext4, Hmap, Hsent8, Hsent12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 59 func57Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func57Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func57]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  ihave Hself0At : pointsTo_u32 (self + 0) (chunk + 8) $$ [Hself0]
  · iapply pointsTo_u32_add_zero
    iexact Hself0
  iapply twp_load32 (chunk + 8) hself00 hself01 hself02 hself03 $$
    Hself0At
  iintro Hself0At
  ihave Hself0 : pointsTo_u32 self (chunk + 8) $$ [Hself0At]
  · iapply pointsTo_u32_zero_add
    iexact Hself0At
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 len hself40 hself41 hself42 hself43 $$ Hself4
  iintro Hself4
  iapply twp_const
  iapply twp_shl
  rw [show len <<< ((0 : UInt32) % 32) = len from by bv_decide]
  iapply twp_store32 f8 hf80 hf81 hf82 hf83 $$ Hf8
  iintro Hf8
  iapply twp_localGet rfl
  iapply twp_load32 len hf80 hf81 hf82 hf83 $$ Hf8
  iintro Hf8
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 f12 hf120 hf121 hf122 hf123 $$ Hf12
  iintro Hf12
  iapply twp_localGet rfl
  iapply twp_load32 1 hf120 hf121 hf122 hf123 $$ Hf12
  iintro Hf12
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_block
  isimp
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [hlen])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply (deallocSized_smallBin_call_twp (α := α)
    (8 + self) chunk len 1 hdr nh oldPrevSize map oldHead oldPrev oldNext
    oldPrevLink hlen hhdr1 hnh2 hsmall hempty hfit hbound hchunkRoom
    hnextRoom hsentRoom (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hstate
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (16 : UInt32) (stackTop - 16)]
  rw [show (stackTop - 16) + 16 = stackTop from by bv_decide]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hself0 Hself4 Hf8 Hf12 Hstate

set_option maxHeartbeats 8000000 in
/-- Complete total call rule for `BufReader::drop` at absolute index 80
when the internal read buffer is a small chunk (the driver's default 8192
byte buffer instead takes the unproven tree-bin free path). -/
theorem dropBufReader_smallBin_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (self len chunk stackTop : UInt32)
    (hdr nh oldPrevSize map oldHead oldPrev oldNext oldPrevLink : UInt32)
    (f8 f12 : UInt32)
    (hlen : len ≠ 0)
    (hhdr1 : hdr &&& 1 ≠ 0)
    (hnh2 : nh &&& 2 ≠ 0)
    (hsmall : freeChunkSize hdr < 256)
    (hempty : map &&& freeBinBit (freeChunkSize hdr) = 0)
    (hfit : ¬freeChunkSize hdr < len + 4)
    (hbound : ¬freeChunkSize hdr > 39 + len)
    (hselfRoom : self.toNat + 8 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 16 ≤ UInt32.size)
    (hnextRoom : (freeNextChunk chunk (freeChunkSize hdr)).toNat + 8 ≤
      UInt32.size)
    (hsentRoom : (freeBinSentinel (freeChunkSize hdr)).toNat + 16 ≤
      UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 self (chunk + 8) ∗
      pointsTo_u32 (self + 4) len ∗
      pointsTo_u32 ((stackTop - 16) + 8) f8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) f12 ∗
      pointsTo_u32 (chunk + 4) hdr ∗
      pointsTo_u32 (chunk + 8) oldNext ∗
      pointsTo_u32 (chunk + 12) oldPrevLink ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr)) oldPrevSize ∗
      pointsTo_u32 (freeNextChunk chunk (freeChunkSize hdr) + 4) nh ∗
      pointsTo_u32 1056608 map ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 8) oldHead ∗
      pointsTo_u32 (freeBinSentinel (freeChunkSize hdr) + 12) oldPrev ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 self (chunk + 8) -∗
        pointsTo_u32 (self + 4) len -∗
        pointsTo_u32 ((stackTop - 16) + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) 1 -∗
        freeSmallChunkAt chunk hdr nh map -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 self :: stack⟩,
        .call 80 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hself0, Hself4, Hf8, Hf12, Hheader, Hlink8,
    Hlink12, Hnext0, Hnext4, Hmap, Hsent8, Hsent12, Hdone⟩
  have Hdrop := dropBufReader_call_twp (α := α) self
    (callerLocals := ⟨params, localValues, []⟩) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hdrop
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropBufReaderSeam]
  have Hinner := dropBufReaderInner_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hinner
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropBufReaderInnerSeam]
  have Hbuffer := dropBufReaderBuffer_call_twp (α := α) self
    (callerLocals := ⟨[.i32 self], [], []⟩) (stack := [])
    (code := [.ret]) (arity := 0) (remainder := []) (controls := [])
    (calls :=
      { locals := ⟨[.i32 self], [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } ::
      { locals := ⟨params, localValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  iapply Hbuffer
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [dropBufReaderBufferSeam]
  iapply (bufReaderRelease_smallBin_call_twp (α := α)
    self len chunk stackTop hdr nh oldPrevSize map oldHead oldPrev
    oldNext oldPrevLink f8 f12 hlen hhdr1 hnh2 hsmall hempty hfit hbound
    hselfRoom hframeRoom hchunkRoom hnextRoom hsentRoom
    (s := s) (E := E) (Φ := Φ))
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hself0]
  · iexact Hself0
  isplitl [Hself4]
  · iexact Hself4
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hf12]
  · iexact Hf12
  isplitl [Hheader]
  · iexact Hheader
  isplitl [Hlink8]
  · iexact Hlink8
  isplitl [Hlink12]
  · iexact Hlink12
  isplitl [Hnext0]
  · iexact Hnext0
  isplitl [Hnext4]
  · iexact Hnext4
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hsent8]
  · iexact Hsent8
  isplitl [Hsent12]
  · iexact Hsent12
  iintro Hruntime Hglobal Hself0 Hself4 Hf8 Hf12 Hstate
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hself0 Hself4 Hf8 Hf12 Hstate

end Project.Mergesort.DeallocProof
