import Project.RustHashMap.DecoderPairLoop

/-!
# The decode stage of the decoder

`decodeStage` is `allocPair` and then the pair loop.  The stage runs with
the header already read, so local 5 holds `len - 4`, local 6 holds
`ptr + 4`, and local 7 holds the declared pair count.

The proof has two steps.  `twp_alloc_pair` asks the allocator for
`min(count, 512)` pairs and writes the three vector words of the frame.
`twp_pair_loop` then runs the loop from index zero.  The out-of-memory arm
of the allocation goes straight to the third arm of `LoopCont`.

The stage takes a `LoopCont` and gives it to the loop unchanged, so all
three exits of the loop stay open for the caller.

## The capacity of the first allocation fits the heap

`CapacityFits` asks for `heapBase + 16 * capacity <= frontier + 4096`.
The allocation gives `frontier <= base` and
`finish = base + 8 * capacity`, and `pairCapacity` is 512 or less.  The
new frontier is `finish`, so `16 * capacity` is `8 * capacity` more than
the `8 * capacity` that the allocation already took, and `8 * 512` is
4096.  The margin is therefore exact.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

/-- Read the lower bound of the frontier without giving the heap up. -/
private theorem BumpHeap_reachable
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) :
    BumpHeap heapId storedCursor frontier history ⊢
      iprop(BumpHeap heapId storedCursor frontier history ∗
        ⌜heapBase.toNat ≤ frontier⌝) := by
  iintro Hbump
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
  isplitl [Hcursor Hfrontier Hauth Hretired Hpages]
  · unfold BumpHeap
    iframe Hcursor Hfrontier Hauth Hretired
    iexists ownedPages
    iframe_pureexact using [Hpages] => hheap
  · ipureexact hheap.1

/-- The layout that the allocation asks for is the layout that the loop
holds. -/
theorem pairLayout_block (count : UInt32) :
    pairLayout count = pairBlock (pairCapacity count).toNat := rfl

/-- The first allocation leaves room for one grow. -/
theorem pairCapacity_fits (count : UInt32) {frontier : Nat}
    {base finish : UInt32}
    (hcount : count ≠ 0)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hclassify :
      classifyBump frontier (pairLayout count) = .success base finish) :
    CapacityFits (pairCapacity count) finish.toNat := by
  have hreach := classifyBump_success_reachable frontier (pairLayout count)
    base finish hfrontier (pairLayout_valid count hcount) (Or.inr rfl)
    hclassify
  have hbase : frontier ≤ base.toNat := hreach.1
  have hfinish : finish.toNat = base.toNat + (pairLayout count).size :=
    hreach.2.2.2.2.2.1
  have hsize : (pairLayout count).size = 8 * (pairCapacity count).toNat :=
    rfl
  have hle := pairCapacity_le count
  unfold CapacityFits
  omega

set_option maxHeartbeats 2000000 in
/-- The decode stage allocates the pair buffer and runs the pair loop. -/
theorem twp_decode_stage [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore pad scratch dataBytes below : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (word4 word8 word12 aux10 aux11 aux12 : UInt32)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (l3 l4 l8 l9 : Value)
    (arity : Nat) (remainder : List Value)
    (decodeFrame : ControlFrame)
    (errorBody errorCont : Program) (errorBelow : List Value)
    (errorControls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hcount : count ≠ 0)
    (hlen : bytes.length = len.toNat)
    (hfour : 4 ≤ bytes.length)
    (hscratchLength : scratch.length = 48)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hptrNowrap : ptr.toNat + bytes.length < UInt32.size) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame (decoderDepth - 64) below ∗
      Slices.ByteSlice 0 frame pad ∗
      pointsTo_u32 0 (frame + 4) word4 ∗
      pointsTo_u32 0 (frame + 8) word8 ∗
      pointsTo_u32 0 (frame + 12) word12 ∗
      Slices.ByteSlice 0 (frame + 16) scratch ∗
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 hdr (ptr + 4) ∗
      pointsTo_u32 0 (hdr + 4) (len - 4) ∗
      Slices.ByteSlice 0 ptr bytes ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      LoopCont out hdr ptr len frame count heapId bytes outBefore pad scratch
        dataBytes input output raised arity remainder
        (decodeFrame :: allocFrame errorBody errorCont errorBelow ::
          errorControls)
        errorControls errorCont errorBelow calls s E Φ) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, .i32 (len - 4), .i32 (ptr + 4),
                .i32 count, l8, l9, .i32 aux10, .i32 aux11, .i32 aux12], []⟩,
            decodeStage, arity, remainder,
            decodeFrame :: allocFrame errorBody errorCont errorBelow ::
              errorControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hpad, Hcapacity, Hbuffer, Hlength, Hscratch,
    Hout, Hhdr, Hlen, Hinput, Hdata, Hbump, Hstreams, Hcont⟩
  ihave ⟨Hbump, %hfrontier⟩ := BumpHeap_reachable heapId storedCursor
    frontier history $$ Hbump
  simp only [decodeStage]
  iapply twp_alloc_pair out hdr frame count word4 word8 word12 heapId
    storedCursor frontier history input output raised l3 l4
    (.i32 (len - 4)) (.i32 (ptr + 4)) l8 l9 (.i32 aux10) (.i32 aux11)
    (.i32 aux12) hcount hframeNowrap
  isplitl_exacts [Hruntime Hcapacity Hbuffer Hlength Hbump Hstreams]
  isimp only [LoopCont] at Hcont
  isplit
  · -- the allocator gave the buffer, so the loop starts at index zero
    iintro %base %finish %allocBytes Hruntime Hbump Hblock Hstreams
      Hcapacity Hbuffer Hlength %halloc
    obtain ⟨hclassify, _⟩ := halloc
    isimp only [pairLayout_block] at Hblock
    have hfits : CapacityFits (pairCapacity count) finish.toNat :=
      pairCapacity_fits count hcount hfrontier hclassify
    have hcountPos : 0 < count.toNat := by
      rcases Nat.eq_zero_or_pos count.toNat with h | h
      · exact absurd (UInt32.toNat_inj.mp (by simpa using h)) hcount
      · exact h
    have hcapDisj : count.toNat ≤ (pairCapacity count).toNat ∨
        2 ≤ (pairCapacity count).toNat := by
      unfold pairCapacity
      by_cases hlt : count < 512
      · exact Or.inl (by rw [if_pos hlt])
      · exact Or.inr (by rw [if_neg hlt]; decide)
    have hlocals :
        (⟨[.i32 out, .i32 hdr],
            [.i32 frame, .i32 0, .i32 (frame + 52), .i32 (len - 4),
              .i32 (ptr + 4), .i32 count, .i32 base, .i32 4, .i32 aux10,
              .i32 aux11, .i32 aux12], []⟩ : Locals)
          = loopLocals out hdr frame ptr len count
            { index := 0, capacity := pairCapacity count, buffer := base,
              allocationId := history.nextId, blockBytes := allocBytes,
              below := below, storedCursor := finish,
              frontier := finish.toNat,
              history := history.allocate base (pairLayout count),
              aux10 := aux10, aux11 := aux11, aux12 := aux12 } := rfl
    rw [hlocals]
    iapply twp_pair_loop out hdr ptr len frame count heapId bytes outBefore
      pad scratch dataBytes input output raised arity remainder decodeFrame
      errorBody errorCont errorBelow errorControls calls s E Φ hlen
      hscratchLength hdataLength hframeLow hframeNowrap hhdrNowrap hptrNowrap
      { index := 0, capacity := pairCapacity count, buffer := base,
        allocationId := history.nextId, blockBytes := allocBytes,
        below := below, storedCursor := finish, frontier := finish.toNat,
        history := history.allocate base (pairLayout count),
        aux10 := aux10, aux11 := aux11, aux12 := aux12 }
    isimp only [LoopInv, LoopCont]
    isplitl_exacts [Hruntime Hsp Hbelow Hpad Hcapacity Hbuffer Hlength
      Hscratch Hout Hhdr Hlen Hinput Hdata Hblock Hbump Hstreams]
    isplitl_pureexact ⟨hcountPos, Nat.zero_le _, hcapDisj, by omega,
      by simp [payload], hfits⟩
    iexact Hcont
  · -- the allocator failed, which is the third arm of the loop
    iintro %remaining Hstreams
    ihave Htail := BI.and_elim_r $$ Hcont
    ihave Hoom := BI.and_elim_r $$ Htail
    iapply Hoom $$ %remaining Hstreams

end Project.RustHashMap.Decoder
