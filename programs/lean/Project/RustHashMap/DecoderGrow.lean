import Project.RustHashMap.DecoderLoop
import Project.RustHashMap.DecoderAppend
import Project.RustHashMap.Func23Proof

/-!
# The borsh decoder: the amortized grow of the pair buffer

One loop step ends with `Project.RustHashMap.Decoder.growBody`, WAT lines
764 to 775.  The fragment tests the length word against the capacity word.
A buffer that is not full takes the branch out of the block and changes
nothing.  A full buffer calls absolute `func 26`, which doubles the
capacity, and the fragment then reads the new pointer into local 8.

The lemma hides the branch.  Both paths give the caller one live block of
`newCapacity` pairs at `newBuffer`, with the bytes of the old block as a
prefix, and the fact `written < newCapacity`.  The caller therefore has
room for the pair that the append writes next.

The capacity bound of `Func23Spec` comes from
`Project.RustHashMap.Decoder.grow_no_overflow`, which the allocator fact
`CapacityFits` gives.  The lemma asks for `2 <= capacity` only when the
buffer is full, because `CapacityFits` does not survive a grow of a buffer
of one pair: the new block is four pairs, and the bound charges sixteen
bytes for each pair of the new capacity.  The decoder never reaches that
case.  The first allocation is `min(count, 512)` pairs, and a grow needs
the index to reach the capacity, so the capacity is 512 or more at every
grow.  A buffer that is not full takes no bound above `0 < capacity`,
which is what a count of one needs.
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
open Project.RustHashMap.FrameCells
open Project.RustHashMap.VecGrow
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

/-- Read the size of a live block without giving it up. -/
private theorem LiveBlock_size [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId : Nat) (ptr : UInt32)
    (layout : AllocLayout) (bytes : List UInt8) :
    LiveBlock heapId allocationId ptr layout bytes ⊢
      iprop(LiveBlock heapId allocationId ptr layout bytes ∗
        ⌜bytes.length = layout.size⌝) := by
  iintro Hblock
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
  isplitl [Htoken Hbytes]
  · unfold LiveBlock
    iframe_pureexact using [Htoken Hbytes] => hfacts
  · ipureexact hfacts.1

/-- Read both frontier bounds of the allocator without giving it up. -/
private theorem BumpHeap_frontier_bounds
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) :
    BumpHeap heapId storedCursor frontier history ⊢
      iprop(BumpHeap heapId storedCursor frontier history ∗
        ⌜heapBase.toNat ≤ frontier ∧ frontier < 2147483648⌝) := by
  iintro Hbump
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
  isplitl [Hcursor Hfrontier Hauth Hretired Hpages]
  · unfold BumpHeap
    iframe Hcursor Hfrontier Hauth Hretired
    iexists ownedPages
    iframe_pureexact using [Hpages] => hheap
  · ipureexact ⟨hheap.1, hheap.2.1⟩

/-- A capacity of two pairs or more doubles without the floor of four. -/
private theorem pairPushCapacity_double (capacity : Nat)
    (hcapacity : 2 ≤ capacity) :
    pairPushCapacity capacity = 2 * capacity := by
  unfold pairPushCapacity
  exact Nat.max_eq_left (by omega)

set_option maxHeartbeats 2000000 in
/-- The amortized grow.  Both paths leave one live block with room for the
pair that the append writes next. -/
theorem twp_grow_body [WasmSmallStepGS hlc Universal.State]
    (out hdr frame capacity buffer written : UInt32)
    (allocationId : Nat) (allBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l4 l5 l6 l7 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hframeLow : 16 ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (hcapacity : 0 < capacity.toNat)
    (hgrowable : written = capacity → 2 ≤ capacity.toNat)
    (hwritten : written.toNat ≤ capacity.toNat)
    (hfits : CapacityFits capacity frontier) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackReserve (frame - 16) shadow ∗
      pointsTo_u32 0 (frame + 4) capacity ∗
      pointsTo_u32 0 (frame + 8) buffer ∗
      LiveBlock heapId allocationId buffer (pairBlock capacity.toNat)
        allBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ newCapacity : UInt32, ∀ newBuffer : UInt32, ∀ newId : Nat,
          ∀ newBytes : List UInt8, ∀ shadow' : List UInt8,
          ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
          ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackReserve (frame - 16) shadow' -∗
          pointsTo_u32 0 (frame + 4) newCapacity -∗
          pointsTo_u32 0 (frame + 8) newBuffer -∗
          LiveBlock heapId newId newBuffer (pairBlock newCapacity.toNat)
            newBytes -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜written.toNat < newCapacity.toNat ∧
            newBytes.take (8 * capacity.toNat) = allBytes ∧
            CapacityFits newCapacity frontier'⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 hdr],
                  [.i32 frame, .i32 written, l4, l5, l6, l7,
                    .i32 newBuffer, l9, l10, l11, l12],
                stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining : List UInt8,
          Streams remaining output true -∗
          Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, .i32 written, l4, l5, l6, l7, .i32 buffer, l9,
                l10, l11, l12],
            stack⟩,
            .block 0 0 growBody :: code, arity, remainder, controls,
            calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hcapacity, Hpointer, Hblock, Hbump,
    Hstreams, Hcont⟩
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts frame 4 4 rfl (by omega)
  obtain ⟨hf8, hf8a, hf8b, hf8c⟩ := offset_facts frame 8 8 rfl (by omega)
  have hplus8 : frame + 4 + 4 = frame + 8 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  have hheadAddr : (4 : UInt32) + frame = frame + 4 := UInt32.add_comm 4 frame
  ihave ⟨Hblock, %hallBytes⟩ := LiveBlock_size heapId allocationId buffer
    (pairBlock capacity.toNat) allBytes $$ Hblock
  ihave ⟨Hbump, %hfrontier⟩ := BumpHeap_frontier_bounds heapId storedCursor
    frontier history $$ Hbump
  have holdSize : allBytes.length = 8 * capacity.toNat := hallBytes
  have hbound : 8 * max 4 (2 * capacity.toNat) ≤ 2147483644 :=
    grow_no_overflow hfits hfrontier.2
  have hsize : UInt32.size = 4294967296 := rfl
  have holdValid : (pairBlock capacity.toNat).Valid := by
    refine ⟨?_, ?_, ⟨2, ?_⟩, ?_, ?_, ?_, ?_⟩
    · show 0 < 8 * capacity.toNat
      omega
    · show 0 < 4
      omega
    · show (4 : Nat) = 2 ^ 2
      norm_num
    · show (4 : Nat) ≤ 2147483648
      omega
    · show 8 * capacity.toNat ≤ 2147483648 - 4
      omega
    · show 8 * capacity.toNat < UInt32.size
      rw [hsize]; omega
    · show (4 : Nat) < UInt32.size
      rw [hsize]; omega
  simp only [growBody]
  wasm_twp_pures [twp_block twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := frame) (offset := 4) capacity
    hf4 hf4a hf4b hf4c with Hcapacity
  by_cases hfull : written = capacity
  · -- the buffer is full, so the body calls `grow_one`
    have hcapacity2 : 2 ≤ capacity.toNat := hgrowable hfull
    have hdouble : 8 * (2 * capacity.toNat) ≤ 2147483644 := by
      have : 4 ≤ 2 * capacity.toNat := by omega
      rw [Nat.max_eq_right this] at hbound
      exact hbound
    have hpush : pairPushCapacity capacity.toNat = 2 * capacity.toNat :=
      pairPushCapacity_double capacity.toNat hcapacity2
    iapply twp_ne (result := 0) (by rw [if_neg (by simp [hfull])])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_add]
    rw [hheadAddr]
    ihave Hpointer' :=
      Project.RustHashMap.Func98Proof.pointsTo_u32_address_eq hplus8.symm $$
        Hpointer
    ihave Hheader : PairHeader (frame + 4) capacity buffer $$
        [Hcapacity Hpointer']
    · unfold PairHeader
      iframe
    ihave Hsource : FinishSourceOwn heapId capacity buffer
        (pairBlock capacity.toNat)
        (FinishSource.allocated allocationId allBytes) $$ [Hblock]
    · isimp only [FinishSourceOwn]
      isplitr_pureexact ⟨by omega, holdValid⟩
      · iexact Hblock
    have Hgrow : Func23Spec (hlc := hlc) :=
      Project.RustHashMap.Func23Proof.func23_correct
    unfold Func23Spec CallContract callExpr at Hgrow
    simp only [List.cons_append, List.nil_append] at Hgrow
    iapply Hgrow (header := frame + 4) (sp := frame) (capacity := capacity)
      (ptr := buffer) (source := FinishSource.allocated allocationId allBytes)
      (shadow := shadow) (heapId := heapId) (storedCursor := storedCursor)
      (frontier := frontier) (history := history) (input := input)
      (output := output) (raised := raised)
      (callerLocals :=
        { params := [.i32 out, .i32 hdr]
          locals := [.i32 frame, .i32 written, l4, l5, l6, l7,
            .i32 buffer, l9, l10, l11, l12]
          values := [] })
      (stack := stack)
    isplitl_exact Hruntime
    isplitl_exacts [Hsp Hreserve Hheader Hsource Hbump Hstreams]
    isplitl_pureexact (by
      refine ⟨hframeLow, ?_, ?_⟩
      · rw [hf4]
        have h4 : (4 : UInt32).toNat = 4 := by decide
        rw [h4]; omega
      · rw [hpush]; omega)
    simp only [PairGrowContinuation]
    cases hdecision :
        classifyBump frontier (pairBlock (pairPushCapacity capacity.toNat))
      with
    | oom =>
        iintro _Hsp _Hreserve _Hheader _Hsource _Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        ihave Hoom := Hoom $$ %input
        iapply Hoom $$ Hstreams
    | success newPtr finish =>
        isplit
        · iintro %newBytes %finalHistory Hruntime Hsp Hreserve Hheader
            Hblock Hbump %hgrown Hstreams
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          isimp only [PairHeader] at Hheader
          icases Hheader with ⟨Hcapacity, Hpointer⟩
          ihave Hpointer :=
            Project.RustHashMap.Func98Proof.pointsTo_u32_address_eq hplus8 $$
              Hpointer
          wasm_twp_pures [twp_localGet]
          wasm_twp_rebind twp_load32 (address := frame) (offset := 8) newPtr
            hf8 hf8a hf8b hf8c with Hpointer
          wasm_twp_localSet [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          wasm_twp_pures [twp_exitControl]
            using [List.take_zero, List.drop_zero, List.nil_append]
          have hnewNat :
              (UInt32.ofNat (pairPushCapacity capacity.toNat)).toNat =
                2 * capacity.toNat := by
            rw [hpush]
            exact UInt32.toNat_ofNat_of_lt' (by rw [hsize]; omega)
          have hlayout :
              pairBlock (UInt32.ofNat (pairPushCapacity capacity.toNat)).toNat
                = pairBlock (pairPushCapacity capacity.toNat) := by
            rw [hnewNat, hpush]
          have hnewSize :
              (pairBlock (pairPushCapacity capacity.toNat)).size =
                8 * (2 * capacity.toNat) := by
            show 8 * pairPushCapacity capacity.toNat = 8 * (2 * capacity.toNat)
            rw [hpush]
          have hcapFits :
              CapacityFits (UInt32.ofNat (pairPushCapacity capacity.toNat))
                finish.toNat := by
            refine CapacityFits.grow hfits hnewNat ?_
            rw [hnewNat]
            have := hgrown.2
            rw [hnewSize] at this
            omega
          have hprefix : newBytes.take (8 * capacity.toNat) = allBytes :=
            hgrown.1
          ihave Hblock :
              LiveBlock heapId history.nextId newPtr
                (pairBlock
                  (UInt32.ofNat (pairPushCapacity capacity.toNat)).toNat)
                newBytes $$ [Hblock]
          · irw_exact [hlayout] with Hblock
          ihave Hnormal := BI.and_elim_l $$ Hcont
          ihave Hnormal := Hnormal
            $$ %(UInt32.ofNat (pairPushCapacity capacity.toNat)) %newPtr
              %history.nextId %newBytes
              %(pairReserveShadow shadow newPtr
                (UInt32.ofNat
                  (pairBlock (pairPushCapacity capacity.toNat)).size))
              %finish %finish.toNat %finalHistory
          iapply Hnormal $$ Hruntime Hsp Hreserve Hcapacity Hpointer Hblock
            Hbump Hstreams
            %⟨by rw [hfull, hnewNat]; omega, hprefix, hcapFits⟩
        · iintro _Hsp _Hreserve _Hheader _Hsource _Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          ihave Hoom := Hoom $$ %input
          iapply Hoom $$ Hstreams
  · -- the buffer has room, so the body leaves the block at once
    iapply twp_ne (result := 1) (by rw [if_pos hfull])
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    have hlt : written.toNat < capacity.toNat := by
      have hne : written.toNat ≠ capacity.toNat := fun h =>
        hfull (UInt32.toNat_inj.mp h)
      omega
    have hprefix : allBytes.take (8 * capacity.toNat) = allBytes := by
      rw [← holdSize, List.take_length]
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %capacity %buffer %allocationId %allBytes
      %shadow %storedCursor %frontier %history
    iapply Hnormal $$ Hruntime Hsp Hreserve Hcapacity Hpointer Hblock Hbump
      Hstreams %⟨hlt, hprefix, hfits⟩

end Project.RustHashMap.Decoder
