import Project.RustHashMap.DecoderGrow
import Project.RustHashMap.DecoderAppendPair

/-!
# One turn of the pair loop of the decoder

The loop body of absolute `func 4` reads one pair, grows the buffer when it
is full, writes the pair, and compares the count with the header length.
`twp_loop_iteration` joins the three stage lemmas and closes both exits.

The proof runs in this order:

1. `twp_pair_stage` reads eight bytes of the input.  The short arm and the
   allocator arm go straight to the matching arms of `LoopCont`.
2. `frame_split` and `StackBelow_as_reserve` cut the 16 bytes below the
   frame that `twp_grow_body` needs, and `frame_join` puts them back.
3. `twp_grow_body` gives a buffer with room for one more pair.
4. `twp_append_pair` writes the key and the value and raises the count.
5. The compare picks the exit.  The last pair falls out of the loop and
   `LoopCont` takes the accepting return.  Any other pair takes the back
   edge and the recursive hypothesis of the loop rule.

`payload_step` is the content of the loop: one more pair on the payload is
the eight input bytes that follow the last one.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.VecGrow
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

/-- Read the depth of a stack region without giving it up. -/
private theorem StackBelow_length [WasmHeapGS Universal.State]
    (sp : UInt32) (depth : Nat) (bytes : List UInt8) :
    StackBelow sp depth bytes ⊢
      iprop(StackBelow sp depth bytes ∗ ⌜bytes.length = depth⌝) := by
  iintro Hbelow
  isimp only [StackBelow] at Hbelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  isplitl [Hbytes]
  · unfold StackBelow
    isplitl_pureexact hlength
    · iexact Hbytes
  · ipureexact hlength

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

/-- One more pair on the payload is the eight bytes that follow it in the
input. -/
theorem payload_step (bytes : List UInt8) (index : Nat)
    (hfit : 4 + 8 * index + 8 ≤ bytes.length) :
    payload bytes (index + 1)
      = payload bytes index ++
        WordCodec.u32le.serialize
          [WordCodec.decodeU32 ((bytes.drop (4 + 8 * index)).take 4),
            WordCodec.decodeU32 ((bytes.drop (4 + 8 * index + 4)).take 4)] :=
    by
  have hlen1 : ((bytes.drop (4 + 8 * index)).take 4).length = 4 := by
    rw [List.length_take, List.length_drop]; omega
  have hlen2 : ((bytes.drop (4 + 8 * index + 4)).take 4).length = 4 := by
    rw [List.length_take, List.length_drop]; omega
  have hser : WordCodec.u32le.serialize
      [WordCodec.decodeU32 ((bytes.drop (4 + 8 * index)).take 4),
        WordCodec.decodeU32 ((bytes.drop (4 + 8 * index + 4)).take 4)]
      = (bytes.drop (4 + 8 * index)).take 4 ++
        (bytes.drop (4 + 8 * index + 4)).take 4 := by
    rw [WordCodec.serialize_cons, WordCodec.serialize_cons,
      WordCodec.serialize_nil, List.append_nil,
      show WordCodec.u32le.encode = WordCodec.encodeU32 from rfl,
      Slices.encodeU32_decodeU32_of_length _ hlen1,
      Slices.encodeU32_decodeU32_of_length _ hlen2]
  have hchunk : (bytes.drop (4 + 8 * index)).take 8
      = (bytes.drop (4 + 8 * index)).take 4 ++
        (bytes.drop (4 + 8 * index + 4)).take 4 := by
    have h : (bytes.drop (4 + 8 * index)).take (4 + 4)
        = (bytes.drop (4 + 8 * index)).take 4 ++
          ((bytes.drop (4 + 8 * index)).drop 4).take 4 := List.take_add
    rw [List.drop_drop] at h
    exact h
  rw [hser]
  unfold payload
  rw [show 8 * (index + 1) = 8 * index + 8 from by omega, List.take_add,
    List.drop_drop, hchunk]

set_option maxHeartbeats 2000000 in
/-- One turn of the pair loop keeps the loop invariant or leaves the loop
through one of the three arms of `LoopCont`. -/
theorem twp_loop_iteration [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore pad scratch dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value)
    (decodeFrame : ControlFrame)
    (errorBody errorCont : Program) (errorBelow : List Value)
    (errorControls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hlen : bytes.length = len.toNat)
    (hscratchLength : scratch.length = 48)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hptrNowrap : ptr.toNat + bytes.length < UInt32.size)
    (st : LoopState) :
    iprop(
      LoopInv out hdr ptr len frame count heapId bytes outBefore pad scratch
        dataBytes input output raised arity remainder
        (decodeFrame :: allocFrame errorBody errorCont errorBelow ::
          errorControls)
        errorControls errorCont errorBelow calls s E Φ st ∗
      (∀ j : LoopState,
        ⌜loopMeasure count.toNat j < loopMeasure count.toNat st⌝ -∗
        LoopInv out hdr ptr len frame count heapId bytes outBefore pad
          scratch dataBytes input output raised arity remainder
          (decodeFrame :: allocFrame errorBody errorCont errorBelow ::
            errorControls)
          errorControls errorCont errorBelow calls s E Φ j -∗
        WP (loopBodyExpr (α := Universal.State)
          (loopLocals out hdr frame ptr len count j) 0 0 arity pairLoopBody
          okReturn remainder []
          (decodeFrame :: allocFrame errorBody errorCont errorBelow ::
            errorControls) calls) @ s; E [{ Φ }])) ⊢
      WP (loopBodyExpr (α := Universal.State)
        (loopLocals out hdr frame ptr len count st) 0 0 arity pairLoopBody
        okReturn remainder []
        (decodeFrame :: allocFrame errorBody errorCont errorBelow ::
          errorControls) calls) @ s; E [{ Φ }] := by
  iintro ⟨Hinv, Hrec⟩
  isimp only [LoopInv] at Hinv
  icases Hinv with ⟨Hruntime, Hsp, Hbelow, Hpad, Hcapacity, Hbuffer,
    Hlength, Hscratch, Hout, Hhdr, Hlen, Hinput, Hdata, Hblock, Hbump,
    Hstreams, %hfacts, Hcont⟩
  obtain ⟨hindex, hindexCap, hcap2, hfit, hpayload, hfits⟩ := hfacts
  have hsize : UInt32.size = 4294967296 := rfl
  have hcountLt : count.toNat < UInt32.size := count.toNat_lt_size
  have hlenLt : len.toNat < UInt32.size := len.toNat_lt_size
  have hposNat : (UInt32.ofNat (4 + 8 * st.index)).toNat = 4 + 8 * st.index :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hposLe : UInt32.ofNat (4 + 8 * st.index) ≤ len :=
    UInt32.le_iff_toNat_le.mpr (by omega)
  have hremaining :
      (len - UInt32.ofNat (4 + 8 * st.index)).toNat
        = bytes.length - (4 + 8 * st.index) := by
    rw [UInt32.toNat_sub_of_le len _ hposLe, hposNat]
    omega
  have hdepth : decoderDepth - 64 = func49Depth := rfl
  isimp only [hdepth] at Hbelow
  simp only [loopBodyExpr, loopLocals, pairLoopBody]
  iapply twp_pair_stage (out := out) (hdr := hdr) (frame := frame)
    (ptr := ptr) (cursor := ptr + UInt32.ofNat (4 + 8 * st.index))
    (remaining := len - UInt32.ofNat (4 + 8 * st.index))
    (pos := 4 + 8 * st.index) (heapId := heapId) (bytes := bytes)
    (scratch := scratch) (below := st.below) (dataBytes := dataBytes)
    (storedCursor := st.storedCursor) (frontier := st.frontier)
    (history := st.history) (input := input) (output := output)
    (raised := raised)
    (l3 := .i32 (UInt32.ofNat st.index)) (l7 := .i32 count)
    (l8 := .i32 st.buffer) (l9 := .i32 (UInt32.ofNat (8 * st.index + 4)))
    (l10 := .i32 st.aux10) (l11 := .i32 st.aux11) (l12 := .i32 st.aux12)
    (loopFrame := _) (decodeFrame := decodeFrame) (errorBody := errorBody)
    (errorCont := errorCont) (errorBelow := errorBelow)
    (hcursor := rfl) (hpos := by omega) (hremaining := hremaining)
    (hptrNowrap := hptrNowrap) (hhdrNowrap := hhdrNowrap)
    (hscratchLength := hscratchLength) (hdataLength := hdataLength)
    (hframeLow := hframeLow) (hframeNowrap := hframeNowrap)
  isplitl_exacts [Hruntime Hsp Hbelow Hscratch Hdata Hhdr Hlen Hinput Hbump
    Hstreams]
  isimp only [LoopCont] at Hcont
  isplit
  · -- the pair is present
    iintro %key %value Hruntime Hsp Hbelow Hscratch Hdata Hhdr Hlen Hinput
      Hbump Hstreams %hpair
    obtain ⟨hfit8, hkey, hvalue⟩ := hpair
    have hindexNat : (UInt32.ofNat st.index).toNat = st.index :=
      UInt32.toNat_ofNat_of_lt' (by omega)
    have hcapPos : 0 < st.capacity.toNat := by
      rcases hcap2 with h | h <;> omega
    have hgrowable : UInt32.ofNat st.index = st.capacity →
        2 ≤ st.capacity.toNat := by
      intro heq
      have hindexEq : st.index = st.capacity.toNat := by
        rw [← heq, hindexNat]
      rcases hcap2 with h | h
      · omega
      · exact h
    have hdeepLow : (16 : Nat) ≤ func49Depth := by
      simp only [func49Depth, errorNewDepth]
      omega
    ihave ⟨Hbelow, %hbelowLength⟩ :=
      StackBelow_length frame func49Depth st.below $$ Hbelow
    ihave ⟨Hblock, %holdSize⟩ := LiveBlock_size heapId st.allocationId
      st.buffer (pairBlock st.capacity.toNat) st.blockBytes $$ Hblock
    simp only [pairBlock] at holdSize
    ihave ⟨Hdeep, Hshadow⟩ :=
      frame_split frame func49Depth 16 st.below hdeepLow $$ Hbelow
    ihave Hshadow :=
      (StackBelow_as_reserve frame (st.below.drop (func49Depth - 16))).mp
        $$ Hshadow
    iapply twp_grow_body out hdr frame st.capacity st.buffer
      (UInt32.ofNat st.index) st.allocationId st.blockBytes
      (st.below.drop (func49Depth - 16)) heapId st.storedCursor st.frontier
      st.history input output raised (.i32 (frame + 52))
      (.i32 (len - UInt32.ofNat (4 + 8 * st.index) - 8))
      (.i32 (ptr + UInt32.ofNat (4 + 8 * st.index) + 8)) (.i32 count)
      (.i32 (UInt32.ofNat (8 * st.index + 4))) (.i32 key)
      (.i32 (ptr + UInt32.ofNat (4 + 8 * st.index) + 8)) (.i32 value)
      (by omega) hframeNowrap hcapPos hgrowable (by omega) hfits
    isplitl_exacts [Hruntime Hsp Hshadow Hcapacity Hbuffer Hblock Hbump
      Hstreams]
    isplit
    · -- the buffer has room after the grow
      iintro %newCapacity %newBuffer %newId %newBytes %shadow'
        %storedCursor' %frontier' %history'
        Hruntime Hsp Hshadow Hcapacity Hbuffer Hblock Hbump Hstreams %hgrow
      obtain ⟨hwritten, hprefix, hfitsNew⟩ := hgrow
      rw [hindexNat] at hwritten
      rw [appendPair_shape]
      iapply twp_append_pair out hdr frame newBuffer newCapacity key value
        (UInt32.ofNat st.index) st.index newId heapId newBytes
        (.i32 (frame + 52))
        (.i32 (len - UInt32.ofNat (4 + 8 * st.index) - 8))
        (.i32 (ptr + UInt32.ofNat (4 + 8 * st.index) + 8)) (.i32 count)
        (.i32 (ptr + UInt32.ofNat (4 + 8 * st.index) + 8))
        hwritten hframeNowrap
      ihave ⟨Hblock, %hnewSize⟩ := LiveBlock_size heapId newId newBuffer
        (pairBlock newCapacity.toNat) newBytes $$ Hblock
      simp only [pairBlock] at hnewSize
      have hcapGrow : st.capacity.toNat ≤ newCapacity.toNat := by
        have hlengths := congrArg List.length hprefix
        rw [List.length_take, hnewSize, holdSize] at hlengths
        omega
      have hpayloadNext :
          (newBytes.take (8 * st.index) ++
            WordCodec.u32le.serialize [key, value] ++
            newBytes.drop (8 * st.index + 8)).take (8 * (st.index + 1))
            = payload bytes (st.index + 1) := by
        have hAlen : (newBytes.take (8 * st.index)).length = 8 * st.index := by
          rw [List.length_take, hnewSize]
          omega
        have hBlen : (WordCodec.u32le.serialize [key, value]).length = 8 := by
          simp
        have hABlen : (newBytes.take (8 * st.index) ++
            WordCodec.u32le.serialize [key, value]).length
              = 8 * (st.index + 1) := by
          rw [List.length_append, hAlen, hBlen]
          omega
        rw [List.take_left' hABlen]
        have hA : newBytes.take (8 * st.index) = payload bytes st.index := by
          rw [← hpayload, ← hprefix, List.take_take]
          congr 1
          omega
        rw [hA, hkey, hvalue, payload_step bytes st.index (by omega)]
      isplitl_exacts [Hblock Hlength]
      iintro Hblock Hlength
      wasm_twp_pures [twp_localGet twp_localGet]
      ihave Hshadow :=
        (StackBelow_as_reserve frame shadow').mpr $$ Hshadow
      ihave Hbelow := frame_join frame func49Depth 16
        (st.below.take (func49Depth - 16)) shadow'
        (by rw [List.length_take, hbelowLength]; omega) hdeepLow
        $$ [Hdeep Hshadow]
      · isplitl_exact Hdeep
        · iexact Hshadow
      isimp only [← hdepth] at Hbelow
      by_cases hlast : st.index + 1 = count.toNat
      · -- the last pair leaves the loop at the accepting return
        have hcount : UInt32.ofNat (st.index + 1) = count := by
          rw [hlast, UInt32.ofNat_toNat]
        iapply twp_ne (result := 0) (by rw [if_neg (by simp [hcount])])
        iapply twp_brIfZero
        wasm_twp_pures [twp_exitControl]
          using [List.take_zero, List.nil_append]
        isimp only [hcount] at Hlength
        isimp only [loop_cursor_step, hlast] at Hhdr
        isimp only [loop_remaining_step, hlast] at Hlen
        rw [loop_remaining_step, loop_cursor_step, hlast, UInt32.ofNat_toNat]
        ihave Hnormal := BI.and_elim_l $$ Hcont
        ihave Hnormal := Hnormal $$ %newCapacity %newBuffer %newId
          %(newBytes.take (8 * st.index) ++
            WordCodec.u32le.serialize [key, value] ++
            newBytes.drop (8 * st.index + 8))
          %(st.below.take (decoderDepth - 64 - 16) ++ shadow')
          %storedCursor' %frontier' %history' %(Value.i32 key)
          %(Value.i32 (newBuffer + UInt32.ofNat (8 * st.index) + 4))
          %(Value.i32 value)
        iapply Hnormal $$ Hruntime Hsp Hbelow Hpad Hcapacity Hbuffer Hlength
          Hscratch Hout Hhdr Hlen Hinput Hdata Hblock Hbump Hstreams
          %⟨by omega, by omega,
            by rw [← hlast]; exact hpayloadNext⟩
      · -- more pairs remain: take the back edge
        have hnextNat : (UInt32.ofNat (st.index + 1)).toNat = st.index + 1 :=
          UInt32.toNat_ofNat_of_lt' (by omega)
        have hne : count ≠ UInt32.ofNat (st.index + 1) := by
          intro heq
          apply hlast
          have htoNat := congrArg UInt32.toNat heq
          rw [hnextNat] at htoNat
          omega
        iapply twp_ne (result := 1) (by rw [if_pos hne])
        iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [List.take_zero, List.nil_append]
        rw [loop_remaining_step, loop_cursor_step]
        ihave Hnext := Hrec $$
          %({ index := st.index + 1, capacity := newCapacity,
              buffer := newBuffer, allocationId := newId,
              blockBytes := newBytes.take (8 * st.index) ++
                WordCodec.u32le.serialize [key, value] ++
                newBytes.drop (8 * st.index + 8),
              below := st.below.take (decoderDepth - 64 - 16) ++ shadow',
              storedCursor := storedCursor', frontier := frontier',
              history := history', aux10 := key,
              aux11 := newBuffer + UInt32.ofNat (8 * st.index) + 4,
              aux12 := value } : LoopState)
          %(by simp only [loopMeasure]; omega)
        iapply Hnext
        isimp only [LoopInv, LoopCont, loopLocals]
        isplitl_exacts [Hruntime Hsp Hbelow Hpad Hcapacity Hbuffer Hlength
          Hscratch Hout Hhdr Hlen Hinput Hdata Hblock Hbump Hstreams]
        isplitl_pureexact ⟨by omega, by omega,
          (by rcases hcap2 with h | h
              exacts [Or.inl (by omega), Or.inr (by omega)]),
          by omega, hpayloadNext, hfitsNew⟩
        iexact Hcont
    · -- the grow asked the allocator and it failed
      iintro %remaining' Hstreams
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Hoom := BI.and_elim_r $$ Htail
      iapply Hoom $$ %remaining' Hstreams
  · isplit
    · -- the pair is short: the decode error leaves the loop
      iintro %word0 %word1 %word2 %word3 %hdrPtr %hdrLen %scratchAfter
        %below' %storedCursor' %frontier' %history' %l5' %l6' %l10' %l12'
        Hruntime Hsp Hbelow Hscratch Hdata Hhdr Hlen Hinput Hbump Hstreams
        %hshort
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Herror := BI.and_elim_l $$ Htail
      ihave Herror := Herror $$ %word0 %word1 %word2 %word3 %hdrPtr %hdrLen
        %st.capacity %st.buffer %(UInt32.ofNat st.index) %scratchAfter
        %below' %storedCursor' %frontier' %history'
        %(.i32 (UInt32.ofNat st.index)) %l5' %l6'
        %(.i32 (UInt32.ofNat (8 * st.index + 4))) %l10' %l12'
      isimp only [← hdepth] at Hbelow
      iapply Herror $$ Hruntime Hsp Hbelow Hpad Hcapacity Hbuffer Hlength
        Hscratch Hout Hhdr Hlen Hinput Hdata Hbump Hstreams
        %⟨hshort.2.1, hshort.2.2, by omega⟩
    · -- the allocator failed
      iintro %remaining' Hstreams
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Hoom := BI.and_elim_r $$ Htail
      iapply Hoom $$ %remaining' Hstreams

end Project.RustHashMap.Decoder
