import Project.RustHashMap.DecoderBody
import Project.RustHashMap.DecoderPrologue

/-!
# Proof of the borsh decoder

Local `func1` (absolute index 4) is `Vec<(u32, u32)>::deserialize`.  It is
WAT lines 470 to 850, the largest body of `map_len` after
`collect_entries`.

`Project.RustHashMap.Decoder.func1_shape` splits the body into the frame,
the outer block, and the stack epilogue.  The proof runs the three in
order:

1. `twp_decoder_frame` lowers the stack pointer by 64 and cuts the
   region below the caller into the frame of the decoder and the region
   of its callees;
2. `twp_outer_body` runs the header stage and the allocation phase and
   reports the two exits of the body;
3. the epilogue adds the 64 bytes back, `frame_join` puts the region
   together again, and the body falls off its own end.

The contract asks for `decoderDepth` bytes below the caller, which is
240.  The frame takes 64 of them and the callees get the other 176,
which is `func49Depth`.  Both numbers are the measured worst path, so
neither has slack.

The theorem is unconditional.
-/

namespace Project.RustHashMap.Func1Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.Decoder
open scoped Wasm.SmallStep.Outcome

/-- The frame pointer of the decoder, as a number. -/
private theorem sub64_toNat (sp : UInt32) (h : 64 ≤ sp.toNat) :
    (sp - 64).toNat = sp.toNat - 64 := by
  have hbits : (sp - 64).toNat
      = (sp.toBitVec - (64 : UInt32).toBitVec).toNat := rfl
  have h64 : ((64 : UInt32).toBitVec).toNat = 64 := rfl
  have hsp : sp.toBitVec.toNat = sp.toNat := rfl
  have hsize : sp.toNat < UInt32.size := sp.toNat_lt_size
  rw [hbits, BitVec.toNat_sub, h64, hsp]
  have hpow : (2 : Nat) ^ 32 = UInt32.size := rfl
  omega

/-- Put the 64-byte frame back on top of the region of the callees. -/
private theorem decoder_frame_join [WasmHeapGS Universal.State]
    (sp : UInt32) (below' frameAfter : List UInt8)
    (hlength : frameAfter.length = 64) :
    iprop(StackBelow (sp - 64) func49Depth below' ∗
        Slices.ByteSlice 0 (sp - 64) frameAfter) ⊢
      StackBelow sp decoderDepth (below' ++ frameAfter) := by
  have hbase : sp - UInt32.ofNat 64 = sp - 64 := rfl
  have hdepth : decoderDepth - 64 = func49Depth := rfl
  iintro ⟨Hbelow, Hframe⟩
  ihave ⟨Hbelow, %hbelowLen⟩ :=
    StackBelow_length (sp - 64) func49Depth below' $$ Hbelow
  ihave Hframe :=
    StackBelow_intro sp (sp - 64) 64 frameAfter hlength hbase $$ Hframe
  isimp only [← hdepth, ← hbase] at Hbelow
  iapply frame_join sp decoderDepth 64 below' frameAfter
    (by rw [hbelowLen, hdepth]) (by decide)
  isplitl_exact Hbelow
  · iexact Hframe

private theorem func1_index :
    Project.RustHashMap.«module».funcs[1]? =
      some Project.RustHashMap.func1Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The decoder meets its contract. -/
theorem func1_correct [WasmSmallStepGS hlc Universal.State] :
    Func1Spec (hlc := hlc) := by
  unfold Func1Spec CallContract callExpr
  intro sp out hdr ptr len heapId bytes outBefore below dataBytes
    storedCursor frontier history input output raised callerLocals stack
    code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hptr, Hlen, Hbytes, Hdata, Hbump,
    Hstreams, %hfacts, Hcont⟩
  have hdeep : decoderDepth ≤ sp.toNat := hfacts.2.2.1
  have h240 : decoderDepth = 240 := rfl
  have h176 : func49Depth = 176 := rfl
  have hspNat : (sp - 64).toNat = sp.toNat - 64 :=
    sub64_toNat sp (by omega)
  have hframeLow : func49Depth ≤ (sp - 64).toNat := by
    rw [hspNat]
    omega
  have hframeNowrap : (sp - 64).toNat + 64 < UInt32.size := by
    rw [hspNat]
    have hsize : sp.toNat < UInt32.size := sp.toNat_lt_size
    omega
  have hrestore : 64 + (sp - 64) = sp := by
    rw [UInt32.add_comm]
    exact UInt32.sub_add_cancel sp 64
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 4
      Project.RustHashMap.func1Def (by decide) func1_index with Hmodule
  simp [Project.RustHashMap.func1Def, Function.toLocals, Function.numParams]
  rw [Project.RustHashMap.Decoder.func1_shape]
  have hzero : (ValueType.i32.zero : Value) = .i32 0 := rfl
  simp only [hzero]
  iclose_map_runtime Hruntime with Hmodule Henv
  iapply twp_decoder_frame sp out hdr below _ _ _ _ _ _ _ _ _ _ _
  isplitl_exacts [Hsp Hbelow]
  iintro Hsp Hbelow Hframe %hframeLength
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_outer_body out hdr ptr len (sp - 64) heapId
    (below.drop func49Depth) outBefore (below.take func49Depth) dataBytes
    bytes storedCursor frontier history input output raised
    _ _ _ _ _ _ _ _ _ _
    _ _ outerBody stackEpilogue _ [] _ s E Φ
    hframeLength hfacts.1 hfacts.2.1 hfacts.2.2.2.2.2
    hframeLow hframeNowrap hfacts.2.2.2.1 hfacts.2.2.2.2.1
  isplitl_exacts [Hruntime Hsp Hbelow Hframe Hout Hptr Hlen Hbytes Hdata
    Hbump Hstreams]
  isimp only [BodyCont]
  isplit
  · -- the accepting exit
    iintro %capacity %buffer %payloadBytes %spareBytes %frameAfter %below'
      %storedCursor' %frontier' %history' %r3 %r4 %r5 %r6 %r7 %r8 %r9
      %r10 %r11 %r12
      Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hbytes Hdata Hbuf Hbump
      Hstreams %hfacts2
    simp only [stackEpilogue]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [StackPointer] at Hsp
    wasm_twp_rebind twp_globalSet with Hsp
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      irw_exact [hrestore] with Hsp
    ihave Hbelow :=
      decoder_frame_join sp below' frameAfter hfacts2.2.1 $$
        [Hbelow Hframe]
    · isplitl_exact Hbelow
      · iexact Hframe
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
    simp only [List.take_zero, List.nil_append]
    isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil] at Hout
    ihave Hok := BI.and_elim_l $$ Hcont
    ihave Hok := Hok $$ %capacity %buffer %payloadBytes %spareBytes
      %(below' ++ frameAfter) %storedCursor' %frontier' %history'
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hok
    iapply Hok $$ %(hfacts2.1) [Hmodule Henv] Hsp Hbelow Hout Hhdr Hlen
      Hbytes Hdata Hbuf Hbump Hstreams
      %⟨hfacts2.2.2.1, hfacts2.2.2.2.1, hfacts2.2.2.2.2.1,
        hfacts2.2.2.2.2.2.1, hfacts2.2.2.2.2.2.2⟩
    · isplitl_exact Hmodule
      · iexact Henv
  · isplit
    · -- the rejecting exit
      iintro %word0 %word1 %word2 %word3 %hdrPtr %hdrLen %frameAfter
        %below' %storedCursor' %frontier' %history' %r3 %r4 %r5 %r6 %r7
        %r8 %r9 %r10 %r11 %r12
        Hruntime Hsp Hbelow Hframe Hout Hhdr Hlen Hbytes Hdata Hbump
        Hstreams %hfacts2
      simp only [stackEpilogue]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [StackPointer] at Hsp
      wasm_twp_rebind twp_globalSet with Hsp
      ihave Hsp : StackPointer sp $$ [Hsp]
      · unfold StackPointer
        irw_exact [hrestore] with Hsp
      ihave Hbelow :=
        decoder_frame_join sp below' frameAfter hfacts2.2.2 $$
          [Hbelow Hframe]
      · isplitl_exact Hbelow
        · iexact Hframe
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
      simp only [List.take_zero, List.nil_append]
      isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
        List.append_nil] at Hout
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Hbad := BI.and_elim_l $$ Htail
      ihave Hbad := Hbad $$ %word0 %word1 %word2 %word3 %hdrPtr %hdrLen
        %(below' ++ frameAfter) %storedCursor' %frontier' %history'
      isimp only [RuntimeContext, ResumeWP, resumeExpr,
        List.nil_append] at Hbad
      iapply Hbad $$ %(hfacts2.1) [Hmodule Henv] Hsp Hbelow Hout Hhdr Hlen
        Hbytes Hdata Hbump Hstreams %(hfacts2.2.1)
      · isplitl_exact Hmodule
        · iexact Henv
    · -- the out-of-memory trap
      iintro %remaining' Hstreams
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Hoom := BI.and_elim_r $$ Htail
      iapply Hoom $$ %remaining' Hstreams

end Project.RustHashMap.Func1Proof
