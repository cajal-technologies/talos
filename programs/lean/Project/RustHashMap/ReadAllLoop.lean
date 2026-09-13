import Project.RustHashMap.ReadAllPush

/-!
# The input loop of the hash map drivers: the loop

The core is parameterised by a `FrameMap`.  The `map_len` driver, absolute
function 22, uses the instance `lenMap`.

See `Project.RustHashMap.ReadAllDefs` for the fragments and the loop
invariant.
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
    (hfunc98 : Func98Spec (hlc := hlc)) (fm : FrameMap)
    (base : UInt32) (heapId : GName) (input output : List UInt8)
    (auxTail : List Value)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hbase : 16 ≤ base.toNat ∧ base.toNat + fm.frame.toNat < UInt32.size)
    (hwf : fm.WF)
    (st : LoopState) :
    iprop(
      LoopInv fm base heapId input output auxTail afterLoop arity
        remainder controls calls s E Φ st ∗
      (∀ j : LoopState, ⌜loopMeasure j < loopMeasure st⌝ -∗
        LoopInv fm base heapId input output auxTail afterLoop
          arity remainder controls calls s E Φ j -∗
        WP (loopBodyExpr (α := Universal.State)
          (loopLocals base auxTail j) 0 0 arity (readLoopBody fm)
          afterLoop remainder [] controls calls) @ s; E [{ Φ }])) ⊢
      WP (loopBodyExpr (α := Universal.State)
        (loopLocals base auxTail st) 0 0 arity (readLoopBody fm)
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
    rewriting [UInt32.add_comm fm.chunkOff base]
  wasm_twp_pures [twp_localGet twp_add]
    rewriting [UInt32.add_comm (UInt32.ofNat st.index) (base + fm.chunkOff)]
  ihave ⟨Hbyte, Hclose⟩ := ByteSlice_byteFocus (base + fm.chunkOff)
    (st.chunk ++ st.chunkTail) st.index hbufferIndex $$ Hchunk
  wasm_twp_rebind twp_load8U_addr_gen ((st.chunk ++ st.chunkTail)[st.index])
    with Hbyte
  ihave Hchunk := Hclose $$ Hbyte
  rw [hbyte]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_push_byte hfunc98 fm base (UInt32.ofNat st.index)
    (UInt32.ofNat (st.chunk.length - st.index)) (st.chunk[st.index])
    st.aux3 auxTail heapId st.capacity st.ptr
    (st.pushed ++ st.chunk.take st.index) st.shadow st.remaining output
    st.storedCursor st.frontier st.history hbase hwf hpush
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
      iapply twp_read_chunk fm base (st.chunk ++ st.chunkTail) st.remaining
        output
        []
        (.i32 base :: .i32 0 :: .i32 0 ::
          .i32 (UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length) ::
          .i32 (st.chunk[st.index]).toUInt32 :: auxTail)
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
          %(UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length)
          %((st.chunk[st.index]).toUInt32)
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
            aux3 := UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length
            aux4 := (st.chunk[st.index]).toUInt32 }
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
          aux3 := UInt32.ofNat (st.pushed ++ st.chunk.take st.index).length
          aux4 := (st.chunk[st.index]).toUInt32 }
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
    (hfunc98 : Func98Spec (hlc := hlc)) (fm : FrameMap)
    (base : UInt32) (heapId : GName) (input output : List UInt8)
    (auxTail : List Value)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hbase : 16 ≤ base.toNat ∧ base.toNat + fm.frame.toNat < UInt32.size)
    (hwf : fm.WF)
    (initial : LoopState) :
    LoopInv fm base heapId input output auxTail afterLoop arity
        remainder controls calls s E Φ initial ⊢
      WP (.running
        ⟨loopLocals base auxTail initial,
          .loop 0 0 (readLoopBody fm) :: afterLoop, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LoopState) (measure := loopMeasure)
    (locals := loopLocals base auxTail)
    (I := LoopInv fm base heapId input output auxTail afterLoop
      arity remainder controls calls s E Φ)
    (initial := initial)
    (initialLocals := loopLocals base auxTail initial)
    (body := readLoopBody fm) (code := afterLoop)
    (paramArity := 0) (resultArity := 0)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (belowStack := []) rfl rfl
  · intro st
    iintro Hrec Hinv
    iapply twp_loop_iteration hfunc98 fm base heapId input output auxTail
      afterLoop arity remainder controls calls s E Φ hbase hwf st
    isplitl [Hinv]
    · iexact Hinv
    · iexact Hrec

end Project.RustHashMap.ReadAll
