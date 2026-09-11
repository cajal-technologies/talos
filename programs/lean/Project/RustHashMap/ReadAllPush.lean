import Project.RustHashMap.ReadAllDefs
import CodeLib.SepLogic.SmallStepTotalLiftingBytesTerminal

/-!
# The input loop of the hash map drivers: one push

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

/-! ## One push -/

/-- The store of one byte into a vector with room, then the length update.
Local 3 holds the length and local 4 the byte. -/
theorem twp_store_tail [WasmSmallStepGS hlc Universal.State]
    (base index count : UInt32) (byte : UInt8)
    (aux5 aux6 aux7 aux8 : UInt32)
    (heapId : GName) (capacity ptr : UInt32) (initialized : List UInt8)
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hbase : base.toNat + 300 < UInt32.size)
    (hroom : initialized.length < capacity.toNat) :
    iprop(
      VecU8 heapId (base + 288) capacity ptr initialized ∗
      (VecU8 heapId (base + 288) capacity ptr (initialized ++ [byte]) -∗
        WP (.running
          ⟨⟨[], [.i32 base, .i32 (index + 1), .i32 count,
              .i32 (UInt32.ofNat initialized.length), .i32 byte.toUInt32,
              .i32 aux5, .i32 aux6, .i32 aux7, .i32 aux8], []⟩,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨[], [.i32 base, .i32 index, .i32 count,
            .i32 (UInt32.ofNat initialized.length), .i32 byte.toUInt32,
            .i32 aux5, .i32 aux6, .i32 aux7, .i32 aux8], []⟩,
          storeTail ++ code, arity, remainder, controls, calls⟩ :
            Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hvec, Hcont⟩
  have hsize : UInt32.size = 4294967296 := rfl
  have h292 : base + 288 + 4 = base + 292 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  have h296 : base + 288 + 8 = base + 296 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  have hb292 : (base + 292).toNat = base.toNat + 292 := by
    simpa using Slices.byteOffset_toNat base 292 (by omega)
  have hb292_1 : (base + 292 + 1).toNat = (base + 292).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (base + 292) 1 (by omega)
  have hb292_2 : (base + 292 + 2).toNat = (base + 292).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (base + 292) 2 (by omega)
  have hb292_3 : (base + 292 + 3).toNat = (base + 292).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (base + 292) 3 (by omega)
  have hb296 : (base + 296).toNat = base.toNat + 296 := by
    simpa using Slices.byteOffset_toNat base 296 (by omega)
  have hb296_1 : (base + 296 + 1).toNat = (base + 296).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (base + 296) 1 (by omega)
  have hb296_2 : (base + 296 + 2).toNat = (base + 296).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (base + 296) 2 (by omega)
  have hb296_3 : (base + 296 + 3).toNat = (base + 296).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (base + 296) 3 (by omega)
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
  wasm_twp_rebind twp_load32 (address := base) (offset := 292) ptr
    (by simpa using hb292) hb292_1 hb292_2 hb292_3 with Hptr
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
  wasm_twp_rebind twp_store32 (address := base) (offset := 296)
    (UInt32.ofNat initialized.length) (by simpa using hb296) hb296_1
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
  ihave Hvec : VecU8 heapId (base + 288) capacity ptr (initialized ++ [byte]) $$
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
    (aux5 aux6 aux7 aux8 : UInt32)
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
      VecU8 heapId (base + 288) capacity' ptr' (initialized ++ [byte]) -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams remaining output false -∗
      ⌜PushVecFacts capacity' ptr' frontier'⌝ -∗
      WP (.running
        ⟨⟨[], [.i32 base, .i32 (index + 1), .i32 count,
            .i32 (UInt32.ofNat initialized.length), .i32 byte.toUInt32,
            .i32 aux5, .i32 aux6, .i32 aux7, .i32 aux8], []⟩,
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
    (aux3 aux5 aux6 aux7 aux8 : UInt32)
    (heapId : GName) (capacity ptr : UInt32)
    (initialized shadow remaining output : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hbase : 16 ≤ base.toNat ∧ base.toNat + 300 < UInt32.size)
    (hpush : PushVecFacts capacity ptr frontier) :
    iprop(
      RuntimeContext ∗
      StackPointer base ∗
      StackReserve (base - 16) shadow ∗
      VecU8 heapId (base + 288) capacity ptr initialized ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output false ∗
      PushContinuation base index count byte aux5 aux6 aux7 aux8 heapId
        initialized remaining output code arity remainder controls calls
        s E Φ) ⊢
      WP (.running
        ⟨⟨[], [.i32 base, .i32 index, .i32 count, .i32 aux3,
            .i32 byte.toUInt32, .i32 aux5, .i32 aux6, .i32 aux7, .i32 aux8],
            []⟩,
          .block 0 0 growBody :: (storeTail ++ code), arity, remainder,
          controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hvec, Hbump, Hstreams, Hcont⟩
  isimp only [PushContinuation] at Hcont
  have hsize : UInt32.size = 4294967296 := rfl
  have h296 : base + 288 + 8 = base + 296 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  have hb288 : (base + 288).toNat = base.toNat + 288 := by
    simpa using Slices.byteOffset_toNat base 288 (by omega)
  have hb288_1 : (base + 288 + 1).toNat = (base + 288).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (base + 288) 1 (by omega)
  have hb288_2 : (base + 288 + 2).toNat = (base + 288).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (base + 288) 2 (by omega)
  have hb288_3 : (base + 288 + 3).toNat = (base + 288).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (base + 288) 3 (by omega)
  have hb296 : (base + 296).toNat = base.toNat + 296 := by
    simpa using Slices.byteOffset_toNat base 296 (by omega)
  have hb296_1 : (base + 296 + 1).toNat = (base + 296).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (base + 296) 1 (by omega)
  have hb296_2 : (base + 296 + 2).toNat = (base + 296).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (base + 296) 2 (by omega)
  have hb296_3 : (base + 296 + 3).toNat = (base + 296).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (base + 296) 3 (by omega)
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapacity, Hptr⟩, Hlength, Hstorage⟩
  ihave ⟨Hstorage, %hfits⟩ := VecStorage_length_le heapId capacity ptr
    initialized $$ Hstorage
  ihave Hlength := pointsTo_u32_address_eq h296 $$ Hlength
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  unfold growBody
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := base) (offset := 296)
    (UInt32.ofNat initialized.length) (by simpa using hb296) hb296_1
    hb296_2 hb296_3 with Hlength
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := base) (offset := 288) capacity
    (by simpa using hb288) hb288_1 hb288_2 hb288_3 with Hcapacity
  ihave Hvec : VecU8 heapId (base + 288) capacity ptr initialized $$
      [Hcapacity Hptr Hlength Hstorage]
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
      rewriting [UInt32.add_comm 288 base]
    have Hgrow := hfunc98 (base + 288) base capacity ptr initialized shadow
      heapId storedCursor frontier history remaining output false
      (callerLocals :=
        ⟨[], [.i32 base, .i32 index, .i32 count,
          .i32 (UInt32.ofNat initialized.length), .i32 byte.toUInt32,
          .i32 aux5, .i32 aux6, .i32 aux7, .i32 aux8], []⟩)
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
          iapply twp_store_tail base index count byte aux5 aux6 aux7 aux8
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
    iapply twp_store_tail base index count byte aux5 aux6 aux7 aux8
      heapId capacity ptr initialized hbase.2 hroom
    isplitl_exacts [Hvec]
    iintro Hvec
    ihave Hnormal := BI.and_elim_l $$ Hcont
    iapply Hnormal $$ %capacity %ptr %storedCursor %frontier %history
      %shadow Hruntime Hsp Hreserve Hvec Hbump Hstreams
    ipureexact hpush

end Project.RustHashMap.ReadAll
