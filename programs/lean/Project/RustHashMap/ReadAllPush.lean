import Project.RustHashMap.ReadAllDefs
import CodeLib.SepLogic.SmallStepTotalLiftingBytesTerminal

/-!
# The input loop of the hash map drivers: one push

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

/-! ## One push -/

/-- The store of one byte into a vector with room, then the length update.
Local 3 holds the length and local 4 the byte. -/
theorem twp_store_tail [WasmSmallStepGS hlc Universal.State]
    (fm : FrameMap) (base index count : UInt32) (byte : UInt8)
    (auxTail : List Value)
    (heapId : GName) (capacity ptr : UInt32) (initialized : List UInt8)
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hbase : base.toNat + fm.frame.toNat < UInt32.size) (hwf : fm.WF)
    (hroom : initialized.length < capacity.toNat) :
    iprop(
      VecU8 heapId (base + fm.vecOff) capacity ptr initialized ∗
      (VecU8 heapId (base + fm.vecOff) capacity ptr (initialized ++ [byte]) -∗
        WP (.running
          ⟨⟨[], .i32 base :: .i32 (index + 1) :: .i32 count ::
              .i32 (UInt32.ofNat initialized.length) ::
              .i32 byte.toUInt32 :: auxTail, []⟩,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨[], .i32 base :: .i32 index :: .i32 count ::
            .i32 (UInt32.ofNat initialized.length) ::
            .i32 byte.toUInt32 :: auxTail, []⟩,
          storeTail fm ++ code, arity, remainder, controls, calls⟩ :
            Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hvec, Hcont⟩
  have hsize : UInt32.size = 4294967296 := rfl
  have hbounds := hwf
  unfold FrameMap.WF at hbounds
  obtain ⟨_, hvecFits, hframeLe, _⟩ := hbounds
  obtain ⟨hq4, hq8⟩ := vec_facts fm hwf
  have h292 : base + fm.vecOff + 4 = base + (fm.vecOff + 4) :=
    vec_addr fm base 4
  have h296 : base + fm.vecOff + 8 = base + (fm.vecOff + 8) :=
    vec_addr fm base 8
  obtain ⟨hb292, hb292_1, hb292_2, hb292_3⟩ :=
    cell_facts base (fm.vecOff + 4) (by omega)
  obtain ⟨hb296, hb296_1, hb296_2, hb296_3⟩ :=
    cell_facts base (fm.vecOff + 8) (by omega)
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
  wasm_twp_rebind twp_load32 (address := base) (offset := fm.vecOff + 4) ptr
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
  wasm_twp_rebind twp_store32 (address := base) (offset := fm.vecOff + 8)
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
  ihave Hvec : VecU8 heapId (base + fm.vecOff) capacity ptr
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
    (fm : FrameMap) (base index count : UInt32) (byte : UInt8)
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
      VecU8 heapId (base + fm.vecOff) capacity' ptr' (initialized ++ [byte]) -∗
      BumpHeap heapId storedCursor' frontier' history' -∗
      Streams remaining output false -∗
      ⌜PushVecFacts capacity' ptr' frontier'⌝ -∗
      WP (.running
        ⟨⟨[], .i32 base :: .i32 (index + 1) :: .i32 count ::
            .i32 (UInt32.ofNat initialized.length) ::
            .i32 byte.toUInt32 :: auxTail, []⟩,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) ∧
  (∀ remaining' : List UInt8,
    Streams remaining' output true -∗
      Φ (.trapped (.host OOM.trapMessage))))

/-- One push: the capacity guard, the possible `grow_one`, and the store.
Local 4 holds the byte. -/
theorem twp_push_byte [WasmSmallStepGS hlc Universal.State]
    (hfunc98 : Func98Spec (hlc := hlc))
    (fm : FrameMap) (base index count : UInt32) (byte : UInt8)
    (aux3 : UInt32) (auxTail : List Value)
    (heapId : GName) (capacity ptr : UInt32)
    (initialized shadow remaining output : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hbase : 16 ≤ base.toNat ∧ base.toNat + fm.frame.toNat < UInt32.size)
    (hwf : fm.WF)
    (hpush : PushVecFacts capacity ptr frontier) :
    iprop(
      RuntimeContext ∗
      StackPointer base ∗
      StackReserve (base - 16) shadow ∗
      VecU8 heapId (base + fm.vecOff) capacity ptr initialized ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output false ∗
      PushContinuation fm base index count byte auxTail heapId
        initialized remaining output code arity remainder controls calls
        s E Φ) ⊢
      WP (.running
        ⟨⟨[], .i32 base :: .i32 index :: .i32 count :: .i32 aux3 ::
            .i32 byte.toUInt32 :: auxTail, []⟩,
          .block 0 0 (growBody fm) :: (storeTail fm ++ code), arity,
          remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hvec, Hbump, Hstreams, Hcont⟩
  isimp only [PushContinuation] at Hcont
  have hsize : UInt32.size = 4294967296 := rfl
  have hbounds := hwf
  unfold FrameMap.WF at hbounds
  obtain ⟨_, hvecFits, hframeLe, _⟩ := hbounds
  obtain ⟨hq4, hq8⟩ := vec_facts fm hwf
  have h296 : base + fm.vecOff + 8 = base + (fm.vecOff + 8) :=
    vec_addr fm base 8
  obtain ⟨hb288, hb288_1, hb288_2, hb288_3⟩ :=
    cell_facts base fm.vecOff (by omega)
  obtain ⟨hb296, hb296_1, hb296_2, hb296_3⟩ :=
    cell_facts base (fm.vecOff + 8) (by omega)
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapacity, Hptr⟩, Hlength, Hstorage⟩
  ihave ⟨Hstorage, %hfits⟩ := VecStorage_length_le heapId capacity ptr
    initialized $$ Hstorage
  ihave Hlength := pointsTo_u32_address_eq h296 $$ Hlength
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  unfold growBody
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := base) (offset := fm.vecOff + 8)
    (UInt32.ofNat initialized.length) hb296 hb296_1
    hb296_2 hb296_3 with Hlength
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := base) (offset := fm.vecOff) capacity
    hb288 hb288_1 hb288_2 hb288_3 with Hcapacity
  ihave Hvec : VecU8 heapId (base + fm.vecOff) capacity ptr initialized $$
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
      rewriting [UInt32.add_comm fm.vecOff base]
    have Hgrow := hfunc98 (base + fm.vecOff) base capacity ptr initialized
      shadow
      heapId storedCursor frontier history remaining output false
      (callerLocals :=
        ⟨[], .i32 base :: .i32 index :: .i32 count ::
          .i32 (UInt32.ofNat initialized.length) ::
          .i32 byte.toUInt32 :: auxTail, []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .block, paramArity := 0, resultArity := 0,
          body := growBody fm, continuation := storeTail fm ++ code,
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
          iapply twp_store_tail fm base index count byte auxTail
            heapId (UInt32.ofNat (pushCapacity capacity.toNat)) newPtr
            initialized hbase.2 hwf hroom
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
    iapply twp_store_tail fm base index count byte auxTail
      heapId capacity ptr initialized hbase.2 hwf hroom
    isplitl_exacts [Hvec]
    iintro Hvec
    ihave Hnormal := BI.and_elim_l $$ Hcont
    iapply Hnormal $$ %capacity %ptr %storedCursor %frontier %history
      %shadow Hruntime Hsp Hreserve Hvec Hbump Hstreams
    ipureexact hpush

end Project.RustHashMap.ReadAll
