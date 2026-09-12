import Project.Mergesort.ExactDriver

/-!
# The input loop with a linear physical-page bound

The loop consumes its current exact page token at a reserve and retains the
updated one at the next back-edge. Its decreasing measure is unread bytes;
all heap, byte-vector, stream, and allocation-lineage facts are preserved.
-/

namespace Project.Mergesort.ExactReadLoop

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Contracts Project.Mergesort.Representations
open Project.Mergesort.DriverProof Project.Mergesort.MemoryBounds
open scoped Wasm.SmallStep.Outcome

/-- Physical capacity sufficient for every retained input-buffer allocation. -/
def readPageBound (original : List UInt32) : Nat :=
  max 17 ((inputFrontierBound (serialize original).length + 65535) / 65536)

theorem readPageBound_le_cap (original : List UInt32)
    (hfit : WorkArraysFit (serialize original).length) :
    readPageBound original ≤ Module.memoryHardCap := by
  unfold WorkArraysFit workArraysFrontierBound at hfit
  unfold readPageBound Module.memoryHardCap
  omega

/-- A bounded exact count, carried linearly through the loop. -/
def ReadPages [WasmSmallStepGS hlc Universal.State] (original : List UInt32) : HeapIProp :=
  iprop(memoryCapOwn 0 Module.memoryHardCap ∗ ∃ pages : Nat,
    ⌜pages ≤ readPageBound original⌝ ∗ memoryPagesHalf pages)

/-- Normal append returns the same linear page-bound resource. -/
def AppendContinuation
    [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32)
    (totalBytes : Nat) (current remaining : List UInt8)
    (initialized chunkBytes outputBytes : List UInt8)
    (heapId : GName)
    (output : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  ∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
    ∀ finalStoredCursor : UInt32, ∀ finalFrontier : Nat,
    ∀ finalHistory : AllocationHistory, ∀ finalShadow : List UInt8,
      ReadPages original -∗ RuntimeContext -∗
      StackPointer driverBase -∗
      StackReserve reserveBase finalShadow -∗
      ExportFrame heapId finalCapacity finalPtr (initialized ++ current)
        chunkBytes outputBytes -∗
      BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
      Streams remaining output false -∗
      ⌜BoundedGeometricVecFacts totalBytes (initialized.length + current.length)
        remaining.length finalCapacity finalPtr finalFrontier finalHistory⌝ -∗
      WP (.running
        ⟨func3AppendLocals finalPtr (UInt32.ofNat current.length)
            (UInt32.ofNat (initialized ++ current).length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }])

/-- Append the current chunk, growing the byte vector exactly when needed. -/
theorem append_current
    [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkTail outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (h : BoundedDriverFacts.ReadFacts original initialized current remaining
      capacity dataPtr frontier history)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(ReadPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output false ∗
      AppendContinuation original (serialize original).length current remaining
        initialized (current ++ chunkTail) outputBytes heapId output aux2 aux4 aux5 aux7 aux8 aux9
        aux10 stack code arity remainder controls calls s E Φ) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr (UInt32.ofNat current.length)
            (UInt32.ofNat initialized.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          .block 0 0 func3CapacityBody :: (func3AppendBody ++ code),
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  let totalBytes := (serialize original).length
  have hfacts : current.length = min 256 (current.length + remaining.length) ∧
      0 < current.length ∧ current.length % 4 = 0 ∧
      totalBytes = initialized.length + current.length + remaining.length ∧
      BoundedGeometricVecFacts totalBytes initialized.length
        (current.length + remaining.length) capacity dataPtr frontier history :=
    ⟨h.chunk_shape, h.chunk_positive, h.chunk_mod, by
      dsimp only [totalBytes]; rw [h.partition]; simp only [List.length_append], h.bounded⟩
  have hlayout := GeometricVecFacts.reserveLayout totalBytes
    initialized.length (current.length + remaining.length) current.length
    capacity dataPtr frontier history hfacts.2.2.2.2.1
    hfacts.1 hfacts.2.1
  dsimp only at hlayout
  have hinitializedCapacity : initialized.length ≤ capacity.toNat := by
    rcases hfacts.2.2.2.2.1 with hinitial | hshort | hlarge
    · omega
    · omega
    · rcases hlarge with
        ⟨_exponent, _hlower, _hupper, _hcapacity, hlength,
          _htotal, _hptr, _hfrontier, _hhistory⟩
      exact hlength
  have hinitializedWord :
      (UInt32.ofNat initialized.length).toNat = initialized.length :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hcurrentWord :
      (UInt32.ofNat current.length).toNat = current.length :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hinitializedLe : UInt32.ofNat initialized.length ≤ capacity := by
    simpa only [UInt32.le_iff_toNat_le_toNat, hinitializedWord] using hinitializedCapacity
  have hspareWord :
      (capacity - UInt32.ofNat initialized.length).toNat =
        capacity.toNat - initialized.length := by
    rw [UInt32.toNat_sub_of_le _ _ hinitializedLe, hinitializedWord]
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  isimp only [AppendContinuation] at Hcont
  isimp only [ExportFrame, VecU8, RawVecHeader] at Hframe
  icases Hframe with
    ⟨⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩,
      Hchunk, Houtput, %hframeLengths⟩
  iapply (twp_block (body := func3CapacityBody)
    (code := func3AppendBody ++ code))
  simp only [func3CapacityBody]
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hcapacity' : pointsTo_u32 0 (driverBase + 0) capacity $$ [Hcapacity]
  · simp only [UInt32.add_zero]
    iexact Hcapacity
  wasm_twp_bind twp_load32 (address := driverBase) (offset := 0) capacity
      (by decide) (by decide) (by decide) (by decide) with Hcapacity' => Hcapacity
  isimp only [UInt32.add_zero] at Hcapacity
  wasm_twp_pures [twp_localGet twp_sub]
  by_cases hfits : current.length ≤ capacity.toNat - initialized.length
  · iapply twp_leU (result := 1)
      (by
        have hfitsWord :
            UInt32.ofNat current.length ≤
              capacity - UInt32.ofNat initialized.length := by
          simpa only [UInt32.le_iff_toNat_le_toNat, hcurrentWord, hspareWord] using hfits
        simp [hfitsWord])
    iapply twp_brIf (by decide) (by rfl)
    simp only [func3AppendBody, func3AppendLocals, List.take_zero,
      List.drop_zero, List.nil_append]
    ihave Hframe : ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes $$
        [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
    · unfold ExportFrame VecU8 RawVecHeader
      iframe_pureexact hframeLengths
    have Happend := twp_func3_append_without_reserve heapId capacity dataPtr
      initialized current chunkTail outputBytes hfacts.2.1 hfits hlayout.1
      aux2 aux4 aux5 aux7 aux8 aux9 aux10
      (stack := stack) (code := code) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls)
      (s := s) (E := E) (Φ := Φ)
    simp only [func3AppendLocals, func3AppendBody] at Happend
    iapply_frame_intro Happend as Hframe
    have hgeo := BoundedGeometricVecFacts.appendWithoutReserve totalBytes
      initialized.length current.length remaining.length capacity dataPtr
      frontier history hfacts.2.2.2.2 hfacts.2.1 hfits
    ihave Hnormal := Hcont
    iapply Hnormal $$ %capacity %dataPtr %storedCursor %frontier %history
      %shadow Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams
    · ipureexact hgeo
  · iapply twp_leU (result := 0)
      (by
        have hfitsWord :
            ¬UInt32.ofNat current.length ≤
              capacity - UInt32.ofNat initialized.length := by
          simpa only [UInt32.le_iff_toNat_le_toNat, hcurrentWord, hspareWord] using hfits
        simp [hfitsWord])
    wasm_twp_pures [twp_brIfZero] using [func3AppendLocals, List.drop_zero]
    ihave Hframe : ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes $$
        [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
    · unfold ExportFrame VecU8 RawVecHeader
      iframe_pureexact hframeLengths
    isimp only [ReadPages] at Hpages
    icases Hpages with ⟨Hcap, %pages, %hpages, Hexact⟩
    have HreserveStep := ExactDriver.twp_func3_reserve_exact original current remaining capacity
      dataPtr initialized (current ++ chunkTail) outputBytes shadow heapId
      storedCursor frontier history output false aux2 aux4 aux5 aux7 aux8 aux9 aux10
      h pages hmode (hpages.trans (readPageBound_le_cap original hfit)) hfit
      (Nat.lt_of_not_ge hfits)
      (stack := stack)
      (code := [.localGet 0, .load32 4, .localSet 1,
        .localGet 0, .load32 8, .localSet 6])
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .block, paramArity := 0, resultArity := 0,
          body := func3CapacityBody,
          continuation := func3AppendBody ++ code,
          belowStack := stack } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3AppendLocals, func3CapacityBody, List.cons_append,
      List.nil_append] at HreserveStep
    iapply HreserveStep
    isplitl_exacts [Hruntime Hcap Hexact Hsp Hreserve Hframe Hbump Hstreams]
    iintro %newPtr %finish %finalHistory Hruntime Hcap Hexact Hsp Hreserve Hframe Hbump %hpure Hstreams
    ihave Hpages : ReadPages original $$ [Hcap Hexact]
    · unfold ReadPages
      iframe Hcap
      iexists max pages (allocatorRequiredPages finish).toNat
      isplitl_pureexact (hpure.2.2.2.trans (max_le hpages (le_max_right _ _)))
      iexact Hexact
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    have Hreload := twp_func3_reload_vec_fields heapId
      (UInt32.ofNat
        (selectedCapacity initialized.length current.length
          capacity.toNat)) dataPtr newPtr initialized
      (current ++ chunkTail) outputBytes
      (UInt32.ofNat current.length) aux2 aux4 aux5 aux7 aux8 aux9
      aux10
      (stack := stack) (code := []) (arity := arity)
      (remainder := remainder)
      (controls :=
        { kind := .block, paramArity := 0, resultArity := 0,
          body := func3CapacityBody,
          continuation := func3AppendBody ++ code,
          belowStack := stack } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3AppendLocals, func3CapacityBody,
      List.cons_append, List.nil_append] at Hreload
    iapply_frame_intro Hreload as Hframe
    wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
    have hnewCapacityWord :
        (UInt32.ofNat
          (selectedCapacity initialized.length current.length
            capacity.toNat)).toNat =
          selectedCapacity initialized.length current.length
            capacity.toNat :=
      UInt32.toNat_ofNat_of_lt' hlayout.2.1
    have hfitsNew :
        current.length ≤
          (UInt32.ofNat
            (selectedCapacity initialized.length current.length
              capacity.toNat)).toNat - initialized.length := by
      rw [hnewCapacityWord]
      unfold selectedCapacity
      omega
    have Happend := twp_func3_append_without_reserve heapId
      (UInt32.ofNat
        (selectedCapacity initialized.length current.length
          capacity.toNat)) newPtr initialized current chunkTail
      outputBytes hfacts.2.1 hfitsNew hlayout.1 aux2 aux4 aux5 aux7
      aux8 aux9 aux10
      (stack := stack) (code := code) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls)
      (s := s) (E := E) (Φ := Φ)
    simp only [func3AppendLocals] at Happend
    iapply_frame_intro Happend as Hframe
    ihave Hnormal := Hcont
    iapply Hnormal $$
      %(UInt32.ofNat
        (selectedCapacity initialized.length current.length
          capacity.toNat)) %newPtr %finish %finish.toNat %finalHistory
      %(reserveSuccessShadow shadow newPtr
        (UInt32.ofNat
          (selectedCapacity initialized.length current.length
            capacity.toNat))) Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams
    · ipureexact hpure.2.2.1
/-- The EOF and back-edge continuations both retain exact page ownership. -/
def IterationContinuation
    [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32)
    (totalBytes : Nat) (current remaining : List UInt8)
    (initialized chunkBytes outputBytes : List UInt8)
    (heapId : GName)
    (output : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let count := min 256 remaining.length
  let nextCurrent := remaining.take count
  let nextRemaining := remaining.drop count
  let nextTail := chunkBytes.drop count
  iprop(
    (∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
      ∀ finalStoredCursor : UInt32, ∀ finalFrontier : Nat,
      ∀ finalHistory : AllocationHistory, ∀ finalShadow : List UInt8,
        ReadPages original -∗ RuntimeContext -∗
        StackPointer driverBase -∗
        StackReserve reserveBase finalShadow -∗
        ExportFrame heapId finalCapacity finalPtr
          (initialized ++ current) chunkBytes outputBytes -∗
        BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
        Streams [] output false -∗
        ⌜remaining = [] ∧
          BoundedGeometricVecFacts totalBytes
            (initialized.length + current.length) 0 finalCapacity finalPtr
            finalFrontier finalHistory⌝ -∗
        WP (.running
          ⟨func3AppendLocals finalPtr 0
              (UInt32.ofNat (initialized ++ current).length)
              aux2 aux4 aux5 aux7 aux8 aux9 aux10 (.i32 1 :: stack),
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ∧
      (∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
        ∀ finalStoredCursor : UInt32, ∀ finalFrontier : Nat,
        ∀ finalHistory : AllocationHistory, ∀ finalShadow : List UInt8,
          ReadPages original -∗ RuntimeContext -∗
          StackPointer driverBase -∗
          StackReserve reserveBase finalShadow -∗
          ExportFrame heapId finalCapacity finalPtr
            (initialized ++ current) (nextCurrent ++ nextTail) outputBytes -∗
          BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
          Streams nextRemaining output false -∗
          ⌜nextCurrent.length = min 256
                (nextCurrent.length + nextRemaining.length) ∧
            0 < nextCurrent.length ∧ nextCurrent.length ≤ 256 ∧
            nextCurrent.length % 4 = 0 ∧
            nextRemaining.length % 4 = 0 ∧
            remaining = nextCurrent ++ nextRemaining ∧
            totalBytes = (initialized ++ current).length +
              nextCurrent.length + nextRemaining.length ∧
            BoundedGeometricVecFacts totalBytes
              (initialized.length + current.length)
              (nextCurrent.length + nextRemaining.length)
              finalCapacity finalPtr finalFrontier finalHistory ∧
            nextCurrent.length + nextRemaining.length <
              current.length + remaining.length⌝ -∗
          WP (.running
            ⟨func3AppendLocals finalPtr (UInt32.ofNat count)
                (UInt32.ofNat (initialized ++ current).length)
                aux2 aux4 aux5 aux7 aux8 aux9 aux10 (.i32 0 :: stack),
              code, arity, remainder, controls, calls⟩ : Expr Universal.State)
            @ s; E [{ Φ }]))

/-- Append, then perform the actual next read and EOF classification. -/
theorem read_loop_iteration
    [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkTail outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (h : BoundedDriverFacts.ReadFacts original initialized current remaining
      capacity dataPtr frontier history)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(ReadPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output false ∗
      IterationContinuation original (serialize original).length current remaining
        initialized (current ++ chunkTail) outputBytes heapId output aux2 aux4 aux5 aux7 aux8 aux9
        aux10 stack code arity remainder controls calls s E Φ) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr (UInt32.ofNat current.length)
            (UInt32.ofNat initialized.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          [.localGet 3, .const 257, .geU, .br_if 1,
            .block 0 0 func3CapacityBody] ++ func3AppendBody ++
              func3ReadClassifyBody ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  let totalBytes := (serialize original).length
  have hfacts : current.length = min 256 (current.length + remaining.length) ∧
      0 < current.length ∧ current.length ≤ 256 ∧ current.length % 4 = 0 ∧
      remaining.length % 4 = 0 ∧
      totalBytes = initialized.length + current.length + remaining.length ∧
      BoundedGeometricVecFacts totalBytes initialized.length
        (current.length + remaining.length) capacity dataPtr frontier history :=
    ⟨h.chunk_shape, h.chunk_positive, h.chunk_shape ▸ min_le_left _ _,
      h.chunk_mod, h.remaining_mod, by
      dsimp only [totalBytes]; rw [h.partition]; simp only [List.length_append], h.bounded⟩
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  isimp only [IterationContinuation] at Hcont
  have Hguard := twp_func3_count_guard dataPtr current.length
    initialized.length aux2 aux4 aux5 aux7 aux8 aux9 aux10 hfacts.2.2.1
    (stack := stack)
    (code := [.block 0 0 func3CapacityBody] ++ func3AppendBody ++
      func3ReadClassifyBody ++ code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [List.cons_append, List.nil_append] at Hguard ⊢
  iapply Hguard
  have Happend := append_current original current remaining
    capacity dataPtr initialized chunkTail outputBytes shadow heapId
    storedCursor frontier history output aux2 aux4 aux5 aux7 aux8 aux9 aux10
    h hmode hfit
    (stack := stack) (code := func3ReadClassifyBody ++ code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  rw [List.append_assoc func3AppendBody func3ReadClassifyBody code]
  iapply Happend
  isplitl_exacts [Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams]
  unfold AppendContinuation
  iintro %finalCapacity %finalPtr %finalStoredCursor %finalFrontier
    %finalHistory %finalShadow Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams
    %hgeo
  have Hread := twp_func3_read_and_classify heapId finalCapacity finalPtr
    (initialized ++ current) (current ++ chunkTail) outputBytes remaining
    output hfacts.2.2.2.2.1 (UInt32.ofNat current.length)
    aux2 aux4 aux5 aux7 aux8 aux9 aux10
    (stack := stack) (code := code) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [List.cons_append, List.nil_append] at Hread
  simp only [func3ReadClassifyBody, List.cons_append, List.nil_append]
  iapply Hread
  isplitl_exacts [Hruntime Hstreams Hframe]
  isplit
  · iintro Hruntime Hstreams Hframe %hremainingEmpty
    ihave Hdone := BI.and_elim_l $$ Hcont
    iapply Hdone $$ %finalCapacity %finalPtr %finalStoredCursor
      %finalFrontier %finalHistory %finalShadow Hpages Hruntime Hsp Hreserve Hframe
      Hbump Hstreams
    · ipureexact ⟨hremainingEmpty, by simpa [hremainingEmpty] using hgeo⟩
  · iintro Hruntime Hstreams Hframe %hnext
    have hremainingLength :
        remaining.length =
          (remaining.take (min 256 remaining.length)).length +
            (remaining.drop (min 256 remaining.length)).length := by
      rw [← List.length_append,
        List.take_append_drop (min 256 remaining.length) remaining]
    have hgeoNext :
        BoundedGeometricVecFacts totalBytes
          (initialized.length + current.length)
          ((remaining.take (min 256 remaining.length)).length +
            (remaining.drop (min 256 remaining.length)).length)
          finalCapacity finalPtr finalFrontier finalHistory := by
      simpa only [← hremainingLength] using hgeo
    have htotalNext :
        totalBytes = (initialized ++ current).length +
          (remaining.take (min 256 remaining.length)).length +
          (remaining.drop (min 256 remaining.length)).length := by
      have htotal := hfacts.2.2.2.2.2.1
      simp only [List.length_append]; omega
    have hreadShape :
        (remaining.take (min 256 remaining.length)).length =
          min 256
            ((remaining.take (min 256 remaining.length)).length +
              (remaining.drop (min 256 remaining.length)).length) := by
      simpa only [← hremainingLength] using hnext.2.1
    have hmeasure :
        (remaining.take (min 256 remaining.length)).length +
            (remaining.drop (min 256 remaining.length)).length <
          current.length + remaining.length := by omega
    have hnextPositive :
        0 < (remaining.take (min 256 remaining.length)).length := by
      simpa only [hnext.2.1] using hnext.2.2.1
    have hnextBound :
        (remaining.take (min 256 remaining.length)).length ≤ 256 := by
      simpa only [hnext.2.1] using hnext.2.2.2.1
    have hnextMod :
        (remaining.take (min 256 remaining.length)).length % 4 = 0 := by
      simpa only [hnext.2.1] using hnext.2.2.2.2.1
    ihave Hnext := BI.and_elim_r $$ Hcont
    iapply Hnext $$ %finalCapacity %finalPtr %finalStoredCursor
      %finalFrontier %finalHistory %finalShadow Hpages Hruntime Hsp Hreserve Hframe
      Hbump Hstreams
    · ipureexact ⟨hreadShape, hnextPositive, hnextBound,
        hnextMod, hnext.2.2.2.2.2.1, hnext.2.2.2.2.2.2,
        htotalNext,
        hgeoNext, hmeasure⟩
/-- The complete input phase returns all bytes and the bounded page token. -/
def ReadLoopContinuation
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  ∀ completed : List UInt8, ∀ chunkBytes : List UInt8,
    ∀ finalShadow : List UInt8,
    ∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
    ∀ finalStoredCursor : UInt32,
    ∀ finalFrontier : Nat, ∀ finalHistory : AllocationHistory,
      ReadPages original -∗ RuntimeContext -∗
      StackPointer driverBase -∗
      StackReserve reserveBase finalShadow -∗
      ExportFrame heapId finalCapacity finalPtr completed chunkBytes
        outputBytes -∗
      BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
      Streams [] [] false -∗
      ⌜serialize original = completed ∧
        BoundedGeometricVecFacts (serialize original).length completed.length 0
          finalCapacity finalPtr finalFrontier finalHistory⌝ -∗
      WP (.running
        ⟨func3AppendLocals finalPtr 0 (UInt32.ofNat completed.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 [],
          afterLoop, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }])

/-- Allocation lineage and exact page ownership at a generated loop header. -/
def ReadLoopInv
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (state : Func3ReadLoopState) : HeapIProp := iprop(ReadPages original ∗
  RuntimeContext ∗
  StackPointer driverBase ∗
  StackReserve reserveBase state.shadow ∗
  ExportFrame heapId state.capacity state.dataPtr state.initialized
    (state.current ++ state.chunkTail) outputBytes ∗
  BumpHeap heapId state.storedCursor state.frontier state.history ∗
  Streams state.remaining [] false ∗
  ⌜serialize original =
      state.initialized ++ state.current ++ state.remaining ∧
    state.current.length =
      min 256 (state.current.length + state.remaining.length) ∧
    0 < state.current.length ∧ state.current.length ≤ 256 ∧
    state.current.length % 4 = 0 ∧ state.remaining.length % 4 = 0 ∧
    BoundedGeometricVecFacts (serialize original).length state.initialized.length
      (state.current.length + state.remaining.length)
      state.capacity state.dataPtr state.frontier state.history⌝ ∗
  ReadLoopContinuation heapId original outputBytes
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 afterLoop arity remainder controls
    calls s E Φ)

/-- The actual loop terminates, with a page token carried through every reserve. -/
theorem read_loop
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (initial : Func3ReadLoopState)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    ReadLoopInv heapId original outputBytes
        aux2 aux4 aux5 aux7 aux8 aux9 aux10 afterLoop arity remainder controls
        calls s E Φ initial ⊢
      WP (.running
        ⟨func3ReadLoopLocals aux2 aux4 aux5 aux7 aux8 aux9 aux10 initial,
          [.loop 0 0 func3ReadLoopBody], arity, remainder,
          func3ReadInnerFrame :: func3ReadPhaseFrame afterLoop :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Func3ReadLoopState)
    (measure := fun state => state.current.length + state.remaining.length)
    (locals := func3ReadLoopLocals aux2 aux4 aux5 aux7 aux8 aux9 aux10)
    (I := ReadLoopInv heapId original outputBytes
      aux2 aux4 aux5 aux7 aux8 aux9 aux10 afterLoop arity remainder controls
      calls s E Φ)
    (initial := initial)
    (initialLocals := func3ReadLoopLocals
      aux2 aux4 aux5 aux7 aux8 aux9 aux10 initial)
    (body := func3ReadLoopBody) (code := [])
    (paramArity := 0) (resultArity := 0)
    (arity := arity) (remainder := remainder)
    (controls := func3ReadInnerFrame ::
      func3ReadPhaseFrame afterLoop :: controls)
    (calls := calls) (belowStack := []) rfl rfl
  · intro state
    simp only [ReadLoopInv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, %hfacts, Hfinish⟩
    isimp only [ReadLoopContinuation] at Hfinish
    have Hiteration := read_loop_iteration original state.current state.remaining state.capacity
      state.dataPtr state.initialized state.chunkTail outputBytes state.shadow
      heapId state.storedCursor state.frontier state.history []
      aux2 aux4 aux5 aux7 aux8 aux9 aux10
      ⟨hfacts.1, hfacts.2.1, hfacts.2.2.1, hfacts.2.2.2.2.1,
        hfacts.2.2.2.2.2.1, hfacts.2.2.2.2.2.2⟩ hmode hfit
      (stack := []) (code := [.br_if 2, .br 0])
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .loop, paramArity := 0, resultArity := 0,
          body := func3ReadLoopBody, continuation := [], belowStack := [] } ::
        func3ReadInnerFrame :: func3ReadPhaseFrame afterLoop :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3ReadLoopBody, List.cons_append, List.nil_append] at Hiteration
    simp only [func3ReadLoopBody, func3ReadLoopLocals,
      List.cons_append, List.nil_append]
    iapply Hiteration
    isplitl_exacts [Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams]
    unfold IterationContinuation
    isplit
    · iintro %finalCapacity %finalPtr %finalStoredCursor %finalFrontier
        %finalHistory %finalShadow Hpages Hruntime Hsp Hreserve Hframe Hbump
        Hstreams %hdone
      simp only [func3AppendLocals]
      iapply twp_brIf (condition := 1) (depth := 2) (arity := arity)
        (code := [.br 0]) (targetCode := afterLoop)
        (targetControl := controls) (targetValues := [])
        (by decide) (by rfl)
      ihave Hnormal := Hfinish
      iapply Hnormal $$ %(state.initialized ++ state.current)
        %(state.current ++ state.chunkTail) %finalShadow %finalCapacity
        %finalPtr %finalStoredCursor %finalFrontier %finalHistory Hpages Hruntime
        Hsp Hreserve Hframe Hbump Hstreams
      · ipureintro
        constructor
        · simpa [hdone.1, List.append_assoc] using hfacts.1
        · simpa only [List.length_append] using hdone.2
    · iintro %finalCapacity %finalPtr %finalStoredCursor %finalFrontier
        %finalHistory %finalShadow Hpages Hruntime Hsp Hreserve Hframe Hbump
        Hstreams %hnext
      let next : Func3ReadLoopState :=
        { capacity := finalCapacity
          dataPtr := finalPtr
          initialized := state.initialized ++ state.current
          current := state.remaining.take (min 256 state.remaining.length)
          remaining := state.remaining.drop (min 256 state.remaining.length)
          chunkTail :=
            (state.current ++ state.chunkTail).drop
              (min 256 state.remaining.length)
          shadow := finalShadow
          storedCursor := finalStoredCursor
          frontier := finalFrontier
          history := finalHistory }
      simp only [func3AppendLocals]
      iapply twp_brIfZero (depth := 2) (arity := arity)
      ihave Hback := Hrec $$ %next %hnext.2.2.2.2.2.2.2.2
      isimp only [next, func3ReadLoopLocals, func3AppendLocals] at Hback
      iapply twp_br (depth := 0) (arity := arity) (code := [])
        (targetCode := func3ReadLoopBody)
        (targetControl :=
          { kind := .loop, paramArity := 0, resultArity := 0,
            body := func3ReadLoopBody, continuation := [], belowStack := [] } ::
          func3ReadInnerFrame :: func3ReadPhaseFrame afterLoop :: controls)
        (targetValues := []) (by rfl)
      simp only [func3ReadLoopBody, List.cons_append, List.nil_append]
      have htakeLength :
          (state.remaining.take (min 256 state.remaining.length)).length =
            min 256 state.remaining.length := by
        simp
      rw [← congrArg UInt32.ofNat htakeLength]
      iapply Hback
      isplitl_exacts [Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams]
      isplitl_pureexact (by
        have hserializeNext :
            serialize original =
              (state.initialized ++ state.current) ++
                state.remaining.take (min 256 state.remaining.length) ++
                state.remaining.drop (min 256 state.remaining.length) := by
          calc
            serialize original =
                (state.initialized ++ state.current) ++
                  state.remaining := hfacts.1
            _ = (state.initialized ++ state.current) ++
                  (state.remaining.take (min 256 state.remaining.length) ++
                    state.remaining.drop
                      (min 256 state.remaining.length)) :=
              congrArg
                (fun tail => (state.initialized ++ state.current) ++ tail)
                hnext.2.2.2.2.2.1
            _ = (state.initialized ++ state.current) ++
                  state.remaining.take (min 256 state.remaining.length) ++
                  state.remaining.drop (min 256 state.remaining.length) := by
              simp only [List.append_assoc]
        have hgeoNext :
            BoundedGeometricVecFacts (serialize original).length
              (state.initialized ++ state.current).length
              ((state.remaining.take (min 256 state.remaining.length)).length +
                (state.remaining.drop (min 256 state.remaining.length)).length)
              finalCapacity finalPtr finalFrontier finalHistory := by
          simpa only [List.length_append] using
            hnext.2.2.2.2.2.2.2.1
        exact ⟨hserializeNext, hnext.1, hnext.2.1, hnext.2.2.1,
          hnext.2.2.2.1, hnext.2.2.2.2.1,
          hgeoNext⟩)
      unfold ReadLoopContinuation
      simp only [func3AppendLocals]
      iexact Hfinish
/-- Execute the enclosing generated phase blocks around the input loop. -/
theorem read_phase
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (initial : Func3ReadLoopState)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    ReadLoopInv heapId original outputBytes
        aux2 aux4 aux5 aux7 aux8 aux9 aux10 afterLoop arity remainder controls
        calls s E Φ initial ⊢
      WP (.running
        ⟨func3ReadLoopLocals aux2 aux4 aux5 aux7 aux8 aux9 aux10 initial,
          .block 0 0 func3ReadPhaseBody :: afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro Hinv
  wasm_twp_pures [twp_block] using [func3ReadPhaseBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block] using [func3ReadLoopBlockBody]
  have Hloop := read_loop heapId original outputBytes
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 initial hmode hfit
    (afterLoop := afterLoop) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3ReadInnerFrame, func3ReadPhaseFrame, func3ReadPhaseBody,
    func3ReadLoopBlockBody, func3ReadLoopLocals, func3AppendLocals,
    List.cons_append, List.nil_append] at Hloop
  simp only [func3ReadLoopLocals, func3AppendLocals, List.drop_zero]
  iapply_exact Hloop with Hinv

/-- Start the growing input phase with the actual first host read. -/
theorem first_read_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes shadow : List UInt8)
    (horiginal : original ≠ [])
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(ReadPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      ReadLoopContinuation heapId original outputBytes
        4 0 0 0 0 0 0 afterLoop arity remainder controls calls s E Φ) ⊢
      WP (.running
        ⟨func3InitializedLocals, func3InitialReadBody,
          arity, remainder, func3InitialReadFrame afterLoop :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  let input := serialize original
  let count := min 256 input.length
  let current := input.take count
  let remaining := input.drop count
  let chunkTail := (List.replicate 256 (0 : UInt8)).drop count
  have hinputLength : input.length = 4 * original.length := by
    dsimp only [input]; exact serialize_length original
  have hinputPositive : 0 < input.length := by
    have horiginalPositive : 0 < original.length := by
      by_contra hzero
      exact horiginal (List.eq_nil_of_length_eq_zero (by omega))
    omega
  have hinputMod : input.length % 4 = 0 := by omega
  have hsplit := readChunk_mod_four input hinputMod
  dsimp only at hsplit
  have hcountPositive : 0 < count := by
    dsimp only [count]; omega
  have hcountSize : count < UInt32.size := by
    norm_num [UInt32.size]; omega
  have hcountWord : (UInt32.ofNat count).toNat = count :=
    UInt32.toNat_ofNat_of_lt' hcountSize
  have hcountNonzero : UInt32.ofNat count ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero; rw [hcountWord] at hzeroNat
    simp only [UInt32.toNat_zero] at hzeroNat; omega
  have hremainingLength :
      input.length = current.length + remaining.length := by
    dsimp only [current, remaining]
    rw [← List.length_append, List.take_append_drop count input]
  have hcurrentLength : current.length = count := hsplit.1
  have hcurrentShape :
      current.length = min 256 (current.length + remaining.length) := by
    simpa only [← hremainingLength] using hsplit.1
  have hcurrentPositive : 0 < current.length := by simpa only [hcurrentLength] using hcountPositive
  have hcurrentBound : current.length ≤ 256 := by
    rw [hcurrentLength]; exact min_le_left 256 input.length
  have hcurrentMod : current.length % 4 = 0 := by simpa only [hcurrentLength] using hsplit.2.1
  have hserializeSplit :
      serialize original = [] ++ current ++ remaining := by
    calc
      serialize original = input := rfl
      _ = current ++ remaining := (List.take_append_drop count input).symm
      _ = [] ++ current ++ remaining := by simp
  have hgeo :
      BoundedGeometricVecFacts input.length 0
        (current.length + remaining.length) 0 1 heapBase.toNat
        AllocationHistory.empty := by
    simpa only [input, current, remaining, count, List.length_nil] using
      (BoundedDriverFacts.ReadFacts.initial original horiginal).bounded
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hfinish⟩
  have Hread := twp_func3_read_chunk heapId 0 1 []
    (List.replicate 256 0) outputBytes input [] false []
    [.i32 driverBase, .i32 0, .i32 4, .i32 0, .i32 0, .i32 0,
      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
    rfl
    (stack := [])
    (code := [.localTee 3, .br_if 0] ++ func3EmptyInputSuffix)
    (arity := arity) (remainder := remainder)
    (controls := func3InitialReadFrame afterLoop :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3InitialReadBody, func3InitialReadPrefix,
    func3EmptyInputSuffix, func3InitializedLocals,
    List.cons_append, List.nil_append] at Hread ⊢
  iapply Hread
  isplitl_exacts [Hruntime Hstreams Hframe]
  iintro Hruntime Hstreams Hframe %_hcountBound
  iapply twp_localTee
      (locals' := func3AppendLocals 0 (UInt32.ofNat count) 0
        4 0 0 0 0 0 0 [.i32 (UInt32.ofNat count)])
      (by simp [func3AppendLocals, count])
  simp only [func3AppendLocals]
  iapply twp_brIf (condition := UInt32.ofNat count) (depth := 0)
    (arity := arity)
    (code := [.const 1, .localSet 4, .const 1, .localSet 5, .br 1])
    (targetCode := func3AfterInitialRead afterLoop)
    (targetControl := controls) (targetValues := []) hcountNonzero (by rfl)
  simp only [func3AfterInitialRead, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_const twp_localSet] using [List.length, List.set]
  wasm_twp_pures [twp_const twp_localSet] using [List.length, List.set]
  let initial : Func3ReadLoopState :=
    { capacity := 0
      dataPtr := 1
      initialized := []
      current := current
      remaining := remaining
      chunkTail := chunkTail
      shadow := shadow
      storedCursor := 0
      frontier := heapBase.toNat
      history := AllocationHistory.empty }
  have Hphase := read_phase heapId original outputBytes
    4 0 0 0 0 0 0 initial hmode hfit
    (afterLoop := afterLoop) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [initial, func3ReadLoopLocals, func3AppendLocals,
    hcurrentLength, List.length_nil, UInt32.reduceOfNat] at Hphase
  iapply Hphase
  unfold ReadLoopInv
  isplitl_exacts [Hpages Hruntime Hsp Hreserve Hframe Hbump Hstreams]
  isplitl_pureexact ⟨hserializeSplit, hcurrentShape, hcurrentPositive,
      hcurrentBound, hcurrentMod, hsplit.2.2, by
        change BoundedGeometricVecFacts input.length 0
          (current.length + remaining.length) 0 1 heapBase.toNat
          AllocationHistory.empty
        exact hgeo⟩
  · iexact Hfinish

/-- Enter the exact generated initial-read block for a nonempty public input.
The block body still contains the empty-input suffix, but the preceding theorem
proves the nonzero read count takes the block branch before that suffix. -/
theorem initial_read_block_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes shadow : List UInt8)
    (horiginal : original ≠ [])
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(ReadPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      ReadLoopContinuation heapId original outputBytes
        4 0 0 0 0 0 0 afterLoop arity remainder controls calls s E Φ) ⊢
      WP (.running
        ⟨func3InitializedLocals,
          .block 0 0 func3InitialReadBody :: func3AfterInitialRead afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro Hresources
  wasm_twp_pures [twp_block]
  have Hread := first_read_nonempty heapId original
    outputBytes shadow horiginal hmode hfit
    (afterLoop := afterLoop) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3InitialReadFrame, func3InitializedLocals] at Hread
  simp only [func3InitializedLocals, List.drop_zero]
  iapply_exact Hread with Hresources

end Project.Mergesort.ExactReadLoop
