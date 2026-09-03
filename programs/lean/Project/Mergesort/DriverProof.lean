import Project.Mergesort.ContractProofs

set_option maxRecDepth 1048576

/-!
# Generated merge-sort driver proof

This file proves `func3` in phases.  The first phase below consumes the raw
entry stack region and executes the generated prologue, producing the exact
empty `ExportFrame` representation used by the reviewed driver contract.
-/

namespace Project.Mergesort.DriverProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

/-- The first instruction after the generated stack/Vec initialization. -/
private def func3AfterInit : Program :=
  Project.Mergesort.func3.drop 21

/-- Exact locals after the generated stack/Vec initialization. -/
private def func3InitializedLocals : Locals :=
  { locals :=
      [.i32 driverBase, .i32 0, .i32 4, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] }

/-- Two adjacent little-endian 32-bit cells are the corresponding 64-bit
cell.  The generated prologue uses a single `i64.store` for the capacity and
pointer fields, while the authoritative Vec representation exposes them as
two `i32` cells. -/
private theorem pointsTo_u32_pair_as_u64
    [WasmHeapGS Universal.State]
    (ptr lo hi : UInt32) :
    iprop(pointsTo_u32 0 ptr lo ∗ pointsTo_u32 0 (ptr + 4) hi) ⊣⊢
      pointsTo_u64 0 ptr
        (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) := by
  let combined : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
  have h0 : u64Byte combined 0 = u32Byte lo 0 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h1 : u64Byte combined 1 = u32Byte lo 1 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h2 : u64Byte combined 2 = u32Byte lo 2 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h3 : u64Byte combined 3 = u32Byte lo 3 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h4 : u64Byte combined 4 = u32Byte hi 0 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h5 : u64Byte combined 5 = u32Byte hi 1 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h6 : u64Byte combined 6 = u32Byte hi 2 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  have h7 : u64Byte combined 7 = u32Byte hi 3 := by
    simp [combined, u64Byte, u32Byte]
    bv_decide
  change iprop(pointsTo_u32 0 ptr lo ∗ pointsTo_u32 0 (ptr + 4) hi) ⊣⊢
    pointsTo_u64 0 ptr combined
  unfold pointsTo_u32 pointsTo_u64
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [show ptr + 4 + 1 = ptr + 5 by bv_decide]
  rw [show ptr + 4 + 2 = ptr + 6 by bv_decide]
  rw [show ptr + 4 + 3 = ptr + 7 by bv_decide]
  constructor
  · iintro ⟨Hlo, Hhi⟩
    icases Hlo with ⟨H0, H1, H2, H3⟩
    icases Hhi with ⟨H4, H5, H6, H7⟩
    iframe
  · iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
    iframe

/-- The offset-zero form of `twp_store64`, stated without the syntactic
`address + 0` in its owned cell. -/
private theorem twp_store64_zero
    {hlc : HasLC} {α : Type} [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)}
    {params localValues values : List Value}
    {address : UInt32} {value : UInt64}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldWord : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    pointsTo_u64 0 address oldWord -∗
    (pointsTo_u64 0 address value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues,
        .i64 value :: .i32 address :: values⟩,
      .store64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  simpa only [UInt32.add_zero, Nat.add_zero] using
    (twp_store64 (α := α) (Terminal := ObservableOutcome)
      (address := address) (offset := 0) (value := value) oldWord
      (by simp) (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4) (by simpa using h5)
      (by simpa using h6) (by simpa using h7))

/-- Execute one generated chunk read through the proved `func10` contract.
The surrounding driver loop keeps the Vec and output-slot ownership framed;
only the stream and the 256-byte chunk region change. -/
theorem twp_func3_read_chunk
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized chunkBytes outputBytes input output : List UInt8)
    (raised : Bool)
    (params localValues : List Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hlocal0 : (⟨params, localValues, stack⟩ : Locals).get 0 =
      some (.i32 driverBase)) :
    let count := min 256 input.length
    iprop(
      RuntimeContext ∗
      Streams input output raised ∗
      ExportFrame heapId capacity ptr initialized chunkBytes outputBytes ∗
      (RuntimeContext -∗
        Streams (input.drop count) output raised -∗
        ExportFrame heapId capacity ptr initialized
          (input.take count ++ chunkBytes.drop count) outputBytes -∗
        ⌜count ≤ 256⌝ -∗
        WP (.running
          ⟨⟨params, localValues,
              .i32 (UInt32.ofNat count) :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨params, localValues, stack⟩,
          [.localGet 0, .const 12, .add, .const 256, .call 13] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let count := min 256 input.length
  iintro ⟨Hruntime, Hstreams, Hframe, Hcont⟩
  isimp only [ExportFrame] at Hframe
  icases Hframe with ⟨Hvec, Hchunk, Houtput, %hframeLengths⟩
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet hlocal0
  wasm_twp_pures [twp_const twp_add]
  rw [show 12 + driverBase = driverBase + 12 by decide]
  wasm_twp_pures [twp_const]
  have Hread := Project.Mergesort.ContractProofs.func10_correct (hlc := hlc)
      (ptr := driverBase + 12) (requested := 256)
      (buffer := chunkBytes) (input := input) (output := output)
      (raised := raised)
      (callerLocals := ⟨params, localValues, stack⟩) (stack := stack)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  dsimp only at Hread
  unfold CallContract callExpr at Hread
  simp only [UInt32.reduceToNat, List.cons_append, List.nil_append] at Hread
  iapply Hread
  isplitl_exact Hruntime
  isplitl_exact Hstreams
  isplitl_exact Hchunk
  isplitl_pureexact ⟨by simpa using hframeLengths.1.symm, by decide⟩
  iintro Hruntime Hstreams Hchunk %hcount
  ihave Hframe : ExportFrame heapId capacity ptr initialized
      (input.take count ++ chunkBytes.drop count) outputBytes $$
      [Hvec Hchunk Houtput]
  · unfold ExportFrame
    isplitl_exact Hvec
    isplitl_exact Hchunk
    isplitl_exact Houtput
    ipureintro
    constructor
    · have htake := List.length_take_le count input
      simp [count, hframeLengths.1]
    · exact hframeLengths.2
  unfold ResumeWP resumeExpr
  simp only [List.cons_append, List.nil_append]
  iapply Hcont $$ Hruntime Hstreams Hframe
  · ipureexact hcount

/-- Locals relevant to the read-loop append path.  The auxiliary slots are
threaded explicitly so the lemma applies at every loop iteration. -/
private def func3AppendLocals
    (dataPtr current length aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (values : List Value) : Locals :=
  { locals :=
      [.i32 driverBase, .i32 dataPtr, .i32 aux2, .i32 current,
        .i32 aux4, .i32 aux5, .i32 length, .i32 aux7, .i32 aux8,
        .i32 aux9, .i32 aux10]
    values := values }

/-- Exact body of the generated block which either observes enough spare
capacity or calls `func1` and reloads the changed Vec header. -/
private def func3CapacityBody : Program :=
  [.localGet 3, .localGet 0, .load32 0, .localGet 6, .sub, .leU, .br_if 0,
    .localGet 0, .localGet 6, .localGet 3, .const 1, .const 1, .call 4,
    .localGet 0, .load32 4, .localSet 1,
    .localGet 0, .load32 8, .localSet 6]

/-- Exact generated block which skips the copy for a zero-length read and
otherwise copies the current chunk into Vec spare capacity. -/
private def func3AppendCopyBody : Program :=
  [.localGet 3, .eqz, .br_if 0,
    .localGet 1, .localGet 6, .add,
    .localGet 0, .const 12, .add,
    .localGet 3, .memoryCopy]

/-- Exact append block plus the length commit which follows that block. -/
private def func3AppendBody : Program :=
  [.block 0 0 func3AppendCopyBody,
    .localGet 0, .localGet 6, .localGet 3, .add,
    .localTee 6, .store32 8]

/-- Copy a nonempty chunk into already-available Vec spare capacity and
commit the new Vec length.  This is the success branch below the generated
capacity guard; the reserve branch is handled separately through `Func1Spec`.
-/
theorem twp_func3_append_without_reserve
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity dataPtr : UInt32)
    (initialized current chunkTail outputBytes : List UInt8)
    (hcurrent : 0 < current.length)
    (hfits : current.length ≤ capacity.toNat - initialized.length)
    (hnewLength : initialized.length + current.length < UInt32.size)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      ExportFrame heapId capacity dataPtr initialized
          (current ++ chunkTail) outputBytes ∗
      (ExportFrame heapId capacity dataPtr (initialized ++ current)
          (current ++ chunkTail) outputBytes -∗
        WP (.running
          ⟨func3AppendLocals dataPtr (UInt32.ofNat current.length)
              (UInt32.ofNat (initialized ++ current).length)
              aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr (UInt32.ofNat current.length)
            (UInt32.ofNat initialized.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          func3AppendBody ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hframe, Hcont⟩
  isimp only [ExportFrame] at Hframe
  icases Hframe with ⟨Hvec, Hchunk, Houtput, %hframeLengths⟩
  ihave Happend := VecU8_appendFocus heapId driverBase capacity dataPtr
      initialized current hcurrent hfits $$ Hvec
  icases Happend with
    ⟨%oldChunk, %holdChunkLength, HoldChunk, HoldLength, HcloseVec⟩
  icases (ByteSlice_append (driverBase + 12) current chunkTail).mp $$
      Hchunk with ⟨Hcurrent, HchunkTail⟩
  isimp only [Project.Mergesort.Representations.ByteSlice] at HoldChunk
  icases HoldChunk with ⟨%holdChunkNowrap, HoldChunkBytes⟩
  isimp only [Project.Mergesort.Representations.ByteSlice] at Hcurrent
  icases Hcurrent with ⟨%hcurrentNowrap, HcurrentBytes⟩
  have hcurrentWord : (UInt32.ofNat current.length).toNat = current.length :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hcurrentNonzero : UInt32.ofNat current.length ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    rw [hcurrentWord] at hzeroNat
    simp only [UInt32.toNat_zero] at hzeroNat
    omega
  simp only [func3AppendBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3AppendCopyBody, func3AppendLocals]
  wasm_twp_pures [twp_localGet]
  iapply twp_eqz (result := 0) (by simp [hcurrentNonzero])
  wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_add twp_localGet twp_const twp_add]
  rw [show 12 + driverBase = driverBase + 12 by decide]
  wasm_twp_pures [twp_localGet]
  rw [show UInt32.ofNat initialized.length + dataPtr =
    dataPtr + UInt32.ofNat initialized.length by ac_rfl]
  iapply twp_memoryCopy32 oldChunk current
      (by simpa [hcurrentWord] using holdChunkLength)
      (by simp [hcurrentWord])
      (by simpa [hcurrentWord])
      (by
        rw [hcurrentWord, ← holdChunkLength]
        exact holdChunkNowrap)
      (by simpa [hcurrentWord] using hcurrentNowrap) $$
      HcurrentBytes HoldChunkBytes
  iintro HcurrentBytes HoldChunkBytes
  ihave Hcurrent : Project.Mergesort.Representations.ByteSlice
      (driverBase + 12) current $$ [HcurrentBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    iframe
    ipureexact hcurrentNowrap
  ihave Hchunk : Project.Mergesort.Representations.ByteSlice
      (driverBase + 12) (current ++ chunkTail) $$ [Hcurrent HchunkTail]
  · iapply_frame (ByteSlice_append (driverBase + 12) current chunkTail).mpr
  ihave HnewBytes : Project.Mergesort.Representations.ByteSlice
      (dataPtr + UInt32.ofNat initialized.length) current $$
      [HoldChunkBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    iframe
    ipureintro
    rw [holdChunkLength] at holdChunkNowrap
    exact holdChunkNowrap
  wasm_twp_pures [twp_exitControl]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_add]
  have hlengthWord :
      UInt32.ofNat current.length + UInt32.ofNat initialized.length =
        UInt32.ofNat (initialized ++ current).length := by
    rw [UInt32.add_comm,
      Wasm.Examples.MergeSort.u32_ofNat_add hnewLength]
    simp
  rw [hlengthWord]
  iapply twp_localTee
      (locals' := func3AppendLocals dataPtr (UInt32.ofNat current.length)
        (UInt32.ofNat (initialized ++ current).length)
        aux2 aux4 aux5 aux7 aux8 aux9 aux10
        (.i32 (UInt32.ofNat (initialized ++ current).length) ::
          .i32 driverBase :: stack)) (by simp [func3AppendLocals])
  simp only [func3AppendLocals]
  wasm_twp_bind twp_store32 (UInt32.ofNat initialized.length)
      (by decide) (by decide) (by decide) (by decide) with HoldLength => HnewLength
  ihave Hvec := HcloseVec $$ HnewBytes HnewLength
  ihave Hframe : ExportFrame heapId capacity dataPtr
      (initialized ++ current) (current ++ chunkTail) outputBytes $$
      [Hvec Hchunk Houtput]
  · unfold ExportFrame
    iframe
    ipureexact hframeLengths
  iapply Hcont $$ Hframe

/-- Reload the Vec data pointer and length after `func1` returns.  The
generated driver does not trust return operands for these fields: it reads
the authoritative header that `Func1Spec` has re-established. -/
theorem twp_func3_reload_vec_fields
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity oldPtr ptr : UInt32)
    (initialized chunkBytes outputBytes : List UInt8)
    (current aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      ExportFrame heapId capacity ptr initialized chunkBytes outputBytes ∗
      (ExportFrame heapId capacity ptr initialized chunkBytes outputBytes -∗
        WP (.running
          ⟨func3AppendLocals ptr current
              (UInt32.ofNat initialized.length)
              aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals oldPtr current
            (UInt32.ofNat initialized.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          [.localGet 0, .load32 4, .localSet 1,
            .localGet 0, .load32 8, .localSet 6] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hframe, Hcont⟩
  isimp only [ExportFrame, VecU8, RawVecHeader] at Hframe
  icases Hframe with
    ⟨⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩,
      Hchunk, Houtput, %hframeLengths⟩
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  wasm_twp_pures [twp_localGet]
  iapply twp_load32 ptr (by decide) (by decide) (by decide) (by decide) $$
    Hpointer
  iintro Hpointer
  wasm_twp_pures [twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (UInt32.ofNat initialized.length)
      (by decide) (by decide) (by decide) (by decide) with Hlength
  wasm_twp_pures [twp_localSet]
  simp only [List.length, List.set]
  ihave Hframe : ExportFrame heapId capacity ptr initialized
      chunkBytes outputBytes $$
      [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
  · unfold ExportFrame VecU8 RawVecHeader
    iframe
    ipureexact hframeLengths
  iapply Hcont $$ Hframe

/-- Driver-level view of `Func1Spec`'s continuation.  It frames the read
chunk and output slot into the complete `ExportFrame` on both success and
reserve-phase OOM. -/
def Func3ReserveContinuation
    [WasmSmallStepGS hlc Universal.State]
    (totalBytes : Nat) (current : List UInt8)
    (capacity dataPtr : UInt32) (initialized chunkBytes outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (remaining output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  let newCapacityNat :=
    selectedCapacity initialized.length current.length capacity.toNat
  let newCapacity := UInt32.ofNat newCapacityNat
  let newLayout : AllocLayout :=
    { size := newCapacityNat, alignment := 1 }
  match classifyBump frontier newLayout with
  | .success newPtr finish => iprop(
      (∀ finalHistory : AllocationHistory,
          RuntimeContext -∗
          StackPointer driverBase -∗
          StackReserve reserveBase
            (reserveSuccessShadow shadow newPtr newCapacity) -∗
          ExportFrame heapId newCapacity newPtr initialized
            chunkBytes outputBytes -∗
          BumpHeap heapId finish finish.toNat finalHistory -∗
          ⌜VecReserveHistory history finalHistory capacity dataPtr newPtr
              newLayout ∧
            GeometricVecFacts totalBytes
              (initialized.length + current.length) remaining.length
              newCapacity newPtr finish.toNat finalHistory⌝ -∗
          Streams remaining output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ) ∧
        (StackPointer reserveBase -∗
          StackReserve reserveBase shadow -∗
          ExportFrame heapId capacity dataPtr initialized
            chunkBytes outputBytes -∗
          BumpHeap heapId storedCursor frontier history -∗
          Streams remaining output true -∗
          Φ (.trapped (.host OOM.trapMessage))))
  | .oom => iprop(
      StackPointer reserveBase -∗
      StackReserve reserveBase shadow -∗
      ExportFrame heapId capacity dataPtr initialized chunkBytes outputBytes -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams remaining output true -∗
      Φ (.trapped (.host OOM.trapMessage)))

/-- Execute the generated reserve call after the capacity guard has proved
that the current nonempty chunk does not fit.  All excluded RawVec error
edges are discharged by the explicit valid-input facts passed to
`Func1Spec`; its only terminal branch is repackaged as the precise driver
reserve OOM state. -/
theorem twp_func3_reserve
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (totalBytes : Nat) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkBytes outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8) (raised : Bool)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (hfacts :
      current.length = min 256 (current.length + remaining.length) ∧
      0 < current.length ∧ current.length % 4 = 0 ∧
      capacity.toNat - initialized.length < current.length ∧
      totalBytes = initialized.length + current.length + remaining.length ∧
      GeometricVecFacts totalBytes initialized.length
        (current.length + remaining.length) capacity dataPtr frontier history ∧
      initialized.length + current.length < UInt32.size ∧
      selectedCapacity initialized.length current.length capacity.toNat <
        UInt32.size ∧
      ({ size := selectedCapacity initialized.length current.length
          capacity.toNat, alignment := 1 } : AllocLayout).Valid)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let callerLocals := func3AppendLocals dataPtr
      (UInt32.ofNat current.length) (UInt32.ofNat initialized.length)
      aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr initialized chunkBytes outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output raised ∗
      Func3ReserveContinuation totalBytes current capacity dataPtr initialized
        chunkBytes outputBytes shadow heapId storedCursor frontier history
        remaining output raised callerLocals stack code arity remainder
        controls calls s E Φ) ⊢
      WP (.running
        ⟨callerLocals,
          [.localGet 0, .localGet 6, .localGet 3,
            .const 1, .const 1, .call 4] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let callerLocals := func3AppendLocals dataPtr
    (UInt32.ofNat current.length) (UInt32.ofNat initialized.length)
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack
  let newCapacityNat :=
    selectedCapacity initialized.length current.length capacity.toNat
  let newCapacity := UInt32.ofNat newCapacityNat
  let newLayout : AllocLayout := { size := newCapacityNat, alignment := 1 }
  have hinitializedWord :
      (UInt32.ofNat initialized.length).toNat = initialized.length :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hcurrentWord :
      (UInt32.ofNat current.length).toNat = current.length :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  isimp only [ExportFrame] at Hframe
  icases Hframe with ⟨Hvec, Hchunk, Houtput, %hframeLengths⟩
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const twp_const]
  have HreserveCall := hfunc1 (header := driverBase)
      (length := UInt32.ofNat initialized.length)
      (additional := UInt32.ofNat current.length)
      (alignment := 1) (elementSize := 1)
      (totalBytes := totalBytes) (current := current)
      (remaining := remaining) (capacity := capacity) (ptr := dataPtr)
      (initialized := initialized) (shadow := shadow) (heapId := heapId)
      (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (output := output) (raised := raised)
      (callerLocals := callerLocals) (stack := stack) (code := code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
  dsimp only at HreserveCall
  unfold CallContract callExpr at HreserveCall
  simp only [List.cons_append, List.nil_append, callerLocals,
    func3AppendLocals] at HreserveCall
  iapply HreserveCall
  isplitl_exact Hruntime
  isplitl_exact Hsp
  isplitl_exact Hreserve
  isplitl_exact Hvec
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isplitl_pureexact ⟨True.intro, True.intro, True.intro,
      hinitializedWord, hcurrentWord,
      hfacts.1, hfacts.2.1, hfacts.2.2.1, hfacts.2.2.2.1,
      hfacts.2.2.2.2.1, hfacts.2.2.2.2.2.1,
      hfacts.2.2.2.2.2.2.1, hfacts.2.2.2.2.2.2.2.1,
      hfacts.2.2.2.2.2.2.2.2⟩
  isimp only [Func3ReserveContinuation] at Hcont
  unfold ReserveContinuation
  dsimp only
  cases hdecision : classifyBump frontier newLayout with
  | oom =>
      isimp only [hdecision] at Hcont
      iintro Hsp Hreserve Hvec Hbump Hstreams
      ihave Hframe : ExportFrame heapId capacity dataPtr initialized
          chunkBytes outputBytes $$ [Hvec Hchunk Houtput]
      · unfold ExportFrame
        iframe
        ipureexact hframeLengths
      iapply Hcont $$ Hsp Hreserve Hframe Hbump Hstreams
  | success newPtr finish =>
      isimp only [hdecision] at Hcont
      isplit
      · iintro %finalHistory Hruntime Hsp Hreserve Hvec Hbump %hpure Hstreams
        ihave Hframe : ExportFrame heapId newCapacity newPtr initialized
            chunkBytes outputBytes $$ [Hvec Hchunk Houtput]
        · unfold ExportFrame
          iframe
          ipureexact hframeLengths
        ihave Hnormal := BI.and_elim_l $$ Hcont
        iapply Hnormal $$ %finalHistory Hruntime Hsp Hreserve Hframe Hbump
          %hpure Hstreams
      · iintro Hsp Hreserve Hvec Hbump Hstreams
        ihave Hframe : ExportFrame heapId capacity dataPtr initialized
            chunkBytes outputBytes $$ [Hvec Hchunk Houtput]
        · unfold ExportFrame
          iframe
          ipureexact hframeLengths
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ Hsp Hreserve Hframe Hbump Hstreams

/-- Continuation shared by the two capacity-guard branches.  Additive
conjunction is essential here: the same linear caller continuation must be
available after normal append and after the allocator's physical OOM arm. -/
def Func3AppendContinuation
    [WasmSmallStepGS hlc Universal.State]
    (totalBytes : Nat) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkBytes outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  (∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
    ∀ finalStoredCursor : UInt32, ∀ finalFrontier : Nat,
    ∀ finalHistory : AllocationHistory, ∀ finalShadow : List UInt8,
      RuntimeContext -∗
      StackPointer driverBase -∗
      StackReserve reserveBase finalShadow -∗
      ExportFrame heapId finalCapacity finalPtr (initialized ++ current)
        chunkBytes outputBytes -∗
      BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
      Streams remaining output false -∗
      ⌜GeometricVecFacts totalBytes (initialized.length + current.length)
        remaining.length finalCapacity finalPtr finalFrontier finalHistory⌝ -∗
      WP (.running
        ⟨func3AppendLocals finalPtr (UInt32.ofNat current.length)
            (UInt32.ofNat (initialized ++ current).length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) ∧
  (StackPointer reserveBase -∗
    StackReserve reserveBase shadow -∗
    ExportFrame heapId capacity dataPtr initialized chunkBytes outputBytes -∗
    BumpHeap heapId storedCursor frontier history -∗
    Streams remaining output true -∗
    Φ (.trapped (.host OOM.trapMessage))))

/-- Discharge the generated `count ≥ 257` panic edge at its originating
guard.  The only premise is the `count ≤ 256` fact returned by `func10`; no
specification for the compiler-generated panic target is introduced. -/
theorem twp_func3_count_guard
    [WasmSmallStepGS hlc Universal.State]
    (dataPtr : UInt32) (currentLength initializedLength : Nat)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (hcurrentBound : currentLength ≤ 256)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      WP (.running
        ⟨func3AppendLocals dataPtr (UInt32.ofNat currentLength)
            (UInt32.ofNat initializedLength)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr (UInt32.ofNat currentLength)
            (UInt32.ofNat initializedLength)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          [.localGet 3, .const 257, .geU, .br_if 1] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  have hcurrentSize : currentLength < UInt32.size := by
    norm_num [UInt32.size]
    omega
  have hcurrentWord :
      (UInt32.ofNat currentLength).toNat = currentLength :=
    UInt32.toNat_ofNat_of_lt' hcurrentSize
  have hlt : UInt32.ofNat currentLength < (257 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt, hcurrentWord,
      show (257 : UInt32).toNat = 257 by decide]
    omega
  iintro Hcont
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_const]
  iapply twp_geU (result := 0)
    (by simp [UInt32.not_le.mpr hlt])
  wasm_twp_pures [twp_brIfZero]
  iexact Hcont

/-- Splitting a canonical byte stream at the driver's 256-byte read size
preserves four-byte word boundaries on both sides. -/
private theorem readChunk_mod_four (input : List UInt8)
    (hmod : input.length % 4 = 0) :
    let count := min 256 input.length
    (input.take count).length = count ∧
      count % 4 = 0 ∧
      (input.drop count).length % 4 = 0 := by
  dsimp only
  by_cases hshort : input.length ≤ 256
  · have hcount : min 256 input.length = input.length :=
      min_eq_right hshort
    rw [hcount]
    simp [hmod]
  · have hcount : min 256 input.length = 256 :=
      min_eq_left (Nat.le_of_not_ge hshort)
    rw [hcount]
    have hlength : 256 ≤ input.length := by omega
    simp only [List.length_take, min_eq_left hlength, List.length_drop]
    exact ⟨trivial, by decide, by omega⟩

/-- Execute the generated next-chunk read, update local 3, and classify the
zero/nonzero result.  The nonzero arm exposes the exact next loop partition
and its word-alignment facts; the zero arm preserves the completed frame. -/
theorem twp_func3_read_and_classify
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity dataPtr : UInt32)
    (initialized chunkBytes outputBytes input output : List UInt8)
    (hinputMod : input.length % 4 = 0)
    (previousCurrent : UInt32)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let count := min 256 input.length
    let nextCurrent := input.take count
    let nextRemaining := input.drop count
    let nextTail := chunkBytes.drop count
    iprop(
      RuntimeContext ∗
      Streams input output false ∗
      ExportFrame heapId capacity dataPtr initialized chunkBytes outputBytes ∗
      ((RuntimeContext -∗
          Streams [] output false -∗
          ExportFrame heapId capacity dataPtr initialized
            chunkBytes outputBytes -∗
          ⌜input = []⌝ -∗
          WP (.running
            ⟨func3AppendLocals dataPtr 0
                (UInt32.ofNat initialized.length)
                aux2 aux4 aux5 aux7 aux8 aux9 aux10 (.i32 1 :: stack),
              code, arity, remainder, controls, calls⟩ : Expr Universal.State)
            @ s; E [{ Φ }]) ∧
        (RuntimeContext -∗
          Streams nextRemaining output false -∗
          ExportFrame heapId capacity dataPtr initialized
            (nextCurrent ++ nextTail) outputBytes -∗
          ⌜input ≠ [] ∧ nextCurrent.length = count ∧
            0 < count ∧ count ≤ 256 ∧
            count % 4 = 0 ∧ nextRemaining.length % 4 = 0 ∧
            input = nextCurrent ++ nextRemaining⌝ -∗
          WP (.running
            ⟨func3AppendLocals dataPtr (UInt32.ofNat count)
                (UInt32.ofNat initialized.length)
                aux2 aux4 aux5 aux7 aux8 aux9 aux10 (.i32 0 :: stack),
              code, arity, remainder, controls, calls⟩ : Expr Universal.State)
            @ s; E [{ Φ }]))) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr previousCurrent
            (UInt32.ofNat initialized.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          [.localGet 0, .const 12, .add, .const 256, .call 13,
            .localTee 3, .eqz] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let count := min 256 input.length
  let nextCurrent := input.take count
  let nextRemaining := input.drop count
  let nextTail := chunkBytes.drop count
  have hsplit := readChunk_mod_four input hinputMod
  dsimp only at hsplit
  have hcountBound : count ≤ 256 := min_le_left _ _
  iintro ⟨Hruntime, Hstreams, Hframe, Hcont⟩
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  have Hread := twp_func3_read_chunk heapId capacity dataPtr initialized chunkBytes
    outputBytes input output false []
    [.i32 driverBase, .i32 dataPtr, .i32 aux2, .i32 previousCurrent,
      .i32 aux4, .i32 aux5, .i32 (UInt32.ofNat initialized.length),
      .i32 aux7, .i32 aux8, .i32 aux9, .i32 aux10]
    rfl
    (stack := stack) (code := [.localTee 3, .eqz] ++ code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [List.cons_append, List.nil_append] at Hread
  iapply Hread
  isplitl_exact Hruntime
  isplitl_exact Hstreams
  isplitl_exact Hframe
  iintro Hruntime Hstreams Hframe %_hcountBound
  iapply twp_localTee
      (locals' := func3AppendLocals dataPtr (UInt32.ofNat count)
        (UInt32.ofNat initialized.length)
        aux2 aux4 aux5 aux7 aux8 aux9 aux10
        (.i32 (UInt32.ofNat count) :: stack))
      (by simp [func3AppendLocals, count])
  simp only [func3AppendLocals]
  by_cases hempty : input = []
  · have hcountZero : count = 0 := by simp [count, hempty]
    have hremainingEmpty : input.drop count = [] := by
      simp [hempty, hcountZero]
    ihave HstreamsEmpty : Streams [] output false $$ [Hstreams]
    · rw [← hremainingEmpty]
      iexact Hstreams
    ihave HframeEmpty : ExportFrame heapId capacity dataPtr initialized
        chunkBytes outputBytes $$ [Hframe]
    · isimp only [hempty, List.length_nil, min_zero, List.take_zero,
        List.drop_zero, List.nil_append] at Hframe
      iexact Hframe
    iapply twp_eqz (result := 1) (by simp [hcountZero])
    simp only [hcountZero, UInt32.reduceOfNat]
    ihave Hempty := BI.and_elim_l $$ Hcont
    iapply Hempty $$ Hruntime HstreamsEmpty HframeEmpty
    · ipureexact hempty
  · have hinputPositive : 0 < input.length := by
      by_contra hnot
      apply hempty
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hcountPositive : 0 < count := by
      dsimp only [count]
      omega
    have hcountSize : count < UInt32.size := by
      norm_num [UInt32.size]
      omega
    have hcountWord : (UInt32.ofNat count).toNat = count :=
      UInt32.toNat_ofNat_of_lt' hcountSize
    have hcountNonzero : UInt32.ofNat count ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt32.toNat hzero
      rw [hcountWord] at hzeroNat
      simp only [UInt32.toNat_zero] at hzeroNat
      omega
    iapply twp_eqz (result := 0) (by simp [hcountNonzero])
    ihave Hnonempty := BI.and_elim_r $$ Hcont
    iapply Hnonempty $$ Hruntime Hstreams Hframe
    · ipureexact ⟨hempty, hsplit.1, hcountPositive, hcountBound,
        hsplit.2.1, hsplit.2.2,
        (List.take_append_drop count input).symm⟩

/-- Execute the generated capacity block and append one nonempty read chunk.
The fitting branch performs no allocation.  The non-fitting branch derives
all of `Func1Spec`'s valid-input premises from `GeometricVecFacts`, reloads
the returned header, and then uses the same append proof. -/
theorem twp_func3_append_current
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (totalBytes : Nat) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkTail outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (hfacts :
      current.length = min 256 (current.length + remaining.length) ∧
      0 < current.length ∧ current.length % 4 = 0 ∧
      totalBytes = initialized.length + current.length + remaining.length ∧
      GeometricVecFacts totalBytes initialized.length
        (current.length + remaining.length) capacity dataPtr frontier history)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output false ∗
      Func3AppendContinuation totalBytes current remaining capacity dataPtr
        initialized (current ++ chunkTail) outputBytes shadow heapId
        storedCursor frontier history output aux2 aux4 aux5 aux7 aux8 aux9
        aux10 stack code arity remainder controls calls s E Φ) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr (UInt32.ofNat current.length)
            (UInt32.ofNat initialized.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          .block 0 0 func3CapacityBody :: (func3AppendBody ++ code),
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  have hlayout := GeometricVecFacts.reserveLayout totalBytes
    initialized.length (current.length + remaining.length) current.length
    capacity dataPtr frontier history hfacts.2.2.2.2
    hfacts.1 hfacts.2.1
  dsimp only at hlayout
  have hinitializedCapacity : initialized.length ≤ capacity.toNat := by
    rcases hfacts.2.2.2.2 with hinitial | hshort | hlarge
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
    rw [UInt32.le_iff_toNat_le_toNat, hinitializedWord]
    exact hinitializedCapacity
  have hspareWord :
      (capacity - UInt32.ofNat initialized.length).toNat =
        capacity.toNat - initialized.length := by
    rw [UInt32.toNat_sub_of_le _ _ hinitializedLe, hinitializedWord]
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  isimp only [Func3AppendContinuation] at Hcont
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
          rw [UInt32.le_iff_toNat_le_toNat, hcurrentWord, hspareWord]
          exact hfits
        simp [hfitsWord])
    iapply twp_brIf (by decide) (by rfl)
    simp only [func3AppendBody, func3AppendLocals, List.take_zero,
      List.drop_zero, List.nil_append]
    ihave Hframe : ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes $$
        [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
    · unfold ExportFrame VecU8 RawVecHeader
      iframe
      ipureexact hframeLengths
    have Happend := twp_func3_append_without_reserve heapId capacity dataPtr
      initialized current chunkTail outputBytes hfacts.2.1 hfits hlayout.1
      aux2 aux4 aux5 aux7 aux8 aux9 aux10
      (stack := stack) (code := code) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls)
      (s := s) (E := E) (Φ := Φ)
    simp only [func3AppendLocals, func3AppendBody] at Happend
    iapply Happend
    iframe; iintro Hframe
    have hgeo := GeometricVecFacts.appendWithoutReserve totalBytes
      initialized.length current.length remaining.length capacity dataPtr
      frontier history hfacts.2.2.2.2 hfacts.2.1 hfits
    ihave Hnormal := BI.and_elim_l $$ Hcont
    iapply Hnormal $$ %capacity %dataPtr %storedCursor %frontier %history
      %shadow Hruntime Hsp Hreserve Hframe Hbump Hstreams
    · ipureexact hgeo
  · iapply twp_leU (result := 0)
      (by
        have hfitsWord :
            ¬UInt32.ofNat current.length ≤
              capacity - UInt32.ofNat initialized.length := by
          rw [UInt32.le_iff_toNat_le_toNat, hcurrentWord, hspareWord]
          exact hfits
        simp [hfitsWord])
    wasm_twp_pures [twp_brIfZero]
    simp only [func3AppendLocals, List.drop_zero]
    ihave Hframe : ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes $$
        [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
    · unfold ExportFrame VecU8 RawVecHeader
      iframe
      ipureexact hframeLengths
    have HreserveStep := twp_func3_reserve hfunc1 totalBytes current remaining capacity
      dataPtr initialized (current ++ chunkTail) outputBytes shadow heapId
      storedCursor frontier history output false aux2 aux4 aux5 aux7 aux8
      aux9 aux10
      ⟨hfacts.1, hfacts.2.1, hfacts.2.2.1, Nat.lt_of_not_ge hfits,
        hfacts.2.2.2.1, hfacts.2.2.2.2, hlayout.1, hlayout.2.1,
        hlayout.2.2⟩
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
    isplitl_exact Hruntime
    isplitl_exact Hsp
    isplitl_exact Hreserve
    isplitl_exact Hframe
    isplitl_exact Hbump
    isplitl_exact Hstreams
    unfold Func3ReserveContinuation
    dsimp only
    cases hdecision : classifyBump frontier
        { size := selectedCapacity initialized.length current.length
            capacity.toNat, alignment := 1 } with
    | oom =>
        iintro Hsp Hreserve Hframe Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ Hsp Hreserve Hframe Hbump Hstreams
    | success newPtr finish =>
        isplit
        · iintro %finalHistory Hruntime Hsp Hreserve Hframe Hbump %hpure
            Hstreams
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
          iapply Hreload
          iframe; iintro Hframe
          wasm_twp_pures [twp_exitControl]
          simp only [List.take_zero, List.nil_append]
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
          iapply Happend
          iframe; iintro Hframe
          ihave Hnormal := BI.and_elim_l $$ Hcont
          iapply Hnormal $$
            %(UInt32.ofNat
              (selectedCapacity initialized.length current.length
                capacity.toNat)) %newPtr %finish %finish.toNat %finalHistory
            %(reserveSuccessShadow shadow newPtr
              (UInt32.ofNat
                (selectedCapacity initialized.length current.length
                  capacity.toNat))) Hruntime Hsp Hreserve Hframe Hbump Hstreams
          · ipureexact hpure.2
        · iintro Hsp Hreserve Hframe Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          iapply Hoom $$ Hsp Hreserve Hframe Hbump Hstreams

/-- The generated read/categorize suffix of one active loop iteration. -/
private def func3ReadClassifyBody : Program :=
  [.localGet 0, .const 12, .add, .const 256, .call 13,
    .localTee 3, .eqz]

/-- Postcondition of one complete active read-loop iteration, immediately
before the generated `br_if 2; br 0` pair. -/
def Func3IterationContinuation
    [WasmSmallStepGS hlc Universal.State]
    (totalBytes : Nat) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkBytes outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
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
    ((∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
      ∀ finalStoredCursor : UInt32, ∀ finalFrontier : Nat,
      ∀ finalHistory : AllocationHistory, ∀ finalShadow : List UInt8,
        RuntimeContext -∗
        StackPointer driverBase -∗
        StackReserve reserveBase finalShadow -∗
        ExportFrame heapId finalCapacity finalPtr
          (initialized ++ current) chunkBytes outputBytes -∗
        BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
        Streams [] output false -∗
        ⌜remaining = [] ∧
          GeometricVecFacts totalBytes
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
          RuntimeContext -∗
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
            GeometricVecFacts totalBytes
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
            @ s; E [{ Φ }])) ∧
    (StackPointer reserveBase -∗
      StackReserve reserveBase shadow -∗
      ExportFrame heapId capacity dataPtr initialized chunkBytes outputBytes -∗
      BumpHeap heapId storedCursor frontier history -∗
      Streams remaining output true -∗
      Φ (.trapped (.host OOM.trapMessage))))

/-- One exact active iteration: exclude the oversized-read panic edge,
append the current chunk (reserving if needed), then read and classify the
next chunk. -/
theorem twp_func3_read_loop_iteration
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (totalBytes : Nat) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkTail outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (hfacts :
      current.length = min 256 (current.length + remaining.length) ∧
      0 < current.length ∧ current.length ≤ 256 ∧
      current.length % 4 = 0 ∧ remaining.length % 4 = 0 ∧
      totalBytes = initialized.length + current.length + remaining.length ∧
      GeometricVecFacts totalBytes initialized.length
        (current.length + remaining.length) capacity dataPtr frontier history)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output false ∗
      Func3IterationContinuation totalBytes current remaining capacity dataPtr
        initialized (current ++ chunkTail) outputBytes shadow heapId
        storedCursor frontier history output aux2 aux4 aux5 aux7 aux8 aux9
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
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  isimp only [Func3IterationContinuation] at Hcont
  have Hguard := twp_func3_count_guard dataPtr current.length
    initialized.length aux2 aux4 aux5 aux7 aux8 aux9 aux10 hfacts.2.2.1
    (stack := stack)
    (code := [.block 0 0 func3CapacityBody] ++ func3AppendBody ++
      func3ReadClassifyBody ++ code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [List.cons_append, List.nil_append] at Hguard ⊢
  iapply Hguard
  have Happend := twp_func3_append_current hfunc1 totalBytes current remaining
    capacity dataPtr initialized chunkTail outputBytes shadow heapId
    storedCursor frontier history output aux2 aux4 aux5 aux7 aux8 aux9 aux10
    ⟨hfacts.1, hfacts.2.1, hfacts.2.2.2.1, hfacts.2.2.2.2.2.1,
      hfacts.2.2.2.2.2.2⟩
    (stack := stack) (code := func3ReadClassifyBody ++ code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  rw [List.append_assoc func3AppendBody func3ReadClassifyBody code]
  iapply Happend
  isplitl_exact Hruntime
  isplitl_exact Hsp
  isplitl_exact Hreserve
  isplitl_exact Hframe
  isplitl_exact Hbump
  isplitl_exact Hstreams
  unfold Func3AppendContinuation
  isplit
  · iintro %finalCapacity %finalPtr %finalStoredCursor %finalFrontier
      %finalHistory %finalShadow Hruntime Hsp Hreserve Hframe Hbump Hstreams
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
    isplitl_exact Hruntime
    isplitl_exact Hstreams
    isplitl_exact Hframe
    isplit
    · iintro Hruntime Hstreams Hframe %hremainingEmpty
      ihave HdonePair := BI.and_elim_l $$ Hcont
      ihave Hdone := BI.and_elim_l $$ HdonePair
      iapply Hdone $$ %finalCapacity %finalPtr %finalStoredCursor
        %finalFrontier %finalHistory %finalShadow Hruntime Hsp Hreserve Hframe
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
          GeometricVecFacts totalBytes
            (initialized.length + current.length)
            ((remaining.take (min 256 remaining.length)).length +
              (remaining.drop (min 256 remaining.length)).length)
            finalCapacity finalPtr finalFrontier finalHistory := by
        rw [← hremainingLength]
        exact hgeo
      have htotalNext :
          totalBytes = (initialized ++ current).length +
            (remaining.take (min 256 remaining.length)).length +
            (remaining.drop (min 256 remaining.length)).length := by
        have htotal := hfacts.2.2.2.2.2.1
        simp only [List.length_append]
        omega
      have hreadShape :
          (remaining.take (min 256 remaining.length)).length =
            min 256
              ((remaining.take (min 256 remaining.length)).length +
                (remaining.drop (min 256 remaining.length)).length) := by
        rw [← hremainingLength]
        exact hnext.2.1
      have hmeasure :
          (remaining.take (min 256 remaining.length)).length +
              (remaining.drop (min 256 remaining.length)).length <
            current.length + remaining.length := by
        rw [← hremainingLength]
        omega
      have hnextPositive :
          0 < (remaining.take (min 256 remaining.length)).length := by
        rw [hnext.2.1]
        exact hnext.2.2.1
      have hnextBound :
          (remaining.take (min 256 remaining.length)).length ≤ 256 := by
        rw [hnext.2.1]
        exact hnext.2.2.2.1
      have hnextMod :
          (remaining.take (min 256 remaining.length)).length % 4 = 0 := by
        rw [hnext.2.1]
        exact hnext.2.2.2.2.1
      ihave HnextPair := BI.and_elim_l $$ Hcont
      ihave Hnext := BI.and_elim_r $$ HnextPair
      iapply Hnext $$ %finalCapacity %finalPtr %finalStoredCursor
        %finalFrontier %finalHistory %finalShadow Hruntime Hsp Hreserve Hframe
        Hbump Hstreams
      · ipureexact ⟨hreadShape, hnextPositive, hnextBound,
          hnextMod, hnext.2.2.2.2.2.1, hnext.2.2.2.2.2.2,
          htotalNext,
          hgeoNext, hmeasure⟩
  · iintro Hsp Hreserve Hframe Hbump Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    iapply Hoom $$ Hsp Hreserve Hframe Hbump Hstreams

/-- Exact generated loop body for the input-accumulation phase. -/
private def func3ReadLoopBody : Program :=
  [.localGet 3, .const 257, .geU, .br_if 1,
    .block 0 0 func3CapacityBody] ++ func3AppendBody ++
    func3ReadClassifyBody ++ [.br_if 2, .br 0]

/-- The compiler-generated panic tail following the inner read-loop block.
The valid-input loop invariant makes its only incoming edge unreachable. -/
private def func3OversizedReadPanic : Program :=
  [.const 0, .localGet 3, .const 256, .const 1049096, .call 49,
    .unreachable]

private def func3ReadLoopBlockBody : Program :=
  [.loop 0 0 func3ReadLoopBody]

private def func3ReadPhaseBody : Program :=
  [.block 0 0 func3ReadLoopBlockBody] ++ func3OversizedReadPanic

private def func3InitialReadPrefix : Program :=
  [.localGet 0, .const 12, .add, .const 256, .call 13,
    .localTee 3, .br_if 0]

private def func3EmptyInputSuffix : Program :=
  [.const 1, .localSet 4, .const 1, .localSet 5, .br 1]

/-- Exact initial-read block.  The suffix is the generated empty-input arm;
the nonempty arm branches to the block continuation before reaching it. -/
private def func3InitialReadBody : Program :=
  func3InitialReadPrefix ++ func3EmptyInputSuffix

private def func3AfterInitialRead (afterLoop : Program) : Program :=
  [.const 0, .localSet 6, .const 1, .localSet 1,
    .block 0 0 func3ReadPhaseBody] ++ afterLoop

private def func3InitialReadFrame (afterLoop : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3InitialReadBody,
    continuation := func3AfterInitialRead afterLoop,
    belowStack := [] }

private def func3EmptyLocals : Locals :=
  func3AppendLocals 0 0 0 4 1 1 0 0 0 0 []

private def func3EnclosingDriverFrame
    (body afterEmpty : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := body, continuation := afterEmpty, belowStack := [] }

private def func3ReadInnerFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3ReadLoopBlockBody,
    continuation := func3OversizedReadPanic,
    belowStack := [] }

private def func3ReadPhaseFrame (afterLoop : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3ReadPhaseBody,
    continuation := afterLoop,
    belowStack := [] }

/-! ## Completed-read dispatch -/

/-- Exact reload of the completed Vec's data pointer. -/
private def func3CompletedPtrReload : Program :=
  [.localGet 0, .load32 4, .localSet 4]

/-- The generated partial-word guard.  Public entry bytes are a canonical
serialization, so this branch condition is always zero. -/
private def func3CompletedLengthGuard : Program :=
  [.localGet 6, .const 3, .and, .br_if 0]

/-- The generated empty/nonempty split after the partial-word guard.  The
nonempty arm branches out of this block with local 7 holding the complete
byte length; the remaining instructions are the empty-input arm. -/
private def func3AlignedLengthBlockBody : Program :=
  [.localGet 6, .const 2147483644, .and, .localTee 7, .br_if 0,
    .const 1, .localSet 5, .const 0, .localSet 1, .br 4]

/-- Reload the completed Vec data pointer from its authoritative frame header.
The read loop already carries the length in local 6, so the generated body
reloads only the pointer into local 4 at this point. -/
theorem twp_func3_reload_completed_ptr
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity dataPtr : UInt32)
    (completed chunkBytes outputBytes : List UInt8)
    (current aux2 oldPtr aux5 aux7 aux8 aux9 aux10 : UInt32)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      ExportFrame heapId capacity dataPtr completed chunkBytes outputBytes ∗
      (ExportFrame heapId capacity dataPtr completed chunkBytes outputBytes -∗
        WP (.running
          ⟨func3AppendLocals dataPtr current
              (UInt32.ofNat completed.length)
              aux2 dataPtr aux5 aux7 aux8 aux9 aux10 stack,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr current
            (UInt32.ofNat completed.length)
            aux2 oldPtr aux5 aux7 aux8 aux9 aux10 stack,
          func3CompletedPtrReload ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hframe, Hcont⟩
  isimp only [ExportFrame, VecU8, RawVecHeader] at Hframe
  icases Hframe with
    ⟨⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩,
      Hchunk, Houtput, %hframeLengths⟩
  simp only [func3CompletedPtrReload, List.cons_append, List.nil_append,
    func3AppendLocals]
  wasm_twp_pures [twp_localGet]
  iapply twp_load32 dataPtr (by decide) (by decide) (by decide) (by decide) $$
    Hpointer
  iintro Hpointer
  wasm_twp_pures [twp_localSet]
  simp only [List.length, List.set]
  ihave Hframe : ExportFrame heapId capacity dataPtr completed
      chunkBytes outputBytes $$
      [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
  · unfold ExportFrame VecU8 RawVecHeader
    iframe
    ipureexact hframeLengths
  iapply Hcont $$ Hframe

/-- Canonical serialized input makes the compiler's partial-word branch
unreachable at its originating guard.  No specification is assigned to the
panic continuation targeted by a nonzero branch. -/
theorem twp_func3_completed_length_guard
    [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) (completed : List UInt8)
    (hcompleted : serialize original = completed)
    (hbound : completed.length < 2147483648)
    (dataPtr current aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    WP (.running
      ⟨func3AppendLocals dataPtr current (UInt32.ofNat completed.length)
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
        code, arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨func3AppendLocals dataPtr current (UInt32.ofNat completed.length)
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
        func3CompletedLengthGuard ++ code,
        arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }] := by
  iintro Hcont
  have halign : completed.length % 4 = 0 := by
    rw [← hcompleted, serialize_length]
    omega
  have hlengthWord :
      (UInt32.ofNat completed.length).toNat = completed.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size] at hbound ⊢
    omega
  have hlowMask : UInt32.ofNat completed.length &&& 3 = 0 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_and, hlengthWord]
    have hthree : (3 : UInt32).toNat = 3 := by decide
    rw [hthree]
    change completed.length &&& 3 = 0
    rw [show (3 : Nat) = 2 ^ 2 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
    exact halign
  simp only [func3CompletedLengthGuard, List.cons_append, List.nil_append,
    func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_const twp_and]
  rw [hlowMask]
  wasm_twp_pures [twp_brIfZero]
  iexact Hcont

/-- On nonempty public input, execute both post-read length tests and enter
the allocation/decode continuation with local 7 equal to the complete byte
length.  `completed_lt_signed` is what makes the signed mask exact; without
the read-loop lineage this theorem is intentionally unavailable. -/
theorem twp_func3_enter_nonempty_decode
    [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) (completed : List UInt8)
    (capacity dataPtr : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hcompleted : serialize original = completed)
    (hgeo : GeometricVecFacts (serialize original).length completed.length 0
      capacity dataPtr frontier history)
    (current aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    {stack : List Value} {afterBlock : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    WP (.running
      ⟨func3AppendLocals dataPtr current (UInt32.ofNat completed.length)
          aux2 aux4 aux5 (UInt32.ofNat completed.length) aux8 aux9 aux10 stack,
        afterBlock, arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨func3AppendLocals dataPtr current (UInt32.ofNat completed.length)
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
        func3CompletedLengthGuard ++
          [.block 0 0 func3AlignedLengthBlockBody] ++ afterBlock,
        arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }] := by
  iintro Hcont
  have hboundTotal := GeometricVecFacts.completed_lt_signed
    (serialize original).length completed.length 0 capacity dataPtr frontier
    history hgeo rfl
  have hbound : completed.length < 2147483648 := by
    simpa [hcompleted] using hboundTotal
  have halign : completed.length % 4 = 0 := by
    rw [← hcompleted, serialize_length]
    omega
  have hmask := align4_signedMask_eq completed.length hbound halign
  have hlengthWord :
      (UInt32.ofNat completed.length).toNat = completed.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size] at hbound ⊢
    omega
  have hpositive : 0 < completed.length := by
    rw [← hcompleted, serialize_length]
    have := List.length_pos_iff_ne_nil.mpr horiginal
    omega
  have hnonzero : UInt32.ofNat completed.length ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    rw [hlengthWord] at hzeroNat
    simp only [UInt32.toNat_zero] at hzeroNat
    omega
  have Hguard := twp_func3_completed_length_guard
    (hlc := hlc) original completed hcompleted hbound dataPtr current
    aux2 aux4 aux5 aux7 aux8 aux9 aux10
    (stack := stack)
    (code := [.block 0 0 func3AlignedLengthBlockBody] ++ afterBlock)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3CompletedLengthGuard, List.cons_append, List.nil_append]
    at Hguard ⊢
  iapply Hguard
  wasm_twp_pures [twp_block]
  simp only [func3AlignedLengthBlockBody, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_const twp_and]
  rw [hmask]
  iapply twp_localTee
      (locals' := func3AppendLocals dataPtr current
        (UInt32.ofNat completed.length) aux2 aux4 aux5
        (UInt32.ofNat completed.length) aux8 aux9 aux10
        (.i32 (UInt32.ofNat completed.length) :: stack))
      (by simp [func3AppendLocals])
  simp only [func3AppendLocals]
  iapply twp_brIf (condition := UInt32.ofNat completed.length) (depth := 0)
    (arity := arity) (targetCode := afterBlock) (targetControl := controls)
    (targetValues := stack) hnonzero (by rfl)
  iexact Hcont

/-! ## Values allocation -/

/-- Execute the generated allocation marker and values allocation call for a
completed nonempty input.  The only terminal allocator result is repackaged as
the exact `.values` driver OOM state; a normal result retains the stack/frame
resources and exposes the fresh complete live block. -/
theorem twp_func3_allocate_values
    [WasmSmallStepGS hlc Universal.State]
    (hfunc5 : Func5Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32)
    (capacity dataPtr : UInt32)
    (completed chunkBytes outputBytes shadow : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hcompleted : serialize original = completed)
    (hgeo : GeometricVecFacts (serialize original).length completed.length 0
      capacity dataPtr frontier history)
    (callerLocals : Locals)
    (hlocal7 : callerLocals.get 7 =
      some (.i32 (UInt32.ofNat completed.length)))
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := completed.length, alignment := 4 }
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr completed chunkBytes outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      ((∀ base : UInt32, ∀ finish : UInt32, ∀ bytes : List UInt8,
          ⌜classifyBump frontier layout = .success base finish⌝ -∗
          RuntimeContext -∗
          StackPointer driverBase -∗
          StackReserve reserveBase shadow -∗
          ExportFrame heapId capacity dataPtr completed chunkBytes
            outputBytes -∗
          BumpHeap heapId finish finish.toNat
            (history.allocate base layout) -∗
          LiveBlock heapId history.nextId base layout bytes -∗
          Streams [] [] false -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls
            calls s E Φ) ∧
        (DriverValuesOOM heapId original -∗
          Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨{ callerLocals with values := stack },
          [.call 7, .localGet 7, .const 4, .call 8] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := completed.length, alignment := 4 }
  have hboundTotal := GeometricVecFacts.completed_lt_signed
    (serialize original).length completed.length 0 capacity dataPtr frontier
    history hgeo rfl
  have hbound : completed.length < 2147483648 := by
    simpa [hcompleted] using hboundTotal
  have halign : completed.length % 4 = 0 := by
    rw [← hcompleted, serialize_length]
    omega
  have hpositive : 0 < completed.length := by
    rw [← hcompleted, serialize_length]
    have := List.length_pos_iff_ne_nil.mpr horiginal
    omega
  have hlengthWord :
      (UInt32.ofNat completed.length).toNat = completed.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size] at hbound ⊢
    omega
  have hlayoutValid : layout.Valid := by
    exact Project.Mergesort.Representations.align4Layout_valid_of_bounds
      completed.length hpositive hbound halign
  have hlayoutMatches :
      layout.Matches (UInt32.ofNat completed.length) 4 := by
    unfold AllocLayout.Matches layout
    simp only [hlengthWord]
    decide
  have hgeoOriginal : GeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity dataPtr frontier history := by
    simpa only [hcompleted] using hgeo
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  simp only [List.cons_append, List.nil_append]
  have Hmarker := Project.Mergesort.ContractProofs.func4_correct
      (hlc := hlc) (callerLocals := callerLocals) (stack := stack)
      (code := [.localGet 7, .const 4, .call 8] ++ code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func4Spec CallContract callExpr at Hmarker
  simp only [List.cons_append, List.nil_append] at Hmarker
  iapply Hmarker
  iframe; iintro Hruntime
  unfold ResumeWP resumeExpr
  simp only [List.cons_append, List.nil_append]
  have hlocal7' : ({ callerLocals with values := stack } : Locals).get 7 =
      some (.i32 (UInt32.ofNat completed.length)) := by
    simpa using hlocal7
  iapply twp_localGet hlocal7'
  wasm_twp_pures [twp_const]
  have Halloc := hfunc5
      (size := UInt32.ofNat completed.length) (alignment := 4)
      (layout := layout) (heapId := heapId) (storedCursor := storedCursor)
      (frontier := frontier) (history := history)
      (input := []) (output := []) (raised := false)
      (callerLocals := callerLocals) (stack := stack) (code := code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  iapply Halloc
  isplitl_exact Hruntime
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isplitl_pureexact ⟨hlayoutMatches, hlayoutValid, Or.inr rfl⟩
  unfold AllocContinuation
  cases hdecision : classifyBump frontier layout with
  | oom =>
      iintro Hbump Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      iapply Hoom
      ihave HframeOriginal : ExportFrame heapId capacity dataPtr
          (serialize original) chunkBytes outputBytes $$ [Hframe]
      · rw [hcompleted]
        iexact Hframe
      unfold DriverValuesOOM
      iexists capacity, dataPtr, chunkBytes, outputBytes, shadow,
        storedCursor, frontier, history
      isplitl_pureexact ⟨List.length_pos_iff_ne_nil.mpr horiginal, hgeoOriginal⟩
      iframe
  | success base finish =>
      isplit
      · iintro %bytes Hruntime Hbump Hblock Hstreams
        ihave Hnormal := BI.and_elim_l $$ Hcont
        ihave Hresume := Hnormal $$ %base %finish %bytes %rfl Hruntime Hsp
          Hreserve Hframe Hbump Hblock Hstreams
        iunfold ResumeWP
        simp only [resumeExpr, List.cons_append, List.nil_append]
        iexact Hresume
      · iintro Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom
        ihave HframeOriginal : ExportFrame heapId capacity dataPtr
            (serialize original) chunkBytes outputBytes $$ [Hframe]
        · rw [hcompleted]
          iexact Hframe
        unfold DriverValuesOOM
        iexists capacity, dataPtr, chunkBytes, outputBytes, shadow,
          storedCursor, frontier, history
        isplitl_pureexact ⟨List.length_pos_iff_ne_nil.mpr horiginal, hgeoOriginal⟩
        iframe

/-- Discharge the generated null check immediately following a normal values
allocation.  Non-nullness comes from the allocator-owned `LiveBlock`; the
depth-one compiler allocation-error target is therefore unreachable. -/
theorem twp_func3_values_nonnull_guard
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId : Nat)
    (base : UInt32) (layout : AllocLayout) (bytes : List UInt8)
    (dataPtr current length aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      LiveBlock heapId allocationId base layout bytes ∗
      (LiveBlock heapId allocationId base layout bytes -∗
        WP (.running
          ⟨func3AppendLocals dataPtr current length base aux4 aux5 aux7 aux8
              aux9 aux10 stack,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals dataPtr current length aux2 aux4 aux5 aux7 aux8
            aux9 aux10 (.i32 base :: stack),
          [.localTee 2, .eqz, .br_if 1] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hblock, Hcont⟩
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  iapply twp_localTee
      (locals' := func3AppendLocals dataPtr current length base aux4 aux5 aux7
        aux8 aux9 aux10 (.i32 base :: stack))
      (by simp [func3AppendLocals])
  simp only [func3AppendLocals]
  iapply twp_eqz (result := 0) (by simp [hfacts.2.1])
  wasm_twp_pures [twp_brIfZero]
  ihave Hblock : LiveBlock heapId allocationId base layout bytes $$
      [Htoken Hbytes]
  · unfold LiveBlock
    iframe
    ipureexact hfacts
  iapply Hcont $$ Hblock

/-- Copy one already-addressed word from the completed input slice into the
decode destination.  The loop index premise justifies both memory accesses,
and `overwritePrefix_set_next` records the exact logical progress. -/
theorem twp_func3_copy_decoded_word
    [WasmSmallStepGS hlc Universal.State]
    (source destination : UInt32)
    (original initial : List UInt32) (copied : Nat)
    (hlength : original.length = initial.length)
    (hcopied : copied < original.length)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let current := overwritePrefix original initial copied
    let next := overwritePrefix original initial (copied + 1)
    let sourceAddress := source + 4 * UInt32.ofNat copied
    let destinationAddress := destination + 4 * UInt32.ofNat copied
    iprop(
      WordSlice source original ∗
      WordSlice destination current ∗
      (WordSlice source original -∗
        WordSlice destination next -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨params, localValues,
            .i32 sourceAddress :: .i32 destinationAddress :: stack⟩,
          [.load32 0, .store32 0] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let current := overwritePrefix original initial copied
  let next := overwritePrefix original initial (copied + 1)
  let sourceAddress := source + 4 * UInt32.ofNat copied
  let destinationAddress := destination + 4 * UInt32.ofNat copied
  have hcurrentLength : current.length = original.length :=
    overwritePrefix_length original initial copied hlength
  have hsourceIndex : copied < original.length := hcopied
  have hdestinationIndex : copied < current.length := by
    rw [hcurrentLength]
    exact hcopied
  iintro ⟨Hsource, Hdestination, Hcont⟩
  ihave HsourceFacts := WordSlice_facts source original $$ Hsource
  icases HsourceFacts with ⟨Hsource, %hsourceFacts⟩
  ihave HdestinationFacts := WordSlice_facts destination current $$
    Hdestination
  icases HdestinationFacts with ⟨Hdestination, %hdestinationFacts⟩
  have hsourceAddress : sourceAddress.toNat = source.toNat + 4 * copied := by
    dsimp only [sourceAddress]
    exact wordOffset_toNat source copied (by omega)
  have hdestinationAddress :
      destinationAddress.toNat = destination.toNat + 4 * copied := by
    dsimp only [destinationAddress]
    exact wordOffset_toNat destination copied (by
      rw [hcurrentLength] at hdestinationFacts
      omega)
  have hsourceRoom : sourceAddress.toNat + 4 ≤ UInt32.size := by
    rw [hsourceAddress]
    omega
  have hdestinationRoom : destinationAddress.toNat + 4 ≤ UInt32.size := by
    rw [hdestinationAddress]
    rw [hcurrentLength] at hdestinationFacts
    omega
  have hsourceRoom' : sourceAddress.toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hsourceRoom
  have hdestinationRoom' : destinationAddress.toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hdestinationRoom
  obtain ⟨hsource1, hsource2, hsource3⟩ :=
    UInt32.addSteps4 sourceAddress hsourceRoom'
  obtain ⟨hdestination1, hdestination2, hdestination3⟩ :=
    UInt32.addSteps4 destinationAddress hdestinationRoom'
  ihave HsourceFocus := WordSlice_get source original copied hsourceIndex $$
    Hsource
  icases HsourceFocus with ⟨HsourceWord, HcloseSource⟩
  ihave HdestinationFocus := WordSlice_set destination current copied
    original[copied] hdestinationIndex $$ Hdestination
  icases HdestinationFocus with ⟨HdestinationWord, HcloseDestination⟩
  ihave HsourceWord' : pointsTo_u32 0 (sourceAddress + 0)
      original[copied] $$ [HsourceWord]
  · simp only [UInt32.add_zero, sourceAddress]
    iexact HsourceWord
  ihave HdestinationWord' : pointsTo_u32 0 (destinationAddress + 0)
      current[copied] $$ [HdestinationWord]
  · simp only [UInt32.add_zero, destinationAddress]
    iexact HdestinationWord
  simp only [List.cons_append, List.nil_append]
  iapply twp_load32 (address := sourceAddress) (offset := 0)
      original[copied] (by simp)
      (by simpa only [UInt32.add_zero] using hsource1)
      (by simpa only [UInt32.add_zero] using hsource2)
      (by simpa only [UInt32.add_zero] using hsource3) $$ HsourceWord'
  iintro HsourceLoaded
  ihave HsourceWord : pointsTo_u32 0
      (source + 4 * UInt32.ofNat copied) original[copied] $$ [HsourceLoaded]
  · simp only [UInt32.add_zero, sourceAddress]
    iexact HsourceLoaded
  iapply twp_store32 (address := destinationAddress) (offset := 0)
      current[copied] (by simp)
      (by simpa only [UInt32.add_zero] using hdestination1)
      (by simpa only [UInt32.add_zero] using hdestination2)
      (by simpa only [UInt32.add_zero] using hdestination3) $$ HdestinationWord'
  iintro HdestinationStored
  ihave HdestinationWord : pointsTo_u32 0
      (destination + 4 * UInt32.ofNat copied) original[copied] $$
      [HdestinationStored]
  · simp only [UInt32.add_zero, destinationAddress]
    iexact HdestinationStored
  ihave Hsource := HcloseSource $$ HsourceWord
  ihave Hdestination := HcloseDestination $$ HdestinationWord
  have hnext : current.set copied original[copied] = next := by
    exact overwritePrefix_set_next original initial copied hlength hcopied
  ihave Hnext : WordSlice destination next $$ [Hdestination]
  · rw [← hnext]
    iexact Hdestination
  iapply Hcont $$ Hsource Hnext

/-- The local-address form used by the generated tail loop (and by each
unrolled bulk store after its address arithmetic). -/
theorem twp_func3_copy_decoded_word_from_locals
    [WasmSmallStepGS hlc Universal.State]
    (source destination : UInt32)
    (original initial : List UInt32) (copied : Nat)
    (hlength : original.length = initial.length)
    (hcopied : copied < original.length)
    (destinationIndex sourceIndex : Nat)
    (params localValues stack : List Value)
    (hdestinationGet :
      (⟨params, localValues, stack⟩ : Locals).get destinationIndex =
        some (.i32 (destination + 4 * UInt32.ofNat copied)))
    (hsourceGet :
      (⟨params, localValues, stack⟩ : Locals).get sourceIndex =
        some (.i32 (source + 4 * UInt32.ofNat copied)))
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let current := overwritePrefix original initial copied
    let next := overwritePrefix original initial (copied + 1)
    iprop(
      WordSlice source original ∗
      WordSlice destination current ∗
      (WordSlice source original -∗
        WordSlice destination next -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨⟨params, localValues, stack⟩,
          [.localGet destinationIndex, .localGet sourceIndex,
            .load32 0, .store32 0] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  iintro Hresources
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet hdestinationGet
  have hsourceGet' :
      (⟨params, localValues,
        .i32 (destination + 4 * UInt32.ofNat copied) :: stack⟩ : Locals).get
          sourceIndex =
        some (.i32 (source + 4 * UInt32.ofNat copied)) := by
    simpa using hsourceGet
  iapply twp_localGet hsourceGet'
  have Hcopy := twp_func3_copy_decoded_word
    (hlc := hlc) source destination original initial copied hlength hcopied
    (params := params) (localValues := localValues) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [List.cons_append, List.nil_append] at Hcopy
  iapply Hcopy
  iexact Hresources

/-! ## Generated decode loops -/

/-- Exact body of the generated scalar decode loop.  The loop is entered only
when local 8 is positive, copies one word, advances both byte cursors, and
decrements local 8 before taking its back edge. -/
private def func3DecodeTailLoopBody : Program :=
  [.localGet 6, .localGet 3, .load32 0, .store32 0,
    .localGet 6, .const 4, .add, .localSet 6,
    .localGet 3, .const 4, .add, .localSet 3,
    .localGet 8, .const 4294967295, .add, .localTee 8, .br_if 0]

private structure Func3DecodeTailState where
  copied : Nat
  remaining : Nat

/-- Exact locals carried by the generated scalar decode loop.  `bulk` is kept
in local 9 until the loop has finished; the generated continuation then
replaces it with the total decoded length held in local 1. -/
private def func3DecodeTailLocals
    (source destination : UInt32) (length bulk : Nat)
    (aux10 : UInt32) (state : Func3DecodeTailState) : Locals :=
  func3AppendLocals (UInt32.ofNat length)
    (source + 4 * UInt32.ofNat state.copied)
    (destination + 4 * UInt32.ofNat state.copied)
    destination source (UInt32.ofNat bulk) (UInt32.ofNat (4 * length))
    (UInt32.ofNat state.remaining) (UInt32.ofNat bulk) aux10 []

private theorem func3_decode_next_address (base : UInt32) (index : Nat) :
    base + 4 * UInt32.ofNat index + 4 =
      base + 4 * UInt32.ofNat (index + 1) := by
  rw [UInt32.ofNat_add, UInt32.mul_add]
  simp
  ac_rfl

private theorem func3_decode_decrement {remaining : Nat}
    (hpositive : 0 < remaining)
    (hbound : remaining < UInt32.size) :
    UInt32.ofNat remaining + 4294967295 =
      UInt32.ofNat (remaining - 1) := by
  have hpred : remaining - 1 + 1 = remaining := by omega
  have hpredBound : remaining - 1 + 1 < UInt32.size := by omega
  have hremaining :
      UInt32.ofNat remaining = UInt32.ofNat (remaining - 1) + 1 := by
    rw [Wasm.Examples.MergeSort.u32_ofNat_succ hpredBound, hpred]
  have hmax : (4294967295 : UInt32) = 0 - 1 := by decide
  rw [hremaining, hmax]
  calc
    (UInt32.ofNat (remaining - 1) + 1) + (0 - 1) =
        UInt32.ofNat (remaining - 1) + ((0 - 1) + 1) := by ac_rfl
    _ = UInt32.ofNat (remaining - 1) := by
      rw [UInt32.sub_add_cancel, UInt32.add_zero]

/-- The generated scalar loop copies the final one to three decoded words.
The proof follows the actual loop back edge, with `remaining` as its
well-founded measure, and exposes the exact post-loop locals needed by the
subsequent scratch-allocation sequence. -/
theorem twp_func3_decode_tail_loop
    [WasmSmallStepGS hlc Universal.State]
    (source destination : UInt32)
    (original initial : List UInt32) (bulk remaining : Nat)
    (aux10 : UInt32)
    (hlength : original.length = initial.length)
    (hpartition : bulk + remaining = original.length)
    (hremaining : 0 < remaining)
    (hlengthBound : original.length < UInt32.size)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let initialState : Func3DecodeTailState :=
      { copied := bulk, remaining := remaining }
    let finalState : Func3DecodeTailState :=
      { copied := original.length, remaining := 0 }
    iprop(
      WordSlice source original ∗
      WordSlice destination (overwritePrefix original initial bulk) ∗
      (WordSlice source original -∗
        WordSlice destination original -∗
        WP (.running
          ⟨func3DecodeTailLocals source destination original.length bulk
              aux10 finalState,
            afterLoop, arity, remainder, controls, calls⟩ :
              Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3DecodeTailLocals source destination original.length bulk aux10
            initialState,
          [.loop 0 0 func3DecodeTailLoopBody] ++ afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let Finish : HeapIProp := iprop(
    WordSlice source original -∗
    WordSlice destination original -∗
    WP (.running
      ⟨func3DecodeTailLocals source destination original.length bulk aux10
          { copied := original.length, remaining := 0 },
        afterLoop, arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }])
  let Inv : Func3DecodeTailState → HeapIProp := fun state => iprop(
    ⌜state.copied + state.remaining = original.length ∧
      0 < state.remaining⌝ ∗
    WordSlice source original ∗
    WordSlice destination
      (overwritePrefix original initial state.copied) ∗
    Finish)
  iintro ⟨Hsource, Hdestination, Hfinish⟩
  simp only [List.cons_append, List.nil_append]
  iapply Project.Mergesort.SortProof.twp_loop_wf_family_from_terminal
    (ι := Func3DecodeTailState)
    (measure := fun state => state.remaining)
    (locals := func3DecodeTailLocals source destination original.length bulk
      aux10)
    (I := Inv)
    (initial := { copied := bulk, remaining := remaining })
    (initialLocals := func3DecodeTailLocals source destination
      original.length bulk aux10 { copied := bulk, remaining := remaining })
    (body := func3DecodeTailLoopBody) (code := afterLoop)
    (belowStack := []) rfl rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with ⟨%hstate, Hsource, Hdestination, Hfinish⟩
    have hcopied : state.copied < original.length := by omega
    have hremainingBound : state.remaining < UInt32.size := by omega
    have hdecrement :
        UInt32.ofNat state.remaining + 4294967295 =
          UInt32.ofNat (state.remaining - 1) :=
      func3_decode_decrement hstate.2 hremainingBound
    let next : Func3DecodeTailState :=
      { copied := state.copied + 1,
        remaining := state.remaining - 1 }
    have hnextPartition :
        next.copied + next.remaining = original.length := by
      dsimp only [next]
      omega
    have Hcopy := twp_func3_copy_decoded_word_from_locals
      (hlc := hlc) source destination original initial state.copied hlength
      hcopied 6 3 []
      (func3DecodeTailLocals source destination original.length bulk aux10
        state).locals []
      (by simp [func3DecodeTailLocals, func3AppendLocals])
      (by simp [func3DecodeTailLocals, func3AppendLocals])
      (code := func3DecodeTailLoopBody.drop 4)
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .loop, paramArity := 0, resultArity := 0,
          body := func3DecodeTailLoopBody, continuation := afterLoop,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3DecodeTailLoopBody, func3DecodeTailLocals,
      func3AppendLocals, List.cons_append, List.nil_append, List.drop]
      at Hcopy ⊢
    iapply Hcopy
    isplitl_exact Hsource
    isplitl_exact Hdestination
    iintro Hsource Hdestination
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4 : UInt32), func3_decode_next_address]
    wasm_twp_pures [twp_localSet]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4 : UInt32), func3_decode_next_address]
    wasm_twp_pures [twp_localSet]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4294967295 : UInt32), hdecrement]
    wasm_twp_pures [twp_localTee]
    simp only [List.length, List.set]
    by_cases hmore : 0 < next.remaining
    · have hnonzero : UInt32.ofNat next.remaining ≠ 0 := by
        intro hzero
        have hzeroNat := congrArg UInt32.toNat hzero
        rw [UInt32.toNat_ofNat_of_lt' (by omega)] at hzeroNat
        simp only [UInt32.toNat_zero] at hzeroNat
        omega
      iapply twp_brIf (condition := UInt32.ofNat next.remaining)
        (depth := 0) (arity := arity) (code := [])
        (targetCode := func3DecodeTailLoopBody)
        (targetControl :=
          { kind := .loop, paramArity := 0, resultArity := 0,
            body := func3DecodeTailLoopBody, continuation := afterLoop,
            belowStack := [] } :: controls)
        (targetValues := []) hnonzero (by rfl)
      simp only [func3DecodeTailLoopBody]
      ispecialize Hrec $$ %next
      isimp only [func3DecodeTailLoopBody, func3DecodeTailLocals,
        func3AppendLocals, next] at Hrec
      iapply Hrec
      · ipureintro
        omega
      isplitr_pureexact ⟨hnextPartition, hmore⟩
      iframe
    · have hzero : next.remaining = 0 := by omega
      have hcondition : UInt32.ofNat next.remaining = 0 := by simp [hzero]
      rw [hcondition]
      wasm_twp_pures [twp_brIfZero twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      have hcopiedFinal : next.copied = original.length := by omega
      have hcopiedFinal' : state.copied + 1 = original.length := by
        simpa only [next] using hcopiedFinal
      have hoverwriteFinal :
          overwritePrefix original initial (state.copied + 1) = original := by
        rw [hcopiedFinal']
        exact overwritePrefix_all original initial hlength
      isimp only [Finish] at Hfinish
      ihave Hfinish' := Hfinish $$ Hsource
      isimp only [hoverwriteFinal] at Hdestination
      rw [hcopiedFinal']
      isimp only [func3DecodeTailLocals, func3AppendLocals] at Hfinish'
      iapply Hfinish' $$ Hdestination
  · simp only [Inv, Finish]
    isplitr_pureexact ⟨hpartition, hremaining⟩
    iframe

/-- Exact body of the generated four-word unrolled decode loop. -/
private def func3DecodeBulkLoopBody : Program :=
  [.localGet 2, .localGet 3, .add, .localTee 6,
    .localGet 4, .localGet 3, .add, .localTee 1,
    .load32 0, .store32 0,
    .localGet 6, .const 4, .add,
    .localGet 1, .const 4, .add, .load32 0, .store32 0,
    .localGet 6, .const 8, .add,
    .localGet 1, .const 8, .add, .load32 0, .store32 0,
    .localGet 6, .const 12, .add,
    .localGet 1, .const 12, .add, .load32 0, .store32 0,
    .localGet 3, .const 16, .add, .localSet 3,
    .localGet 5, .localGet 9, .const 4, .add, .localTee 9,
    .ne, .br_if 0]

private structure Func3DecodeBulkState where
  copied : Nat
  aux1 : UInt32
  aux6 : UInt32

/-- Exact locals at the head of the generated unrolled loop.  Locals 1 and 6
are scratch address temporaries: their initial values are irrelevant, and
every back edge records the base addresses of the previous four-word group. -/
private def func3DecodeBulkLocals
    (source destination : UInt32) (length bulk tail : Nat)
    (aux10 : UInt32) (state : Func3DecodeBulkState) : Locals :=
  func3AppendLocals state.aux1 (UInt32.ofNat (4 * state.copied)) state.aux6
    destination source (UInt32.ofNat bulk) (UInt32.ofNat (4 * length))
    (UInt32.ofNat tail) (UInt32.ofNat state.copied) aux10 []

private theorem func3_decode_byte_offset (index : Nat) :
    UInt32.ofNat (4 * index) = 4 * UInt32.ofNat index := by
  rw [UInt32.ofNat_mul]
  rfl

private theorem func3_decode_address_increment
    (base : UInt32) (index increment : Nat) :
    base + 4 * UInt32.ofNat index + 4 * UInt32.ofNat increment =
      base + 4 * UInt32.ofNat (index + increment) := by
  rw [UInt32.ofNat_add, UInt32.mul_add]
  ac_rfl

private theorem func3_decode_address_add4 (base : UInt32) (index : Nat) :
    base + 4 * UInt32.ofNat index + 4 =
      base + 4 * UInt32.ofNat (index + 1) := by
  simpa only [show 4 * UInt32.ofNat 1 = (4 : UInt32) by decide] using
    func3_decode_address_increment base index 1

private theorem func3_decode_address_add8 (base : UInt32) (index : Nat) :
    base + 4 * UInt32.ofNat index + 8 =
      base + 4 * UInt32.ofNat (index + 2) := by
  simpa only [show 4 * UInt32.ofNat 2 = (8 : UInt32) by decide] using
    func3_decode_address_increment base index 2

private theorem func3_decode_address_add12 (base : UInt32) (index : Nat) :
    base + 4 * UInt32.ofNat index + 12 =
      base + 4 * UInt32.ofNat (index + 3) := by
  simpa only [show 4 * UInt32.ofNat 3 = (12 : UInt32) by decide] using
    func3_decode_address_increment base index 3

private theorem func3_decode_byte_offset_step (index : Nat) :
    4 * UInt32.ofNat index + 16 =
      UInt32.ofNat (4 * (index + 4)) := by
  rw [← func3_decode_byte_offset]
  rw [show 4 * (index + 4) = 4 * index + 16 by omega,
    UInt32.ofNat_add]
  rfl

private theorem func3_decode_count_step (index : Nat) :
    UInt32.ofNat index + 4 = UInt32.ofNat (index + 4) := by
  rw [UInt32.ofNat_add]
  rfl

/-- The generated unrolled loop copies exactly the largest multiple-of-four
prefix.  Its back edge advances by four words, and its terminating comparison
is justified from the same masked bulk count used by the generated code. -/
theorem twp_func3_decode_bulk_loop
    [WasmSmallStepGS hlc Universal.State]
    (source destination : UInt32)
    (original initial : List UInt32) (bulk tail : Nat)
    (initialAux1 initialAux6 aux10 : UInt32)
    (hlength : original.length = initial.length)
    (hpartition : bulk + tail = original.length)
    (hbulkPositive : 4 ≤ bulk)
    (hbulkMod : bulk % 4 = 0)
    (hlengthBound : original.length < UInt32.size)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let initialState : Func3DecodeBulkState :=
      { copied := 0, aux1 := initialAux1, aux6 := initialAux6 }
    let finalState : Func3DecodeBulkState :=
      { copied := bulk,
        aux1 := source + 4 * UInt32.ofNat (bulk - 4),
        aux6 := destination + 4 * UInt32.ofNat (bulk - 4) }
    iprop(
      WordSlice source original ∗ WordSlice destination initial ∗
      (WordSlice source original -∗
        WordSlice destination (overwritePrefix original initial bulk) -∗
        WP (.running
          ⟨func3DecodeBulkLocals source destination original.length bulk tail
              aux10 finalState,
            afterLoop, arity, remainder, controls, calls⟩ :
              Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3DecodeBulkLocals source destination original.length bulk tail
            aux10 initialState,
          [.loop 0 0 func3DecodeBulkLoopBody] ++ afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let Finish : HeapIProp := iprop(
    WordSlice source original -∗
    WordSlice destination (overwritePrefix original initial bulk) -∗
    WP (.running
      ⟨func3DecodeBulkLocals source destination original.length bulk tail
          aux10
          { copied := bulk,
            aux1 := source + 4 * UInt32.ofNat (bulk - 4),
            aux6 := destination + 4 * UInt32.ofNat (bulk - 4) },
        afterLoop, arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }])
  let Inv : Func3DecodeBulkState → HeapIProp := fun state => iprop(
    ⌜state.copied + 4 ≤ bulk ∧ state.copied % 4 = 0⌝ ∗
    WordSlice source original ∗
    WordSlice destination
      (overwritePrefix original initial state.copied) ∗
    Finish)
  iintro ⟨Hsource, Hdestination, Hfinish⟩
  simp only [List.cons_append, List.nil_append]
  iapply Project.Mergesort.SortProof.twp_loop_wf_family_from_terminal
    (ι := Func3DecodeBulkState)
    (measure := fun state => bulk - state.copied)
    (locals := func3DecodeBulkLocals source destination original.length bulk
      tail aux10)
    (I := Inv)
    (initial := { copied := 0, aux1 := initialAux1, aux6 := initialAux6 })
    (initialLocals := func3DecodeBulkLocals source destination
      original.length bulk tail aux10
      { copied := 0, aux1 := initialAux1, aux6 := initialAux6 })
    (body := func3DecodeBulkLoopBody) (code := afterLoop)
    (belowStack := []) rfl rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with ⟨%hstate, Hsource, Hdestination, Hfinish⟩
    have hbulkLe : bulk ≤ original.length := by omega
    have hcopy0 : state.copied < original.length := by omega
    have hcopy1 : state.copied + 1 < original.length := by omega
    have hcopy2 : state.copied + 2 < original.length := by omega
    have hcopy3 : state.copied + 3 < original.length := by omega
    let next : Func3DecodeBulkState :=
      { copied := state.copied + 4,
        aux1 := source + 4 * UInt32.ofNat state.copied,
        aux6 := destination + 4 * UInt32.ofNat state.copied }
    let addressedState : Func3DecodeBulkState :=
      { copied := state.copied,
        aux1 := source + 4 * UInt32.ofNat state.copied,
        aux6 := destination + 4 * UInt32.ofNat state.copied }
    simp only [func3DecodeBulkLoopBody, func3DecodeBulkLocals,
      func3AppendLocals]
    simp only [func3_decode_byte_offset]
    wasm_twp_pures [twp_localGet twp_localGet twp_add]
    rw [UInt32.add_comm (4 * UInt32.ofNat state.copied)]
    wasm_twp_pures [twp_localTee]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_localGet twp_localGet twp_add]
    rw [UInt32.add_comm (4 * UInt32.ofNat state.copied)]
    wasm_twp_pures [twp_localTee]
    simp only [List.length, List.set]
    have Hcopy0 := twp_func3_copy_decoded_word
      (hlc := hlc) source destination original initial state.copied hlength
      hcopy0 (params := [])
      (localValues := (func3DecodeBulkLocals source destination
        original.length bulk tail aux10 addressedState).locals)
      (stack := []) (code := func3DecodeBulkLoopBody.drop 10)
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .loop, paramArity := 0, resultArity := 0,
          body := func3DecodeBulkLoopBody, continuation := afterLoop,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3DecodeBulkLoopBody, func3DecodeBulkLocals,
      func3AppendLocals, addressedState, func3_decode_byte_offset,
      List.drop, List.cons_append, List.nil_append] at Hcopy0
    iapply Hcopy0
    isplitl_exact Hsource
    isplitl_exact Hdestination
    iintro Hsource Hdestination
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4 : UInt32), func3_decode_address_add4]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4 : UInt32), func3_decode_address_add4]
    have Hcopy1 := twp_func3_copy_decoded_word
      (hlc := hlc) source destination original initial (state.copied + 1)
      hlength hcopy1 (params := [])
      (localValues := (func3DecodeBulkLocals source destination
        original.length bulk tail aux10 addressedState).locals)
      (stack := []) (code := func3DecodeBulkLoopBody.drop 18)
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .loop, paramArity := 0, resultArity := 0,
          body := func3DecodeBulkLoopBody, continuation := afterLoop,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3DecodeBulkLoopBody, func3DecodeBulkLocals,
      func3AppendLocals, addressedState, func3_decode_byte_offset,
      List.drop, List.cons_append, List.nil_append] at Hcopy1
    iapply Hcopy1
    isplitl_exact Hsource
    isplitl_exact Hdestination
    iintro Hsource Hdestination
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (8 : UInt32), func3_decode_address_add8]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (8 : UInt32), func3_decode_address_add8]
    have Hcopy2 := twp_func3_copy_decoded_word
      (hlc := hlc) source destination original initial (state.copied + 2)
      hlength hcopy2 (params := [])
      (localValues := (func3DecodeBulkLocals source destination
        original.length bulk tail aux10 addressedState).locals)
      (stack := []) (code := func3DecodeBulkLoopBody.drop 26)
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .loop, paramArity := 0, resultArity := 0,
          body := func3DecodeBulkLoopBody, continuation := afterLoop,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3DecodeBulkLoopBody, func3DecodeBulkLocals,
      func3AppendLocals, addressedState, func3_decode_byte_offset,
      List.drop, List.cons_append, List.nil_append] at Hcopy2
    iapply Hcopy2
    isplitl_exact Hsource
    isplitl_exact Hdestination
    iintro Hsource Hdestination
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (12 : UInt32), func3_decode_address_add12]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (12 : UInt32), func3_decode_address_add12]
    have Hcopy3 := twp_func3_copy_decoded_word
      (hlc := hlc) source destination original initial (state.copied + 3)
      hlength hcopy3 (params := [])
      (localValues := (func3DecodeBulkLocals source destination
        original.length bulk tail aux10 addressedState).locals)
      (stack := []) (code := func3DecodeBulkLoopBody.drop 34)
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .loop, paramArity := 0, resultArity := 0,
          body := func3DecodeBulkLoopBody, continuation := afterLoop,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3DecodeBulkLoopBody, func3DecodeBulkLocals,
      func3AppendLocals, addressedState, func3_decode_byte_offset,
      List.drop, List.cons_append, List.nil_append] at Hcopy3
    iapply Hcopy3
    isplitl_exact Hsource
    isplitl_exact Hdestination
    iintro Hsource Hdestination
    have hcopiedFour : state.copied + 3 + 1 = state.copied + 4 := by omega
    isimp only [hcopiedFour] at Hdestination
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (16 : UInt32), func3_decode_byte_offset_step]
    wasm_twp_pures [twp_localSet]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4 : UInt32), func3_decode_count_step]
    wasm_twp_pures [twp_localTee]
    simp only [List.length, List.set]
    by_cases hmore : state.copied + 4 < bulk
    · have hnextBound : state.copied + 8 ≤ bulk := by
        omega
      have hnextMod : (state.copied + 4) % 4 = 0 := by omega
      have hnextLtSize : state.copied + 4 < UInt32.size := by omega
      have hbulkLtSize : bulk < UInt32.size := by omega
      have hne : UInt32.ofNat (state.copied + 4) ≠
          UInt32.ofNat bulk := by
        intro heq
        have hnat := congrArg UInt32.toNat heq
        rw [UInt32.toNat_ofNat_of_lt' hnextLtSize,
          UInt32.toNat_ofNat_of_lt' hbulkLtSize] at hnat
        omega
      have hcounterNe :
          ¬UInt32.ofNat bulk = UInt32.ofNat state.copied + 4 := by
        rw [func3_decode_count_step]
        exact fun heq => hne heq.symm
      iapply twp_ne (result := 1) (by simp [hcounterNe])
      iapply twp_brIf (condition := 1) (depth := 0) (arity := arity)
        (code := []) (targetCode := func3DecodeBulkLoopBody)
        (targetControl :=
          { kind := .loop, paramArity := 0, resultArity := 0,
            body := func3DecodeBulkLoopBody, continuation := afterLoop,
            belowStack := [] } :: controls)
        (targetValues := []) (by decide) (by rfl)
      simp only [func3DecodeBulkLoopBody]
      simp only [func3_decode_byte_offset]
      ispecialize Hrec $$ %next
      isimp only [func3DecodeBulkLoopBody, func3DecodeBulkLocals,
        func3AppendLocals, next] at Hrec
      iapply Hrec
      · ipureintro
        omega
      isplitr_pureexact ⟨hnextBound, hnextMod⟩
      iframe
    · have hdone : state.copied + 4 = bulk := by omega
      have heq : UInt32.ofNat (state.copied + 4) = UInt32.ofNat bulk := by
        rw [hdone]
      iapply twp_ne (result := 0) (by simp [heq])
      wasm_twp_pures [twp_brIfZero twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      have hprevious : state.copied = bulk - 4 := by omega
      isimp only [Finish] at Hfinish
      ihave Hfinish' := Hfinish $$ Hsource
      have hoverwrite :
          overwritePrefix original initial (state.copied + 4) =
            overwritePrefix original initial bulk := by rw [hdone]
      isimp only [hoverwrite] at Hdestination
      rw [hdone, hprevious]
      simp only [func3_decode_byte_offset]
      isimp only [func3DecodeBulkLocals, func3AppendLocals,
        func3_decode_byte_offset] at Hfinish'
      iapply Hfinish' $$ Hdestination
  · simp only [Inv, Finish, overwritePrefix_zero]
    isplitr_pureexact ⟨hbulkPositive, by simp⟩
    iframe

/-- Arithmetic and local initialization immediately following the values
null check. -/
private def func3DecodeSetup : Program :=
  [.localGet 7, .const 4294967292, .add, .localTee 6,
    .const 2, .shrU, .const 1, .add, .localTee 1,
    .const 3, .and, .localSet 8,
    .const 0, .localSet 9, .localGet 4, .localSet 3]

private theorem func3_decode_sub_four (length : Nat)
    (hpositive : 0 < length) :
    UInt32.ofNat (4 * length) + 4294967292 =
      UInt32.ofNat (4 * length - 4) := by
  have hsplit : 4 * length - 4 + 4 = 4 * length := by omega
  have hmax : (4294967292 : UInt32) = 0 - 4 := by decide
  calc
    UInt32.ofNat (4 * length) + 4294967292 =
        (UInt32.ofNat (4 * length - 4) + 4) + (0 - 4) := by
      rw [← hsplit, UInt32.ofNat_add, hmax]
      rfl
    _ = UInt32.ofNat (4 * length - 4) := by
      calc
        (UInt32.ofNat (4 * length - 4) + 4) + (0 - 4) =
            UInt32.ofNat (4 * length - 4) + ((0 - 4) + 4) := by ac_rfl
        _ = UInt32.ofNat (4 * length - 4) := by
          rw [UInt32.sub_add_cancel, UInt32.add_zero]

private theorem func3_decode_shift_two (length : Nat)
    (hpositive : 0 < length)
    (hbound : 4 * length < UInt32.size) :
    UInt32.ofNat (4 * length - 4) >>> (2 : UInt32) =
      UInt32.ofNat (length - 1) := by
  apply UInt32.toNat.inj
  have hsubBound : 4 * length - 4 < UInt32.size := by omega
  have hpredBound : length - 1 < UInt32.size := by omega
  rw [UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat_of_lt' hsubBound,
    UInt32.toNat_ofNat_of_lt' hpredBound]
  rw [show (2 : UInt32).toNat % 32 = 2 by decide,
    Nat.shiftRight_eq_div_pow]
  have hshape : 4 * length - 4 = 4 * (length - 1) := by omega
  rw [hshape]
  norm_num

private theorem func3_decode_tail_mask (length : Nat)
    (hbound : length < UInt32.size) :
    UInt32.ofNat length &&& (3 : UInt32) =
      UInt32.ofNat (length % 4) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_and,
    UInt32.toNat_ofNat_of_lt' hbound]
  have hthree : (3 : UInt32).toNat = 3 := by decide
  rw [hthree]
  have htailBound : length % 4 < UInt32.size := by
    have := Nat.mod_lt length (by decide : 0 < 4)
    norm_num [UInt32.size]
    omega
  rw [UInt32.toNat_ofNat_of_lt' htailBound]
  rw [show (3 : Nat) = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

/-- Execute the generated decode arithmetic and establish the exact bulk/tail
locals consumed by the two decode-loop proofs. -/
theorem twp_func3_decode_setup
    [WasmSmallStepGS hlc Universal.State]
    (source destination : UInt32) (length : Nat)
    (current aux5 aux8 aux9 aux10 : UInt32)
    (hpositive : 0 < length)
    (hbyteBound : 4 * length < 2147483648)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    WP (.running
      ⟨func3AppendLocals (UInt32.ofNat length) source
          (UInt32.ofNat (4 * length - 4)) destination source aux5
          (UInt32.ofNat (4 * length)) (UInt32.ofNat (length % 4)) 0 aux10 [],
        code, arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨func3AppendLocals source current (UInt32.ofNat (4 * length))
          destination source aux5 (UInt32.ofNat (4 * length)) aux8 aux9
          aux10 [],
        func3DecodeSetup ++ code,
        arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Φ }] := by
  iintro Hcont
  have hwordBound : 4 * length < UInt32.size := by
    norm_num [UInt32.size] at hbyteBound ⊢
    omega
  have hlengthBound : length < UInt32.size := by omega
  have hsub := func3_decode_sub_four length hpositive
  have hshift := func3_decode_shift_two length hpositive hwordBound
  have hsucc : UInt32.ofNat (length - 1) + 1 = UInt32.ofNat length := by
    have hpred : length - 1 + 1 = length := by omega
    have hpredBound : length - 1 + 1 < UInt32.size := by omega
    rw [Wasm.Examples.MergeSort.u32_ofNat_succ hpredBound, hpred]
  have htail := func3_decode_tail_mask length hlengthBound
  simp only [func3DecodeSetup, func3AppendLocals,
    List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [UInt32.add_comm (4294967292 : UInt32), hsub]
  wasm_twp_pures [twp_localTee]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_shrU]
  rw [show (2 % 32 : UInt32) = 2 by decide, hshift]
  wasm_twp_pures [twp_const twp_add]
  rw [UInt32.add_comm (1 : UInt32), hsucc]
  wasm_twp_pures [twp_localTee]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_and]
  rw [htail]
  wasm_twp_pures [twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_localGet twp_localSet]
  simp only [List.length, List.set]
  iexact Hcont

/-- Instructions common to the small-input and post-bulk scalar tails. -/
private def func3DecodeTailContinuation : Program :=
  [.localGet 9, .localGet 8, .add, .localSet 1,
    .localGet 2, .localGet 9, .const 2, .shl, .add, .localSet 6,
    .loop 0 0 func3DecodeTailLoopBody,
    .localGet 1, .localSet 9]

/-- Inner generated block: select the bulk path, execute it, and either leave
the outer block for a zero tail or prepare the scalar source cursor. -/
private def func3DecodeBulkBlockBody : Program :=
  [.localGet 6, .const 12, .ltU, .br_if 0,
    .localGet 1, .const 2147483644, .and, .localSet 5,
    .const 0, .localSet 9, .const 0, .localSet 3,
    .loop 0 0 func3DecodeBulkLoopBody,
    .localGet 8, .eqz, .br_if 1,
    .localGet 4, .localGet 3, .add, .localSet 3]

private def func3DecodeOuterBlockBody : Program :=
  [.block 0 0 func3DecodeBulkBlockBody] ++ func3DecodeTailContinuation

private def func3DecodeOuterFrame (afterDecode : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3DecodeOuterBlockBody, continuation := afterDecode,
    belowStack := [] }

private def func3DecodeBulkFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3DecodeBulkBlockBody,
    continuation := func3DecodeTailContinuation, belowStack := [] }

/-- Execute the common positive scalar tail, set local 9 to the total decoded
length, and leave the surrounding generated decode block. -/
theorem twp_func3_decode_positive_tail
    [WasmSmallStepGS hlc Universal.State]
    (source destination : UInt32)
    (original initial : List UInt32) (bulk tail : Nat)
    (aux1 aux6 aux10 : UInt32)
    (hlength : original.length = initial.length)
    (hpartition : bulk + tail = original.length)
    (htailPositive : 0 < tail)
    (hlengthBound : original.length < UInt32.size)
    {afterDecode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      WordSlice source original ∗
      WordSlice destination (overwritePrefix original initial bulk) ∗
      (WordSlice source original -∗
        WordSlice destination original -∗
        WP (.running
          ⟨func3AppendLocals (UInt32.ofNat original.length)
              (source + 4 * UInt32.ofNat original.length)
              (destination + 4 * UInt32.ofNat original.length)
              destination source (UInt32.ofNat bulk)
              (UInt32.ofNat (4 * original.length)) 0
              (UInt32.ofNat original.length) aux10 [],
            afterDecode, arity, remainder, controls, calls⟩ :
              Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals aux1
            (source + 4 * UInt32.ofNat bulk) aux6 destination source
            (UInt32.ofNat bulk) (UInt32.ofNat (4 * original.length))
            (UInt32.ofNat tail) (UInt32.ofNat bulk) aux10 [],
          func3DecodeTailContinuation,
          arity, remainder, func3DecodeOuterFrame afterDecode :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hsource, Hdestination, Hcont⟩
  have htotal :
      UInt32.ofNat tail + UInt32.ofNat bulk =
        UInt32.ofNat original.length := by
    calc
      UInt32.ofNat tail + UInt32.ofNat bulk =
          UInt32.ofNat bulk + UInt32.ofNat tail := UInt32.add_comm _ _
      _ = UInt32.ofNat (bulk + tail) := (UInt32.ofNat_add _ _).symm
      _ = UInt32.ofNat original.length := by rw [hpartition]
  simp only [func3DecodeTailContinuation, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_add]
  rw [htotal]
  wasm_twp_pures [twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
  rw [MemRegion.shl2_eq_mul4]
  wasm_twp_pures [twp_add]
  rw [UInt32.add_comm (4 * UInt32.ofNat bulk)]
  wasm_twp_pures [twp_localSet]
  simp only [List.length, List.set]
  have Htail := twp_func3_decode_tail_loop
    (hlc := hlc) source destination original initial bulk tail aux10 hlength
    hpartition htailPositive hlengthBound
    (afterLoop := [.localGet 1, .localSet 9])
    (arity := arity) (remainder := remainder)
    (controls := func3DecodeOuterFrame afterDecode :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3DecodeTailLoopBody, func3DecodeTailLocals,
    func3AppendLocals, List.cons_append, List.nil_append] at Htail
  simp only [func3DecodeTailLoopBody]
  iapply Htail
  isplitl_exact Hsource
  isplitl_exact Hdestination
  iintro Hsource Hdestination
  wasm_twp_pures [twp_localGet twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_exitControl]
  simp only [func3DecodeOuterFrame, List.take_zero, List.nil_append]
  iapply Hcont $$ Hsource Hdestination

/-- Compose the generated bulk/tail dispatcher.  The postcondition hides the
compiler's dead address temporaries but fixes local 9 to the authoritative
decoded word count and the destination contents to `original`. -/
theorem twp_func3_decode_blocks
    [WasmSmallStepGS hlc Universal.State]
    (source destination : UInt32)
    (original initial : List UInt32) (aux10 : UInt32)
    (hlength : original.length = initial.length)
    (hpositive : 0 < original.length)
    (hbyteBound : 4 * original.length < 2147483648)
    {afterDecode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      WordSlice source original ∗ WordSlice destination initial ∗
      ((∀ final1 : UInt32, ∀ final3 : UInt32, ∀ final6 : UInt32,
        ∀ final5 : UInt32, ∀ final8 : UInt32,
          WordSlice source original -∗ WordSlice destination original -∗
          WP (.running
            ⟨func3AppendLocals final1 final3 final6 destination source final5
                (UInt32.ofNat (4 * original.length)) final8
                (UInt32.ofNat original.length) aux10 [],
              afterDecode, arity, remainder, controls, calls⟩ :
                Expr Universal.State)
            @ s; E [{ Φ }]))) ⊢
      WP (.running
        ⟨func3AppendLocals (UInt32.ofNat original.length) source
            (UInt32.ofNat (4 * original.length - 4)) destination source 0
            (UInt32.ofNat (4 * original.length))
            (UInt32.ofNat (original.length % 4)) 0 aux10 [],
          [.block 0 0 func3DecodeOuterBlockBody] ++ afterDecode,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  let bulk := 4 * (original.length / 4)
  let tail := original.length % 4
  have hpartition : bulk + tail = original.length := by
    dsimp only [bulk, tail]
    exact bulk4_add_tail original.length
  have hlengthBound : original.length < UInt32.size := by
    norm_num [UInt32.size] at hbyteBound ⊢
    omega
  have hcountBound : original.length < 2147483648 := by omega
  have hbyteWordBound : 4 * original.length - 4 < UInt32.size := by
    norm_num [UInt32.size]
    omega
  have hbyteWord :
      (UInt32.ofNat (4 * original.length - 4)).toNat =
        4 * original.length - 4 :=
    UInt32.toNat_ofNat_of_lt' hbyteWordBound
  iintro ⟨Hsource, Hdestination, Hcont⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3DecodeOuterBlockBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3DecodeBulkBlockBody, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_const]
  by_cases hsmall : original.length < 4
  · have htail : tail = original.length := by
      dsimp only [tail]
      exact Nat.mod_eq_of_lt hsmall
    dsimp only [tail] at htail
    have hlt : UInt32.ofNat (4 * original.length - 4) < (12 : UInt32) := by
      rw [UInt32.lt_iff_toNat_lt, hbyteWord]
      have h12 : (12 : UInt32).toNat = 12 := by decide
      rw [h12]
      omega
    iapply twp_ltU (result := 1) (by simp [hlt])
    iapply twp_brIf (condition := 1) (depth := 0) (arity := arity)
      (targetCode := func3DecodeTailContinuation)
      (targetControl := func3DecodeOuterFrame afterDecode :: controls)
      (targetValues := []) (by decide) (by rfl)
    rw [htail]
    have Htail := twp_func3_decode_positive_tail
      (hlc := hlc) source destination original initial 0 original.length
      (UInt32.ofNat original.length)
      (UInt32.ofNat (4 * original.length - 4)) aux10 hlength
      (by simp) hpositive hlengthBound
      (afterDecode := afterDecode) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3DecodeTailContinuation, func3DecodeOuterFrame,
      func3AppendLocals, overwritePrefix_zero] at Htail ⊢
    simp only [show UInt32.ofNat 0 = 0 by decide, UInt32.mul_zero,
      UInt32.add_zero] at Htail
    iapply Htail
    isplitl_exact Hsource
    isplitl_exact Hdestination
    iintro Hsource Hdestination
    ihave Hfinal := Hcont $$
      %(UInt32.ofNat original.length)
      %(source + 4 * UInt32.ofNat original.length)
      %(destination + 4 * UInt32.ofNat original.length) %(0 : UInt32)
      %(0 : UInt32) Hsource Hdestination
    iexact Hfinal
  · have hbulkPositive : 4 ≤ bulk := by
      dsimp only [bulk]
      omega
    have hbulkMod : bulk % 4 = 0 := by
      dsimp only [bulk]
      omega
    have hnotLt : ¬UInt32.ofNat (4 * original.length - 4) <
        (12 : UInt32) := by
      rw [UInt32.lt_iff_toNat_lt, hbyteWord]
      have h12 : (12 : UInt32).toNat = 12 := by decide
      rw [h12]
      omega
    iapply twp_ltU (result := 0) (by simp [hnotLt])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_and]
    rw [bulk4_signedMask_eq original.length hcountBound]
    wasm_twp_pures [twp_localSet]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_const twp_localSet]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_const twp_localSet]
    simp only [List.length, List.set]
    have Hbulk := twp_func3_decode_bulk_loop
      (hlc := hlc) source destination original initial bulk tail
      (UInt32.ofNat original.length)
      (UInt32.ofNat (4 * original.length - 4)) aux10 hlength hpartition
      hbulkPositive hbulkMod hlengthBound
      (afterLoop := [.localGet 8, .eqz, .br_if 1,
        .localGet 4, .localGet 3, .add, .localSet 3])
      (arity := arity) (remainder := remainder)
      (controls := func3DecodeBulkFrame ::
        func3DecodeOuterFrame afterDecode :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3DecodeBulkLoopBody, func3DecodeBulkLocals,
      func3AppendLocals, List.cons_append, List.nil_append] at Hbulk
    simp only [func3DecodeBulkFrame, func3DecodeOuterFrame,
      func3DecodeBulkBlockBody, func3DecodeOuterBlockBody,
      func3DecodeBulkLoopBody, List.cons_append, List.nil_append,
      show UInt32.ofNat 0 = 0 by decide] at Hbulk
    simp only [func3DecodeBulkLoopBody]
    simp only [List.drop_zero]
    iapply Hbulk
    isplitl_exact Hsource
    isplitl_exact Hdestination
    iintro Hsource Hdestination
    wasm_twp_pures [twp_localGet]
    by_cases htailZero : tail = 0
    · rw [htailZero]
      iapply twp_eqz (result := 1) (by simp)
      iapply twp_brIf (condition := 1) (depth := 1) (arity := arity)
        (targetCode := afterDecode) (targetControl := controls)
        (targetValues := []) (by decide) (by rfl)
      have hbulkAll : bulk = original.length := by omega
      have hoverwrite :
          overwritePrefix original initial bulk = original := by
        rw [hbulkAll]
        exact overwritePrefix_all original initial hlength
      isimp only [hoverwrite] at Hdestination
      rw [hbulkAll]
      ihave Hfinal := Hcont $$
        %(source + 4 * UInt32.ofNat (original.length - 4))
        %(UInt32.ofNat (4 * original.length))
        %(destination + 4 * UInt32.ofNat (original.length - 4))
        %(UInt32.ofNat original.length) %(0 : UInt32)
        Hsource Hdestination
      iexact Hfinal
    · have htailPositive : 0 < tail := by omega
      have htailNonzero : UInt32.ofNat tail ≠ 0 := by
        intro hzero
        have hnat := congrArg UInt32.toNat hzero
        rw [UInt32.toNat_ofNat_of_lt' (by omega)] at hnat
        simp only [UInt32.toNat_zero] at hnat
        omega
      dsimp only [tail] at htailNonzero
      iapply twp_eqz (result := 0) (by simpa using htailNonzero)
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_add]
      simp only [func3_decode_byte_offset]
      rw [UInt32.add_comm (4 * UInt32.ofNat bulk) source]
      wasm_twp_pures [twp_localSet]
      simp only [List.length, List.set]
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      have Htail := twp_func3_decode_positive_tail
        (hlc := hlc) source destination original initial bulk tail
        (source + 4 * UInt32.ofNat (bulk - 4))
        (destination + 4 * UInt32.ofNat (bulk - 4)) aux10 hlength
        hpartition htailPositive hlengthBound
        (afterDecode := afterDecode) (arity := arity)
        (remainder := remainder) (controls := controls) (calls := calls)
        (s := s) (E := E) (Φ := Φ)
      simp only [func3DecodeTailContinuation, func3DecodeOuterFrame,
        func3DecodeOuterBlockBody, func3DecodeBulkBlockBody,
        func3DecodeBulkLoopBody, func3AppendLocals,
        func3_decode_byte_offset, List.cons_append, List.nil_append] at Htail ⊢
      iapply Htail
      isplitl_exact Hsource
      isplitl_exact Hdestination
      iintro Hsource Hdestination
      ihave Hfinal := Hcont $$
        %(UInt32.ofNat original.length)
        %(source + 4 * UInt32.ofNat original.length)
        %(destination + 4 * UInt32.ofNat original.length)
        %(UInt32.ofNat bulk) %(0 : UInt32) Hsource Hdestination
      iexact Hfinal

/-- From a normal values-allocation result, exclude the generated null edge,
open the completed input Vec and fresh allocation as word arrays, execute the
entire decode, and reseal the values allocation with contents `original`.
All compiler address temporaries remain hidden behind the continuation. -/
theorem twp_func3_decode_allocated
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId : Nat)
    (capacity source destination : UInt32)
    (original : List UInt32)
    (chunkBytes outputBytes bytes : List UInt8)
    (frontier : Nat) (history : AllocationHistory)
    (current aux2 aux8 aux9 aux10 : UInt32)
    (horiginal : original ≠ [])
    (hgeo : GeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity source frontier history)
    {afterDecode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := 4 * original.length, alignment := 4 }
    iprop(
      ExportFrame heapId capacity source (serialize original) chunkBytes
          outputBytes ∗
      LiveBlock heapId valuesId destination layout bytes ∗
      ((∀ final1 : UInt32, ∀ final3 : UInt32, ∀ final6 : UInt32,
        ∀ final5 : UInt32, ∀ final8 : UInt32,
          ExportFrame heapId capacity source (serialize original) chunkBytes
              outputBytes -∗
          LiveWordBlock heapId valuesId destination original -∗
          WP (.running
            ⟨func3AppendLocals final1 final3 final6 destination source final5
                (UInt32.ofNat (4 * original.length)) final8
                (UInt32.ofNat original.length) aux10 [],
              afterDecode, arity, remainder, controls, calls⟩ :
                Expr Universal.State)
            @ s; E [{ Φ }]))) ⊢
      WP (.running
        ⟨func3AppendLocals source current
            (UInt32.ofNat (4 * original.length)) aux2 source 0
            (UInt32.ofNat (4 * original.length)) aux8 aux9 aux10
            [.i32 destination],
          [.localTee 2, .eqz, .br_if 1] ++ func3DecodeSetup ++
            [.block 0 0 func3DecodeOuterBlockBody] ++ afterDecode,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := 4 * original.length, alignment := 4 }
  have hpositive : 0 < original.length :=
    List.length_pos_iff_ne_nil.mpr horiginal
  have hbyteBound : 4 * original.length < 2147483648 := by
    have htotal := GeometricVecFacts.completed_lt_signed
      (serialize original).length (serialize original).length 0 capacity
      source frontier history hgeo rfl
    simpa only [serialize_length] using htotal
  iintro ⟨Hframe, Hblock, Hcont⟩
  have Hguard := twp_func3_values_nonnull_guard
    (hlc := hlc) heapId valuesId destination layout bytes source current
    (UInt32.ofNat (4 * original.length)) aux2 source 0
    (UInt32.ofNat (4 * original.length)) aux8 aux9 aux10
    (stack := [])
    (code := func3DecodeSetup ++
      [.block 0 0 func3DecodeOuterBlockBody] ++ afterDecode)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [List.cons_append, List.nil_append] at Hguard ⊢
  iapply Hguard
  iframe; iintro Hblock
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨HallocationToken, HallocationBytes, %hblockFacts⟩
  have hbytes : bytes.length = 4 * original.length := by
    simpa only [layout] using hblockFacts.1
  have hdecodedLength : (decodeWords bytes).length = original.length :=
    (serialize_decodeWords_of_length bytes original.length hbytes).2
  ihave Hblock : LiveBlock heapId valuesId destination layout bytes $$
      [HallocationToken HallocationBytes]
  · unfold LiveBlock
    iframe
    ipureexact hblockFacts
  ihave Hbuffers := DriverDecodeBuffers_open heapId capacity source destination
    valuesId original chunkBytes outputBytes bytes frontier history horiginal
    hgeo $$ [Hframe Hblock]
  · iframe
  icases Hbuffers with ⟨Hsource, HcloseSource, Hvalues⟩
  isimp only [LiveWordBlock] at Hvalues
  icases Hvalues with ⟨Htoken, Hdestination, %hnonnull⟩
  isimp only [hdecodedLength] at Htoken
  have Hsetup := twp_func3_decode_setup
    (hlc := hlc) source destination original.length current 0 aux8 aux9
    aux10 hpositive hbyteBound
    (code := [.block 0 0 func3DecodeOuterBlockBody] ++ afterDecode)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3DecodeSetup, List.cons_append, List.nil_append] at Hsetup ⊢
  iapply Hsetup
  have Hdecode := twp_func3_decode_blocks
    (hlc := hlc) source destination original (decodeWords bytes) aux10
    hdecodedLength.symm
    hpositive hbyteBound
    (afterDecode := afterDecode) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3DecodeOuterBlockBody, List.cons_append, List.nil_append]
    at Hdecode ⊢
  iapply Hdecode
  isplitl_exact Hsource
  isplitl_exact Hdestination
  iintro %final1
  iintro %final3
  iintro %final6
  iintro %final5
  iintro %final8
  iintro Hsource Hdestination
  ihave Hframe := HcloseSource $$ Hsource
  ihave Hvalues : LiveWordBlock heapId valuesId destination original $$
      [Htoken Hdestination]
  · unfold LiveWordBlock
    iframe
    ipureexact hnonnull
  iapply Hcont $$ %final1 %final3 %final6 %final5 %final8 Hframe Hvalues

/-- Execute the allocation marker and zeroing scratch allocation after decode.
The valid layout follows from the same signed byte bound used by the decode;
the allocator's only exceptional result is repackaged as `.scratch` OOM. -/
theorem twp_func3_allocate_scratch
    [WasmSmallStepGS hlc Universal.State]
    (hfunc9 : Func9Spec (hlc := hlc))
    (heapId : GName) (valuesId : Nat)
    (capacity source valuesPtr : UInt32)
    (original : List UInt32)
    (chunkBytes outputBytes shadow : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (final1 final3 final6 final5 final8 aux10 : UInt32)
    (hpositive : 0 < original.length)
    (hbyteBound : 4 * original.length < 2147483648)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvaluesEnd : valuesPtr.toNat + 4 * original.length ≤ frontier)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := 4 * original.length, alignment := 4 }
    let callerLocals :=
      func3AppendLocals final1 final3 final6 valuesPtr source final5
        (UInt32.ofNat (4 * original.length)) final8
        (UInt32.ofNat original.length) (UInt32.ofNat (4 * original.length)) []
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity source (serialize original) chunkBytes
        outputBytes ∗
      LiveWordBlock heapId valuesId valuesPtr original ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      ((∀ scratch : UInt32, ∀ finish : UInt32,
          ⌜classifyBump frontier layout = .success scratch finish⌝ -∗
          RuntimeContext -∗
          StackPointer driverBase -∗
          StackReserve reserveBase shadow -∗
          ExportFrame heapId capacity source (serialize original) chunkBytes
            outputBytes -∗
          LiveWordBlock heapId valuesId valuesPtr original -∗
          BumpHeap heapId finish finish.toNat
            (history.allocate scratch layout) -∗
          LiveBlock heapId history.nextId scratch layout
            (List.replicate layout.size 0) -∗
          Streams [] [] false -∗
          ⌜MemRegion.Disjoint
            ⟨valuesPtr, 4 * original.length⟩
            ⟨scratch, 4 * original.length⟩⌝ -∗
          ResumeWP [.i32 scratch] callerLocals [] code arity remainder controls
            calls s E Φ) ∧
        (DriverScratchOOM heapId original -∗
          Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨func3AppendLocals final1 final3 final6 valuesPtr source final5
            (UInt32.ofNat (4 * original.length)) final8
            (UInt32.ofNat original.length) aux10 [],
          [.call 7, .localGet 9, .const 2, .shl, .localTee 10,
            .const 4, .call 12] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := 4 * original.length, alignment := 4 }
  let callerLocals :=
    func3AppendLocals final1 final3 final6 valuesPtr source final5
      (UInt32.ofNat (4 * original.length)) final8
      (UInt32.ofNat original.length) (UInt32.ofNat (4 * original.length)) []
  have hwordBound : 4 * original.length < UInt32.size := by
    norm_num [UInt32.size] at hbyteBound ⊢
    omega
  have hsizeWord :
      (UInt32.ofNat (4 * original.length)).toNat = 4 * original.length :=
    UInt32.toNat_ofNat_of_lt' hwordBound
  have hlayoutValid : layout.Valid := by
    exact align4Layout_valid_of_bounds (4 * original.length)
      (by omega) hbyteBound (by omega)
  have hlayoutMatches :
      layout.Matches (UInt32.ofNat (4 * original.length)) 4 := by
    unfold AllocLayout.Matches layout
    simp only [hsizeWord]
    decide
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hvalues, Hbump, Hstreams, Hcont⟩
  simp only [List.cons_append, List.nil_append]
  have Hmarker := Project.Mergesort.ContractProofs.func4_correct
    (hlc := hlc)
    (callerLocals := func3AppendLocals final1 final3 final6 valuesPtr source
      final5 (UInt32.ofNat (4 * original.length)) final8
      (UInt32.ofNat original.length) aux10 [])
    (stack := [])
    (code := [.localGet 9, .const 2, .shl, .localTee 10,
      .const 4, .call 12] ++ code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func4Spec CallContract callExpr at Hmarker
  simp only [List.cons_append, List.nil_append] at Hmarker
  simp only [func3AppendLocals] at Hmarker ⊢
  iapply Hmarker
  iframe; iintro Hruntime
  unfold ResumeWP resumeExpr
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_shl]
  rw [MemRegion.shl2_eq_mul4, ← func3_decode_byte_offset]
  wasm_twp_pures [twp_localTee]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const]
  have Halloc := hfunc9
    (size := UInt32.ofNat (4 * original.length)) (alignment := 4)
    (layout := layout) (heapId := heapId) (storedCursor := storedCursor)
    (frontier := frontier) (history := history)
    (input := []) (output := []) (raised := false)
    (callerLocals := callerLocals) (stack := []) (code := code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func9Spec CallContract callExpr at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  dsimp only [callerLocals] at Halloc
  simp only [func3AppendLocals] at Halloc
  iapply Halloc
  isplitl_exact Hruntime
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isplitl_pureexact ⟨hlayoutMatches, hlayoutValid, rfl⟩
  unfold ZeroAllocContinuation
  cases hdecision : classifyBump frontier layout with
  | oom =>
      iintro Hbump Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      iapply Hoom
      unfold DriverScratchOOM
      iexists capacity, source, valuesPtr, valuesId, chunkBytes, outputBytes,
        shadow, storedCursor, frontier, history
      isplitl_pureexact hpositive
      iframe
  | success scratch finish =>
      have hscratchStart : frontier ≤ scratch.toNat :=
        (classifyBump_success_reachable frontier layout scratch finish
          hfrontier hlayoutValid (Or.inr rfl) hdecision).1
      have hdisjoint : MemRegion.Disjoint
          ⟨valuesPtr, 4 * original.length⟩
          ⟨scratch, 4 * original.length⟩ :=
        wordRegions_disjoint_of_order valuesPtr scratch original original
          (Nat.le_trans hvaluesEnd hscratchStart)
      isplit
      · iintro Hruntime Hbump Hscratch Hstreams
        ihave Hnormal := BI.and_elim_l $$ Hcont
        ihave Hresume := Hnormal $$ %scratch %finish %rfl Hruntime Hsp Hreserve
          Hframe Hvalues Hbump Hscratch Hstreams %hdisjoint
        iunfold ResumeWP
        simp only [resumeExpr, List.cons_append, List.nil_append]
        iexact Hresume
      · iintro Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom
        unfold DriverScratchOOM
        iexists capacity, source, valuesPtr, valuesId, chunkBytes, outputBytes,
          shadow, storedCursor, frontier, history
        isplitl_pureexact hpositive
        iframe

/-- Exact success tail following the generated zeroed scratch allocation. -/
private def func3ScratchSuccessTail : Program :=
  [.localTee 8, .eqz, .br_if 2,
    .localGet 7, .const 2, .shrU, .localSet 1,
    .const 0, .localSet 5, .br 4]

private theorem func3_scratch_count_shift
    (length : Nat) (hbound : 4 * length < UInt32.size) :
    UInt32.ofNat (4 * length) >>> (2 : UInt32) = UInt32.ofNat length := by
  apply UInt32.toNat.inj
  have hlengthBound : length < UInt32.size := by omega
  rw [UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat_of_lt' hbound,
    UInt32.toNat_ofNat_of_lt' hlengthBound]
  rw [show (2 : UInt32).toNat % 32 = 2 by decide,
    Nat.shiftRight_eq_div_pow]
  norm_num

/-- Discharge the scratch allocator's generated null check from the returned
live block, restore the element count, clear the scratch-skip flag, and take
the real depth-four branch to the shared sort/output continuation. -/
theorem twp_func3_scratch_success_tail
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (scratchId : Nat) (scratch : UInt32)
    (layout : AllocLayout) (bytes : List UInt8)
    (length : Nat)
    (final1 final3 final6 valuesPtr source final5 final8 : UInt32)
    (hbyteBound : 4 * length < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls targetControls : List ControlFrame}
    {targetCode : Program} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp}
    (hbranch : branchTarget? arity 4 controls [] =
      some (targetCode, targetControls, [])) :
    iprop(
      LiveBlock heapId scratchId scratch layout bytes ∗
      (LiveBlock heapId scratchId scratch layout bytes -∗
        WP (.running
          ⟨func3AppendLocals (UInt32.ofNat length) final3 final6 valuesPtr
              source 0 (UInt32.ofNat (4 * length)) scratch
              (UInt32.ofNat length) (UInt32.ofNat (4 * length)) [],
            targetCode, arity, remainder, targetControls, calls⟩ :
              Expr Universal.State) @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3AppendLocals final1 final3 final6 valuesPtr source final5
            (UInt32.ofNat (4 * length)) final8 (UInt32.ofNat length)
            (UInt32.ofNat (4 * length)) [.i32 scratch],
          func3ScratchSuccessTail, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hscratch, Hcont⟩
  isimp only [LiveBlock] at Hscratch
  icases Hscratch with ⟨Htoken, Hbytes, %hfacts⟩
  simp only [func3ScratchSuccessTail, func3AppendLocals]
  wasm_twp_pures [twp_localTee]
  simp only [List.length, List.set]
  iapply twp_eqz (result := 0) (by simp [hfacts.2.1])
  wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_shrU]
  rw [show (2 : UInt32) % 32 = 2 by decide,
    func3_scratch_count_shift length hbyteBound]
  wasm_twp_pures [twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  iapply twp_br hbranch
  ihave Hscratch : LiveBlock heapId scratchId scratch layout bytes $$
      [Htoken Hbytes]
  · unfold LiveBlock
    iframe
    ipureexact hfacts
  iapply Hcont $$ Hscratch

/-- Frame both allocation tokens around the single generated `func2` call.
The sort contract supplies the sorted-permutation fact and the precise
piecewise scratch contents needed to reseal both complete live blocks. -/
theorem twp_func3_sort
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId scratchId : Nat)
    (valuesPtr scratchPtr source : UInt32)
    (original : List UInt32)
    (final1 final3 final6 final5 aux10 : UInt32)
    (hdisjoint : MemRegion.Disjoint
      ⟨valuesPtr, 4 * original.length⟩
      ⟨scratchPtr, 4 * original.length⟩)
    (hbyteBound : 4 * original.length < UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := 4 * original.length, alignment := 4 }
    let scratchInitial := List.replicate original.length (0 : UInt32)
    let scratchResult := fun sorted : List UInt32 =>
      if original.length ≤ 1 then scratchInitial else sorted
    iprop(
      RuntimeContext ∗
      LiveWordBlock heapId valuesId valuesPtr original ∗
      LiveBlock heapId scratchId scratchPtr layout
        (List.replicate layout.size 0) ∗
      (∀ sorted : List UInt32,
        RuntimeContext -∗
        LiveWordBlock heapId valuesId valuesPtr sorted -∗
        LiveWordBlock heapId scratchId scratchPtr (scratchResult sorted) -∗
        ⌜SortedPermutation original sorted⌝ -∗
        WP (.running
          ⟨func3AppendLocals final1 final3 final6 valuesPtr source final5
              (UInt32.ofNat (4 * original.length)) scratchPtr
              (UInt32.ofNat original.length) aux10 [],
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals final1 final3 final6 valuesPtr source final5
            (UInt32.ofNat (4 * original.length)) scratchPtr
            (UInt32.ofNat original.length) aux10 [],
          [.localGet 2, .localGet 9, .localGet 8, .localGet 9, .call 5] ++
            code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := 4 * original.length, alignment := 4 }
  let scratchInitial := List.replicate original.length (0 : UInt32)
  let scratchResult := fun sorted : List UInt32 =>
    if original.length ≤ 1 then scratchInitial else sorted
  iintro ⟨Hruntime, Hvalues, Hscratch, Hcont⟩
  ihave HscratchWords :
      LiveWordBlock heapId scratchId scratchPtr scratchInitial $$ [Hscratch]
  · iapply (zeroLiveBlock_as_liveWordBlock heapId scratchId original.length
      scratchPtr).mp $$ Hscratch
  ihave Hfocus := LiveWordBlocks_sortFocus heapId valuesId scratchId valuesPtr
    scratchPtr original scratchInitial (by simp [scratchInitial])
    (by simpa [scratchInitial] using hdisjoint) $$ [Hvalues HscratchWords]
  · iframe
  icases Hfocus with ⟨Hbuffers, HcloseBuffers⟩
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  have Hsort := Project.Mergesort.ContractProofs.func2_correct
    (hlc := hlc) (source := valuesPtr)
    (n := UInt32.ofNat original.length) (scratch := scratchPtr)
    (scratchN := UInt32.ofNat original.length)
    (input := original) (scratchInput := scratchInitial)
    (callerLocals := func3AppendLocals final1 final3 final6 valuesPtr source
      final5 (UInt32.ofNat (4 * original.length)) scratchPtr
      (UInt32.ofNat original.length) aux10 [])
    (stack := []) (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func2Spec CallContract callExpr at Hsort
  simp only [List.cons_append, List.nil_append, func3AppendLocals] at Hsort
  iapply Hsort
  isplitl_exact Hruntime
  isplitl_exact Hbuffers
  isplitl []
  · ipureintro
    have hcountBound : original.length < UInt32.size := by omega
    simp [scratchInitial, UInt32.toNat_ofNat_of_lt' hcountBound]
  iintro %sorted Hruntime Hresult
  isimp only [SortResultBuffers] at Hresult
  icases Hresult with ⟨Hbuffers, %hsorted⟩
  have hsortedLength : sorted.length = original.length :=
    hsorted.2.length_eq.symm
  have hscratchLength : (scratchResult sorted).length = scratchInitial.length := by
    simp only [scratchResult]
    split
    · rfl
    · simp [scratchInitial, hsortedLength]
  have hresultLengths :
      sorted.length = original.length ∧
        (scratchResult sorted).length = scratchInitial.length :=
    ⟨hsortedLength, hscratchLength⟩
  ihave Hblocks := HcloseBuffers $$ %sorted %(scratchResult sorted)
    %hresultLengths Hbuffers
  icases Hblocks with ⟨Hvalues, Hscratch⟩
  ihave Hresume := Hcont $$ %sorted Hruntime Hvalues Hscratch %hsorted
  iunfold ResumeWP
  simp only [resumeExpr, List.nil_append]
  iexact Hresume

/-- Emit one sorted word through the driver's reusable four-byte frame slot.
The source read is justified by the loop index, the slot is reassembled with
the singleton canonical serialization, and `func11` appends exactly it. -/
theorem twp_func3_write_one
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8)
    (sorted : List UInt32) (emitted : Nat)
    (aux1 aux6 aux4 aux5 aux7 aux8 aux10 : UInt32)
    (hemitted : emitted < sorted.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      ExportFrame heapId capacity inputPtr input chunkBytes outputBytes ∗
      WordSlice valuesPtr sorted ∗
      Streams [] (serialize (sorted.take emitted)) false ∗
      (RuntimeContext -∗
        ExportFrame heapId capacity inputPtr input chunkBytes
          (serialize [sorted[emitted]]) -∗
        WordSlice valuesPtr sorted -∗
        Streams []
          (serialize (sorted.take emitted) ++ serialize [sorted[emitted]])
          false -∗
        WP (.running
          ⟨func3AppendLocals aux1
              (valuesPtr + 4 * UInt32.ofNat emitted) aux6 valuesPtr aux4 aux5
              aux7 aux8 (UInt32.ofNat sorted.length) aux10 [],
            code, arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals aux1
            (valuesPtr + 4 * UInt32.ofNat emitted) aux6 valuesPtr aux4 aux5
            aux7 aux8 (UInt32.ofNat sorted.length) aux10 [],
          [.localGet 0, .localGet 3, .load32 0, .store32 268,
            .localGet 0, .const 268, .add, .const 4, .call 14] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hframe, Hvalues, Hstreams, Hcont⟩
  isimp only [ExportFrame] at Hframe
  icases Hframe with ⟨Hvec, Hchunk, Houtput, %hframeLengths⟩
  ihave HvalueFacts := WordSlice_facts valuesPtr sorted $$ Hvalues
  icases HvalueFacts with ⟨Hvalues, %hvalueFacts⟩
  have haddress :
      (valuesPtr + 4 * UInt32.ofNat emitted).toNat =
        valuesPtr.toNat + 4 * emitted :=
    wordOffset_toNat valuesPtr emitted (by omega)
  have hroom :
      (valuesPtr + 4 * UInt32.ofNat emitted).toNat + 4 ≤ UInt32.size := by
    rw [haddress]
    omega
  obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4
    (valuesPtr + 4 * UInt32.ofNat emitted) (by
      simpa only [UInt32.size] using hroom)
  ihave HvalueFocus := WordSlice_get valuesPtr sorted emitted hemitted $$ Hvalues
  icases HvalueFocus with ⟨Hvalue, HcloseValue⟩
  ihave HoutputFocus := ByteSlice_storeWordFocus (driverBase + 268)
    outputBytes sorted[emitted] hframeLengths.2 (by decide) $$ Houtput
  icases HoutputFocus with ⟨HoldOutput, HcloseOutput⟩
  ihave Hvalue' : pointsTo_u32 0
      (valuesPtr + 4 * UInt32.ofNat emitted + 0) sorted[emitted] $$ [Hvalue]
  · simp only [UInt32.add_zero]
    iexact Hvalue
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_load32
    (address := valuesPtr + 4 * UInt32.ofNat emitted) (offset := 0)
    sorted[emitted] (by simp)
    (by simpa only [UInt32.add_zero] using h1)
    (by simpa only [UInt32.add_zero] using h2)
    (by simpa only [UInt32.add_zero] using h3) $$ Hvalue'
  iintro HvalueLoaded
  ihave Hvalue : pointsTo_u32 0
      (valuesPtr + 4 * UInt32.ofNat emitted) sorted[emitted] $$ [HvalueLoaded]
  · simp only [UInt32.add_zero]
    iexact HvalueLoaded
  ihave Hvalues := HcloseValue $$ Hvalue
  wasm_twp_bind twp_store32 (address := driverBase) (offset := 268)
      (Spec.decodeWord outputBytes) (by decide) (by decide) (by decide)
      (by decide) with HoldOutput => Houtput
  ihave Houtput := HcloseOutput $$ Houtput
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [UInt32.add_comm (268 : UInt32)]
  wasm_twp_pures [twp_const]
  have Hwrite := Project.Mergesort.ContractProofs.func11_correct
    (hlc := hlc) (ptr := driverBase + 268) (requested := 4)
    (bytes := serialize [sorted[emitted]]) (input := [])
    (output := serialize (sorted.take emitted)) (raised := false)
    (callerLocals := func3AppendLocals aux1
      (valuesPtr + 4 * UInt32.ofNat emitted) aux6 valuesPtr aux4 aux5 aux7
      aux8 (UInt32.ofNat sorted.length) aux10 [])
    (stack := []) (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hwrite
  simp only [List.cons_append, List.nil_append, func3AppendLocals] at Hwrite
  iapply Hwrite
  isplitl_exact Hruntime
  isplitl_exact Hstreams
  isplitl_exact Houtput
  isplitl []
  · ipureintro
    constructor
    · change 4 = (Spec.u32Codec.encode sorted[emitted]).length
      exact (Spec.u32Codec.encode_length sorted[emitted]).symm
    · decide
  iintro Hruntime Hstreams Houtput
  ihave Hframe : ExportFrame heapId capacity inputPtr input chunkBytes
      (serialize [sorted[emitted]]) $$ [Hvec Hchunk Houtput]
  · unfold ExportFrame
    iframe
    ipureintro
    refine ⟨hframeLengths.1, ?_⟩
    change (Spec.u32Codec.encode sorted[emitted]).length = 4
    exact Spec.u32Codec.encode_length sorted[emitted]
  ihave Hresume := Hcont $$ Hruntime Hframe Hvalues Hstreams
  iunfold ResumeWP
  simp only [resumeExpr, List.nil_append]
  iexact Hresume

/-- Exact body of the generated loop which serializes each sorted word through
the reusable four-byte output slot. -/
private def func3OutputLoopBody : Program :=
  [.localGet 0, .localGet 3, .load32 0, .store32 268,
    .localGet 0, .const 268, .add, .const 4, .call 14,
    .localGet 3, .const 4, .add, .localSet 3,
    .localGet 6, .const 4294967292, .add, .localTee 6, .br_if 0]

/-- Exact driver locals at the head of an output-loop iteration.  `emitted`
determines both the source cursor and the byte countdown; all other generated
temporaries are threaded unchanged. -/
private def func3OutputLocals
    (valuesPtr : UInt32) (sorted : List UInt32)
    (aux1 aux4 aux5 aux7 aux8 aux10 : UInt32) (emitted : Nat) : Locals :=
  func3AppendLocals aux1
    (valuesPtr + 4 * UInt32.ofNat emitted)
    (UInt32.ofNat (4 * (sorted.length - emitted)))
    valuesPtr aux4 aux5 aux7 aux8 (UInt32.ofNat sorted.length) aux10 []

private theorem func3_output_countdown_step
    {length emitted : Nat} (hemitted : emitted < length) :
    UInt32.ofNat (4 * (length - emitted)) + 4294967292 =
      UInt32.ofNat (4 * (length - (emitted + 1))) := by
  have hsub := func3_decode_sub_four (length - emitted) (by omega)
  rw [show 4 * (length - emitted) - 4 =
      4 * (length - (emitted + 1)) by omega] at hsub
  exact hsub

/-- The generated output loop emits precisely the canonical serialization of
the sorted array.  This is a partial-correctness loop rule: it identifies the
normal state after the loop without asserting that execution terminates. -/
theorem twp_func3_output_loop
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId : Nat)
    (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8)
    (sorted : List UInt32)
    (aux1 aux4 aux5 aux7 aux8 aux10 : UInt32)
    (hpositive : 0 < sorted.length)
    (hbyteBound : 4 * sorted.length < UInt32.size)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      ExportFrame heapId capacity inputPtr input chunkBytes outputBytes ∗
      LiveWordBlock heapId valuesId valuesPtr sorted ∗
      Streams [] [] false ∗
      (∀ finalOutput : List UInt8,
        RuntimeContext -∗
        ExportFrame heapId capacity inputPtr input chunkBytes finalOutput -∗
        LiveWordBlock heapId valuesId valuesPtr sorted -∗
        Streams [] (serialize sorted) false -∗
        WP (.running
          ⟨func3OutputLocals valuesPtr sorted aux1 aux4 aux5 aux7 aux8 aux10
              sorted.length,
            afterLoop, arity, remainder, controls, calls⟩ :
              Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3OutputLocals valuesPtr sorted aux1 aux4 aux5 aux7 aux8 aux10 0,
          [.loop 0 0 func3OutputLoopBody] ++ afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  let Finish : HeapIProp := iprop(
    ∀ finalOutput : List UInt8,
      RuntimeContext -∗
      ExportFrame heapId capacity inputPtr input chunkBytes finalOutput -∗
      LiveWordBlock heapId valuesId valuesPtr sorted -∗
      Streams [] (serialize sorted) false -∗
      WP (.running
        ⟨func3OutputLocals valuesPtr sorted aux1 aux4 aux5 aux7 aux8 aux10
            sorted.length,
          afterLoop, arity, remainder, controls, calls⟩ :
            Expr Universal.State)
        @ s; E [{ Φ }])
  let Inv : Nat → HeapIProp := fun emitted => iprop(
    ⌜emitted < sorted.length⌝ ∗
    ∃ frameOutput : List UInt8,
      RuntimeContext ∗
      ExportFrame heapId capacity inputPtr input chunkBytes frameOutput ∗
      LiveWordBlock heapId valuesId valuesPtr sorted ∗
      Streams [] (serialize (sorted.take emitted)) false ∗
      Finish)
  iintro ⟨Hruntime, Hframe, Hvalues, Hstreams, Hfinish⟩
  simp only [List.cons_append, List.nil_append]
  iapply Project.Mergesort.SortProof.twp_loop_wf_family_from_terminal
    (ι := Nat)
    (measure := fun emitted => sorted.length - emitted)
    (locals := func3OutputLocals valuesPtr sorted aux1 aux4 aux5 aux7 aux8
      aux10)
    (I := Inv) (initial := 0)
    (initialLocals := func3OutputLocals valuesPtr sorted aux1 aux4 aux5 aux7
      aux8 aux10 0)
    (body := func3OutputLoopBody) (code := afterLoop)
    (belowStack := []) rfl rfl
  · intro emitted
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨%hemitted, %frameOutput, Hruntime, Hframe, Hvalues, Hstreams, Hfinish⟩
    isimp only [LiveWordBlock] at Hvalues
    icases Hvalues with ⟨Htoken, Hwords, %hnonnull⟩
    have hcountdown := func3_output_countdown_step hemitted
    have hstreamStep :
        serialize (sorted.take emitted) ++ serialize [sorted[emitted]] =
          serialize (sorted.take (emitted + 1)) := by
      rw [← serialize_append,
        ← Wasm.Examples.MergeSort.take_succ_eq_append_getElem hemitted]
    have Hwrite := twp_func3_write_one
      (hlc := hlc) heapId capacity inputPtr valuesPtr input chunkBytes
      frameOutput sorted emitted aux1
      (UInt32.ofNat (4 * (sorted.length - emitted))) aux4 aux5 aux7 aux8
      aux10 hemitted
      (code := func3OutputLoopBody.drop 9)
      (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .loop, paramArity := 0, resultArity := 0,
          body := func3OutputLoopBody, continuation := afterLoop,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp only [func3OutputLoopBody, func3OutputLocals, func3AppendLocals,
      List.drop, List.cons_append, List.nil_append] at Hwrite ⊢
    iapply Hwrite
    isplitl_exact Hruntime
    isplitl_exact Hframe
    isplitl_exact Hwords
    isplitl_exact Hstreams
    iintro Hruntime Hframe Hwords Hstreams
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4 : UInt32), func3_decode_next_address]
    wasm_twp_pures [twp_localSet]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (4294967292 : UInt32), hcountdown]
    wasm_twp_pures [twp_localTee]
    simp only [List.length, List.set]
    ihave Hvalues : LiveWordBlock heapId valuesId valuesPtr sorted $$
        [Htoken Hwords]
    · unfold LiveWordBlock
      iframe
      ipureexact hnonnull
    by_cases hmore : emitted + 1 < sorted.length
    · have hnonzero :
          UInt32.ofNat (4 * (sorted.length - (emitted + 1))) ≠ 0 := by
        intro hzero
        have hzeroNat := congrArg UInt32.toNat hzero
        rw [UInt32.toNat_ofNat_of_lt' (by omega)] at hzeroNat
        simp only [UInt32.toNat_zero] at hzeroNat
        omega
      iapply twp_brIf
        (condition := UInt32.ofNat (4 * (sorted.length - (emitted + 1))))
        (depth := 0) (arity := arity) (code := [])
        (targetCode := func3OutputLoopBody)
        (targetControl :=
          { kind := .loop, paramArity := 0, resultArity := 0,
            body := func3OutputLoopBody, continuation := afterLoop,
            belowStack := [] } :: controls)
        (targetValues := []) hnonzero (by rfl)
      ispecialize Hrec $$ %(emitted + 1)
      simp only [func3OutputLoopBody]
      iapply Hrec
      · ipureintro
        omega
      isplitr_pureexact hmore
      iexists (serialize [sorted[emitted]])
      isimp only [hstreamStep] at Hstreams
      iframe
    · have hdone : emitted + 1 = sorted.length := by omega
      have hzero :
          UInt32.ofNat (4 * (sorted.length - (emitted + 1))) = 0 := by
        simp [hdone]
      rw [hzero]
      wasm_twp_pures [twp_brIfZero twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      have hfinalCountdown :
          UInt32.ofNat (4 * (sorted.length - sorted.length)) = 0 := by
        simp
      isimp only [Finish, func3OutputLocals, func3AppendLocals] at Hfinish
      isimp only [hfinalCountdown] at Hfinish
      isimp only [hstreamStep, hdone, List.take_length] at Hstreams
      rw [hdone]
      iapply Hfinish $$ %(serialize [sorted[emitted]]) Hruntime Hframe Hvalues
        Hstreams
  · simp only [Inv, Finish, List.take_zero, serialize, WordCodec.serialize,
      List.flatMap_nil]
    isplitr_pureexact hpositive
    iexists outputBytes
    iframe

/-- Exact enclosing block for the generated output phase.  The guard is the
ordinary empty/nonempty split; only the nonempty arm initializes and enters
`func3OutputLoopBody`. -/
private def func3OutputBlockBody : Program :=
  [.localGet 9, .eqz, .br_if 0,
    .localGet 9, .const 2, .shl, .localSet 6,
    .localGet 2, .localSet 3,
    .loop 0 0 func3OutputLoopBody]

/-- Compose the output guard, countdown setup, and full output loop.  Locals 3
and 6 are dead after this phase, so the continuation quantifies over their
branch-dependent final values while retaining every authoritative resource. -/
theorem twp_func3_output
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId : Nat)
    (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8)
    (sorted : List UInt32)
    (aux1 aux3 aux6 aux4 aux5 aux7 aux8 aux10 : UInt32)
    (hbyteBound : 4 * sorted.length < UInt32.size)
    {afterOutput : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      ExportFrame heapId capacity inputPtr input chunkBytes outputBytes ∗
      LiveWordBlock heapId valuesId valuesPtr sorted ∗
      Streams [] [] false ∗
      (∀ final3 : UInt32, ∀ final6 : UInt32,
        ∀ finalOutput : List UInt8,
          RuntimeContext -∗
          ExportFrame heapId capacity inputPtr input chunkBytes finalOutput -∗
          LiveWordBlock heapId valuesId valuesPtr sorted -∗
          Streams [] (serialize sorted) false -∗
          WP (.running
            ⟨func3AppendLocals aux1 final3 final6 valuesPtr aux4 aux5 aux7
                aux8 (UInt32.ofNat sorted.length) aux10 [],
              afterOutput, arity, remainder, controls, calls⟩ :
                Expr Universal.State)
            @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals aux1 aux3 aux6 valuesPtr aux4 aux5 aux7 aux8
            (UInt32.ofNat sorted.length) aux10 [],
          [.block 0 0 func3OutputBlockBody] ++ afterOutput,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hframe, Hvalues, Hstreams, Hcont⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3OutputBlockBody, func3AppendLocals]
  wasm_twp_pures [twp_localGet]
  by_cases hempty : sorted.length = 0
  · have hzero : UInt32.ofNat sorted.length = 0 := by simp [hempty]
    iapply twp_eqz (result := 1) (by simp [hzero])
    iapply twp_brIf (condition := 1) (depth := 0) (arity := arity)
      (targetCode := afterOutput) (targetControl := controls)
      (targetValues := []) (by decide) (by rfl)
    have hserialize : serialize sorted = [] := by
      rw [List.length_eq_zero_iff.mp hempty]
      rfl
    ihave Hstreams' : Streams [] (serialize sorted) false $$ [Hstreams]
    · isimp only [hserialize]
      iexact Hstreams
    iapply Hcont $$ %aux3 %aux6 %outputBytes Hruntime Hframe Hvalues Hstreams'
  · have hpositive : 0 < sorted.length := Nat.pos_of_ne_zero hempty
    have hnonzero : UInt32.ofNat sorted.length ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt32.toNat hzero
      rw [UInt32.toNat_ofNat_of_lt' (by omega)] at hzeroNat
      simp only [UInt32.toNat_zero] at hzeroNat
      omega
    iapply twp_eqz (result := 0) (by simp [hnonzero])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_shl]
    rw [MemRegion.shl2_eq_mul4, ← func3_decode_byte_offset]
    wasm_twp_pures [twp_localSet]
    simp only [List.length, List.set]
    wasm_twp_pures [twp_localGet twp_localSet]
    simp only [List.length, List.set]
    have Hloop := twp_func3_output_loop
      (hlc := hlc) heapId valuesId capacity inputPtr valuesPtr input
      chunkBytes outputBytes sorted aux1 aux4 aux5 aux7 aux8 aux10 hpositive
      hbyteBound
      (afterLoop := []) (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .block, paramArity := 0, resultArity := 0,
          body := func3OutputBlockBody, continuation := afterOutput,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    simp [func3OutputLocals, func3AppendLocals, func3OutputBlockBody]
      at Hloop ⊢
    iapply Hloop
    isplitl_exact Hruntime
    isplitl_exact Hframe
    isplitl_exact Hvalues
    isplitl_exact Hstreams
    iintro %finalOutput Hruntime Hframe Hvalues Hstreams
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append]
    iapply Hcont $$ %(valuesPtr + 4 * UInt32.ofNat sorted.length)
      %(0 : UInt32) %finalOutput Hruntime Hframe Hvalues Hstreams

/-- Exact generated block which retires the sorted values allocation. -/
private def func3ValuesDeallocBlockBody : Program :=
  [.localGet 1, .eqz, .br_if 0,
    .localGet 2, .localGet 1, .const 2, .shl, .const 4, .call 10]

/-- Retire the complete sorted values block through the proved no-op physical
deallocator.  The nonzero guard is discharged from the allocation-path
invariant, and the logical allocation token and bytes move into `BumpHeap`. -/
theorem twp_func3_deallocate_values
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId : Nat) (valuesPtr : UInt32)
    (sorted : List UInt32)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (aux3 aux6 aux4 aux5 aux7 aux8 aux10 : UInt32)
    (hpositive : 0 < sorted.length)
    (hbyteBound : 4 * sorted.length < UInt32.size)
    {afterValues : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := 4 * sorted.length, alignment := 4 }
    iprop(
      RuntimeContext ∗
      BumpHeap heapId storedCursor frontier history ∗
      LiveWordBlock heapId valuesId valuesPtr sorted ∗
      (RuntimeContext -∗
        BumpHeap heapId storedCursor frontier
          (history.retire valuesId valuesPtr layout) -∗
        WP (.running
          ⟨func3AppendLocals (UInt32.ofNat sorted.length) aux3 aux6 valuesPtr
              aux4 aux5 aux7 aux8 (UInt32.ofNat sorted.length) aux10 [],
            afterValues, arity, remainder, controls, calls⟩ :
              Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals (UInt32.ofNat sorted.length) aux3 aux6 valuesPtr
            aux4 aux5 aux7 aux8 (UInt32.ofNat sorted.length) aux10 [],
          [.block 0 0 func3ValuesDeallocBlockBody] ++ afterValues,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := 4 * sorted.length, alignment := 4 }
  have hcountBound : sorted.length < UInt32.size := by omega
  have hcountNonzero : UInt32.ofNat sorted.length ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    rw [UInt32.toNat_ofNat_of_lt' hcountBound] at hzeroNat
    simp only [UInt32.toNat_zero] at hzeroNat
    omega
  have hsizeWord :
      (UInt32.ofNat (4 * sorted.length)).toNat = 4 * sorted.length :=
    UInt32.toNat_ofNat_of_lt' hbyteBound
  have hfour : (4 : UInt32).toNat = 4 := by decide
  iintro ⟨Hruntime, Hbump, Hvalues, Hcont⟩
  ihave Hblock := (LiveWordBlock_as_liveBlock heapId valuesId valuesPtr
    sorted).mp $$ Hvalues
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3ValuesDeallocBlockBody, func3AppendLocals, List.drop_zero]
  wasm_twp_pures [twp_localGet]
  iapply twp_eqz (result := 0) (by simp [hcountNonzero])
  wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const twp_shl]
  rw [MemRegion.shl2_eq_mul4, ← func3_decode_byte_offset]
  wasm_twp_pures [twp_const]
  have Hdealloc := Project.Mergesort.ContractProofs.func7_correct
    (hlc := hlc)
    (ptr := valuesPtr) (size := UInt32.ofNat (4 * sorted.length))
    (alignment := 4) (layout := layout) (heapId := heapId)
    (allocationId := valuesId) (bytes := serialize sorted)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history)
    (callerLocals := func3AppendLocals (UInt32.ofNat sorted.length) aux3
      aux6 valuesPtr aux4 aux5 aux7 aux8 (UInt32.ofNat sorted.length)
      aux10 [])
    (stack := []) (code := []) (arity := arity) (remainder := remainder)
    (controls :=
      { kind := .block, paramArity := 0, resultArity := 0,
        body := func3ValuesDeallocBlockBody, continuation := afterValues,
        belowStack := [] } :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func7Spec CallContract callExpr at Hdealloc
  simp only [List.cons_append, List.nil_append,
    func3AppendLocals, func3ValuesDeallocBlockBody]
    at Hdealloc
  iapply Hdealloc
  isplitl_exact Hruntime
  isplitl_exact Hbump
  isplitl_exact Hblock
  isplitl_pureexact ⟨hsizeWord, hfour, Or.inr rfl⟩
  iintro Hruntime Hbump
  unfold ResumeWP resumeExpr
  wasm_twp_pures [twp_exitControl]
  simp only [List.take_zero, List.nil_append]
  iapply Hcont $$ Hruntime Hbump

/-- Exact generated block which retires the scratch allocation. -/
private def func3ScratchDeallocBlockBody : Program :=
  [.localGet 5, .br_if 0,
    .localGet 8, .localGet 10, .const 4, .call 10]

/-- Retire the complete scratch block.  The successful allocation path fixes
local 5 to zero, so the generated skip edge is unreachable; local 10 carries
the exact four-byte word-array layout consumed by `func7`. -/
theorem twp_func3_deallocate_scratch
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (scratchId : Nat) (scratchPtr valuesPtr : UInt32)
    (sorted scratchValues : List UInt32)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (aux3 aux6 aux4 aux7 : UInt32)
    (hscratchLength : scratchValues.length = sorted.length)
    (hbyteBound : 4 * sorted.length < UInt32.size)
    {afterScratch : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := 4 * sorted.length, alignment := 4 }
    iprop(
      RuntimeContext ∗
      BumpHeap heapId storedCursor frontier history ∗
      LiveWordBlock heapId scratchId scratchPtr scratchValues ∗
      (RuntimeContext -∗
        BumpHeap heapId storedCursor frontier
          (history.retire scratchId scratchPtr layout) -∗
        WP (.running
          ⟨func3AppendLocals (UInt32.ofNat sorted.length) aux3 aux6 valuesPtr
              aux4 0 aux7 scratchPtr (UInt32.ofNat sorted.length)
              (UInt32.ofNat (4 * sorted.length)) [],
            afterScratch, arity, remainder, controls, calls⟩ :
              Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3AppendLocals (UInt32.ofNat sorted.length) aux3 aux6 valuesPtr
            aux4 0 aux7 scratchPtr (UInt32.ofNat sorted.length)
            (UInt32.ofNat (4 * sorted.length)) [],
          [.block 0 0 func3ScratchDeallocBlockBody] ++ afterScratch,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := 4 * sorted.length, alignment := 4 }
  have hsizeWord :
      (UInt32.ofNat (4 * sorted.length)).toNat = 4 * sorted.length :=
    UInt32.toNat_ofNat_of_lt' hbyteBound
  have hfour : (4 : UInt32).toNat = 4 := by decide
  iintro ⟨Hruntime, Hbump, Hscratch, Hcont⟩
  ihave Hblock := (LiveWordBlock_as_liveBlock heapId scratchId scratchPtr
    scratchValues).mp $$ Hscratch
  isimp only [hscratchLength] at Hblock
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3ScratchDeallocBlockBody, func3AppendLocals, List.drop_zero]
  wasm_twp_pures [twp_localGet twp_brIfZero twp_localGet twp_localGet twp_const]
  have Hdealloc := Project.Mergesort.ContractProofs.func7_correct
    (hlc := hlc)
    (ptr := scratchPtr) (size := UInt32.ofNat (4 * sorted.length))
    (alignment := 4) (layout := layout) (heapId := heapId)
    (allocationId := scratchId) (bytes := serialize scratchValues)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history)
    (callerLocals := func3AppendLocals (UInt32.ofNat sorted.length) aux3
      aux6 valuesPtr aux4 0 aux7 scratchPtr (UInt32.ofNat sorted.length)
      (UInt32.ofNat (4 * sorted.length)) [])
    (stack := []) (code := []) (arity := arity) (remainder := remainder)
    (controls :=
      { kind := .block, paramArity := 0, resultArity := 0,
        body := func3ScratchDeallocBlockBody, continuation := afterScratch,
        belowStack := [] } :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func7Spec CallContract callExpr at Hdealloc
  simp only [List.cons_append, List.nil_append, func3AppendLocals,
    func3ScratchDeallocBlockBody] at Hdealloc
  iapply Hdealloc
  isplitl_exact Hruntime
  isplitl_exact Hbump
  isplitl_exact Hblock
  isplitl_pureexact ⟨hsizeWord, hfour, Or.inr rfl⟩
  iintro Hruntime Hbump
  unfold ResumeWP resumeExpr
  wasm_twp_pures [twp_exitControl]
  simp only [List.take_zero, List.nil_append]
  iapply Hcont $$ Hruntime Hbump

/-- Exact generated tail which either skips empty Vec storage or retires its
complete allocation.  This is still inside the driver's outermost block. -/
private def func3InputDeallocTail : Program :=
  [.localGet 0, .load32 0, .localTee 3, .eqz, .br_if 0,
    .localGet 4, .localGet 3, .const 1, .call 10]

/-- Retire a completed nonempty input Vec and expose the raw stack-frame bytes.
The allocation identity is obtained from `VecStorage`, while its membership in
the current allocator history is obtained from authoritative ghost agreement.
Keeping that lookup explicit is what later makes `AllRetired` provable without
assuming which allocation ID the Vec happened to receive. -/
theorem twp_func3_deallocate_input
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (capacity inputPtr : UInt32)
    (initialized chunkBytes outputBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (aux1 aux3 aux6 aux2 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (hcapacity : 0 < capacity.toNat)
    (driverBody afterDriver : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := capacity.toNat, alignment := 1 }
    let finalLocals :=
      func3AppendLocals aux1 capacity aux6 aux2 inputPtr aux5 aux7 aux8 aux9
        aux10 []
    iprop(
      RuntimeContext ∗
      ExportFrame heapId capacity inputPtr initialized chunkBytes outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      (∀ allocationId : Nat, ∀ allBytes : List UInt8,
        ∀ spare : List UInt8,
        ⌜0 < capacity.toNat ∧
          initialized.length ≤ capacity.toNat ∧
          allBytes = initialized ++ spare ∧
          spare.length = capacity.toNat - initialized.length ∧
          (exportFrameBytes capacity inputPtr initialized chunkBytes
            outputBytes).length = 272 ∧
          get? history.records allocationId =
            some (liveMeta inputPtr layout)⌝ -∗
        RuntimeContext -∗
        BumpHeap heapId storedCursor frontier
          (history.retire allocationId inputPtr layout) -∗
        ByteSlice driverBase
          (exportFrameBytes capacity inputPtr initialized chunkBytes
            outputBytes) -∗
        WP (.running
          ⟨finalLocals, afterDriver, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3AppendLocals aux1 aux3 aux6 aux2 inputPtr aux5 aux7 aux8
            aux9 aux10 [],
          func3InputDeallocTail, arity, remainder,
          { kind := .block, paramArity := 0, resultArity := 0,
            body := driverBody, continuation := afterDriver,
            belowStack := [] } :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := capacity.toNat, alignment := 1 }
  let finalLocals :=
    func3AppendLocals aux1 capacity aux6 aux2 inputPtr aux5 aux7 aux8 aux9
      aux10 []
  have hcapacityNonzero : capacity ≠ 0 := by
    intro hzero
    have := congrArg UInt32.toNat hzero
    simp only [UInt32.toNat_zero] at this
    omega
  have hone : (1 : UInt32).toNat = 1 := by decide
  iintro ⟨Hruntime, Hframe, Hbump, Hcont⟩
  isimp only [ExportFrame, VecU8, RawVecHeader] at Hframe
  icases Hframe with
    ⟨⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩,
      Hchunk, Houtput, %hframeLengths⟩
  simp only [func3InputDeallocTail, func3AppendLocals]
  wasm_twp_pures [twp_localGet]
  ihave Hcapacity' : pointsTo_u32 0 (driverBase + 0) capacity $$ [Hcapacity]
  · simp only [UInt32.add_zero]
    iexact Hcapacity
  wasm_twp_bind twp_load32 (address := driverBase) (offset := 0) capacity
      (by decide) (by decide) (by decide) (by decide) with Hcapacity' => Hcapacity
  isimp only [UInt32.add_zero] at Hcapacity
  wasm_twp_pures [twp_localTee]
  simp only [List.length, List.set]
  iapply twp_eqz (result := 0) (by simp [hcapacityNonzero])
  wasm_twp_pures [twp_brIfZero]
  ihave Hframe : ExportFrame heapId capacity inputPtr initialized chunkBytes
      outputBytes $$ [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
  · unfold ExportFrame VecU8 RawVecHeader
    iframe
    ipureexact hframeLengths
  ihave Hreleased := ExportFrame_releaseStorage heapId capacity inputPtr
    initialized chunkBytes outputBytes $$ Hframe
  icases Hreleased with ⟨Hstorage, HframeBytes, %_hframeLength⟩
  isimp only [VecStorage] at Hstorage
  icases Hstorage with (%hempty | Hlive)
  ·
    have hzero := congrArg UInt32.toNat hempty.1
    simp only [UInt32.toNat_zero] at hzero
    omega
  · icases Hlive with
      ⟨%allocationId, %allBytes, %spare, %hstorage, Hblock⟩
    isimp only [BumpHeap] at Hbump
    icases Hbump with
      ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
    isimp only [LiveBlock] at Hblock
    icases Hblock with ⟨Htoken, Hbytes, %hblock⟩
    ihave %hlookup : ⌜get? history.records allocationId =
        some (liveMeta inputPtr layout)⌝ $$ [Hauth Htoken]
    · iapply_frame AllocMetaAuth_token_agree
    ihave Hbump : BumpHeap heapId storedCursor frontier history $$
        [Hcursor Hfrontier Hauth Hretired Hpages]
    · unfold BumpHeap
      iframe
      ipureexact hheap
    ihave Hblock : LiveBlock heapId allocationId inputPtr layout allBytes $$
        [Htoken Hbytes]
    · unfold LiveBlock
      iframe
      ipureexact hblock
    wasm_twp_pures [twp_localGet twp_localGet twp_const]
    have Hdealloc := Project.Mergesort.ContractProofs.func7_correct
      (hlc := hlc) (ptr := inputPtr) (size := capacity) (alignment := 1)
      (layout := layout) (heapId := heapId) (allocationId := allocationId)
      (bytes := allBytes) (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (callerLocals := finalLocals) (stack := [])
      (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .block, paramArity := 0, resultArity := 0,
          body := driverBody, continuation := afterDriver,
          belowStack := [] } :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Phi)
    unfold Func7Spec CallContract callExpr at Hdealloc
    simp only [List.cons_append, List.nil_append, finalLocals,
      func3AppendLocals] at Hdealloc
    iapply Hdealloc
    isplitl_exact Hruntime
    isplitl_exact Hbump
    isplitl_exact Hblock
    isplitl_pureexact ⟨rfl, hone, Or.inl rfl⟩
    iintro Hruntime Hbump
    unfold ResumeWP resumeExpr
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append]
    ispecialize Hcont $$ %allocationId %allBytes %spare
    ispecialize Hcont $$
      %⟨hstorage.1, hstorage.2.1, hstorage.2.2.1,
        hstorage.2.2.2, _hframeLength, hlookup⟩
    iapply Hcont $$ Hruntime Hbump HframeBytes

/-- The empty Vec owns no allocation.  Its zero-capacity guard exits the
driver's outer block before the syntactically following deallocator call. -/
theorem twp_func3_skip_empty_input
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (chunkBytes outputBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (aux1 aux3 aux6 aux2 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (driverBody afterDriver : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    let finalLocals :=
      func3AppendLocals aux1 0 aux6 aux2 1 aux5 aux7 aux8 aux9 aux10 []
    iprop(
      RuntimeContext ∗
      ExportFrame heapId 0 1 [] chunkBytes outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      (RuntimeContext -∗
        BumpHeap heapId storedCursor frontier history -∗
        ByteSlice driverBase
          (exportFrameBytes 0 1 [] chunkBytes outputBytes) -∗
        ⌜(exportFrameBytes 0 1 [] chunkBytes outputBytes).length = 272⌝ -∗
        WP (.running
          ⟨finalLocals, afterDriver, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3AppendLocals aux1 aux3 aux6 aux2 1 aux5 aux7 aux8 aux9
            aux10 [],
          func3InputDeallocTail, arity, remainder,
          { kind := .block, paramArity := 0, resultArity := 0,
            body := driverBody, continuation := afterDriver,
            belowStack := [] } :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  dsimp only
  let finalLocals :=
    func3AppendLocals aux1 0 aux6 aux2 1 aux5 aux7 aux8 aux9 aux10 []
  iintro ⟨Hruntime, Hframe, Hbump, Hcont⟩
  isimp only [ExportFrame, VecU8, RawVecHeader] at Hframe
  icases Hframe with
    ⟨⟨⟨Hcapacity, Hpointer⟩, Hlength, Hstorage⟩,
      Hchunk, Houtput, %hframeLengths⟩
  simp only [func3InputDeallocTail, func3AppendLocals]
  wasm_twp_pures [twp_localGet]
  ihave Hcapacity' : pointsTo_u32 0 (driverBase + 0) 0 $$ [Hcapacity]
  · simp only [UInt32.add_zero]
    iexact Hcapacity
  wasm_twp_bind twp_load32 (address := driverBase) (offset := 0) 0
      (by decide) (by decide) (by decide) (by decide) with Hcapacity' => Hcapacity
  isimp only [UInt32.add_zero] at Hcapacity
  wasm_twp_pures [twp_localTee]
  simp only [List.length, List.set]
  iapply twp_eqz (result := 1) (by simp)
  ihave Hframe : ExportFrame heapId 0 1 [] chunkBytes outputBytes $$
      [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
  · unfold ExportFrame VecU8 RawVecHeader
    iframe
    ipureexact hframeLengths
  ihave Hreleased := ExportFrame_releaseStorage heapId 0 1 [] chunkBytes
    outputBytes $$ Hframe
  icases Hreleased with ⟨Hstorage, HframeBytes, %hframeLength⟩
  isimp only [VecStorage] at Hstorage
  icases Hstorage with (%_hempty | Hlive)
  · iapply twp_brIf (condition := 1) (depth := 0) (arity := arity)
      (targetCode := afterDriver) (targetControl := controls)
      (targetValues := []) (by decide) (by rfl)
    iapply Hcont $$ Hruntime Hbump HframeBytes %hframeLength
  · icases Hlive with
      ⟨%_allocationId, %_allBytes, %_spare, %hlive, _Hblock⟩
    norm_num at hlive

/-- Exact generated epilogue restoring the exported shadow-stack pointer. -/
private def func3RestoreStackTail : Program :=
  [.localGet 0, .const 272, .add, .globalSet 0]

/-- Restore the public 288-byte entry stack from the untouched 16-byte reserve
and the raw 272-byte driver frame.  This theorem deliberately stops before
the administrative return-from-call step, so the body proof and the public
call contract remain separate composition layers. -/
theorem twp_func3_restore_stack
    [WasmSmallStepGS hlc Universal.State]
    (reserveBytes frameBytes : List UInt8)
    (aux1 aux3 aux6 aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (hframeLength : frameBytes.length = 272)
    (afterRestore : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ByteSlice driverBase frameBytes ∗
      (StackPointer entryStackTop -∗
        StackRegion entryStackLow (reserveBytes ++ frameBytes) -∗
        ⌜(reserveBytes ++ frameBytes).length = 288⌝ -∗
        WP (.running
          ⟨func3AppendLocals aux1 aux3 aux6 aux2 aux4 aux5 aux7 aux8 aux9
              aux10 [],
            afterRestore, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3AppendLocals aux1 aux3 aux6 aux2 aux4 aux5 aux7 aux8 aux9
            aux10 [],
          func3RestoreStackTail ++ afterRestore,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Phi }] := by
  iintro ⟨Hsp, Hreserve, Hframe, Hcont⟩
  ihave Hfinish : iprop(
      StackPointer entryStackTop -∗
        WP (.running
          ⟨func3AppendLocals aux1 aux3 aux6 aux2 aux4 aux5 aux7 aux8 aux9
              aux10 [],
            afterRestore, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Phi }]) $$
      [Hreserve Hframe Hcont]
  · iintro Hsp'
    ihave Hcombined : iprop(
        StackRegion entryStackLow (reserveBytes ++ frameBytes) ∗
          ⌜(reserveBytes ++ frameBytes).length = 288⌝) $$
        [Hreserve Hframe]
    · iapply_frame StackReserve_combineFrame reserveBytes frameBytes hframeLength
    icases Hcombined with ⟨Hstack, %hstackLength⟩
    iapply Hcont $$ Hsp' Hstack %hstackLength
  isimp only [StackPointer] at Hsp
  simp only [func3RestoreStackTail, func3AppendLocals,
    List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show 272 + driverBase = entryStackTop by decide]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp' : StackPointer entryStackTop $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hfinish $$ Hsp'

/-- A completed nonempty input lineage has no live metadata except the Vec
storage identified by its authoritative allocation token. -/
private theorem completedHistory_other_records_retired
    (total : Nat) (capacity inputPtr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (inputId : Nat)
    (hpositive : 0 < total)
    (hgeo : GeometricVecFacts total total 0 capacity inputPtr frontier history)
    (hinput : get? history.records inputId =
      some (liveMeta inputPtr
        { size := capacity.toNat, alignment := 1 })) :
    ∀ allocationId metadata,
      get? history.records allocationId = some metadata →
      allocationId ≠ inputId → metadata.status = .retired := by
  rcases hgeo with hempty | hshort | hlarge
  · omega
  · rcases hshort with
      ⟨_remaining, _length, _totalBound, _capacity, _ptr, _frontier,
        hhistory⟩
    subst history
    have hinputId : inputId = 0 := by
      by_contra hne
      unfold shortHistory at hinput
      rw [get?_insert_ne (Ne.symm hne)] at hinput
      simp [LawfulPartialMap.get?_empty] at hinput
    intro allocationId metadata hlookup hne
    subst inputId
    unfold shortHistory at hlookup
    by_cases hid : 0 = allocationId
    · exact False.elim (hne hid.symm)
    · rw [get?_insert_ne hid] at hlookup
      simp [LawfulPartialMap.get?_empty] at hlookup
  · rcases hlarge with
      ⟨exponent, hexponentLower, _hexponentUpper, hcapacity, _hlength,
        _htotal, hptr, _hfrontier, hhistory⟩
    have hptrExact :
        inputPtr = UInt32.ofNat (vectorBlockBase exponent) := by
      rw [← UInt32.ofNat_toNat (x := inputPtr), hptr]
    have hinputId : inputId = exponent - 8 := by
      apply geometricHistory_live_unique exponent inputId hexponentLower
      simpa only [hhistory, hptrExact, hcapacity] using hinput
    intro allocationId metadata hlookup hne
    subst history
    unfold geometricHistory at hlookup
    rw [geometricRecords_lookup] at hlookup
    split at hlookup
    · rename_i hidBound
      injection hlookup with hmetadata
      subst metadata
      have hnotTop : allocationId + 8 ≠ exponent := by
        intro hlive
        apply hne
        rw [hinputId]
        omega
      simp [geometricMetadata, hnotTop]
    · contradiction

/-- Allocation history immediately before the completed input Vec is
retired: both same-sized driver word arrays have already been retired. -/
private def completedDriverBeforeInputHistory
    (history : AllocationHistory) (valuesPtr scratchPtr : UInt32)
    (workLayout : AllocLayout) : AllocationHistory :=
  (((history.allocate valuesPtr workLayout).allocate scratchPtr workLayout).retire
      history.nextId valuesPtr workLayout).retire
    (history.nextId + 1) scratchPtr workLayout

/-- Retiring the two driver-owned word arrays and then the unique completed
input Vec leaves an allocation history with no live entries. -/
private theorem completedDriverHistory_allRetired
    (total : Nat) (capacity inputPtr valuesPtr scratchPtr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (inputId : Nat) (workLayout : AllocLayout)
    (hpositive : 0 < total)
    (hgeo : GeometricVecFacts total total 0 capacity inputPtr frontier history)
    (hinput :
      get? (completedDriverBeforeInputHistory history valuesPtr scratchPtr
          workLayout).records inputId =
        some (liveMeta inputPtr
          { size := capacity.toNat, alignment := 1 })) :
    AllRetired
      ((completedDriverBeforeInputHistory history valuesPtr scratchPtr
        workLayout).retire
          inputId inputPtr { size := capacity.toNat, alignment := 1 }) := by
  let inputLayout : AllocLayout :=
    { size := capacity.toNat, alignment := 1 }
  have hinputNeValues : inputId ≠ history.nextId := by
    intro heq
    subst inputId
    simp only [completedDriverBeforeInputHistory, AllocationHistory.allocate,
      AllocationHistory.retire] at hinput
    rw [get?_insert_ne (by omega)] at hinput
    rw [get?_insert_eq rfl] at hinput
    have hstatus := congrArg AllocationMeta.status (Option.some.inj hinput)
    simp [liveMeta, retiredMeta] at hstatus
  have hinputNeScratch : inputId ≠ history.nextId + 1 := by
    intro heq
    subst inputId
    simp only [completedDriverBeforeInputHistory, AllocationHistory.allocate,
      AllocationHistory.retire] at hinput
    rw [get?_insert_eq rfl] at hinput
    have hstatus := congrArg AllocationMeta.status (Option.some.inj hinput)
    simp [liveMeta, retiredMeta] at hstatus
  have hinputBase : get? history.records inputId =
      some (liveMeta inputPtr inputLayout) := by
    simp only [completedDriverBeforeInputHistory, AllocationHistory.allocate,
      AllocationHistory.retire] at hinput
    rw [get?_insert_ne (Ne.symm hinputNeScratch)] at hinput
    rw [get?_insert_ne (Ne.symm hinputNeValues)] at hinput
    rw [get?_insert_ne (Ne.symm hinputNeScratch)] at hinput
    rw [get?_insert_ne (Ne.symm hinputNeValues)] at hinput
    simpa only [inputLayout] using hinput
  have hothers := completedHistory_other_records_retired total capacity
    inputPtr frontier history inputId hpositive hgeo hinputBase
  unfold AllRetired
  intro allocationId metadata hlookup
  simp only [completedDriverBeforeInputHistory, AllocationHistory.allocate,
    AllocationHistory.retire] at hlookup
  by_cases hinputId : inputId = allocationId
  · rw [get?_insert_eq hinputId] at hlookup
    injection hlookup with hmetadata
    subst metadata
    rfl
  · rw [get?_insert_ne hinputId] at hlookup
    by_cases hscratchId : history.nextId + 1 = allocationId
    · rw [get?_insert_eq hscratchId] at hlookup
      injection hlookup with hmetadata
      subst metadata
      rfl
    · rw [get?_insert_ne hscratchId] at hlookup
      by_cases hvaluesId : history.nextId = allocationId
      · rw [get?_insert_eq hvaluesId] at hlookup
        injection hlookup with hmetadata
        subst metadata
        rfl
      · rw [get?_insert_ne hvaluesId] at hlookup
        rw [get?_insert_ne hscratchId] at hlookup
        rw [get?_insert_ne hvaluesId] at hlookup
        exact hothers allocationId metadata hlookup (Ne.symm hinputId)

/-- Exact cleanup sequence following the generated output block. -/
private def func3NonemptyCleanup : Program :=
  [.block 0 0 func3ValuesDeallocBlockBody,
    .block 0 0 func3ScratchDeallocBlockBody] ++ func3InputDeallocTail

private def func3CleanupOuterFrame (driverBody : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := driverBody, continuation := func3RestoreStackTail,
    belowStack := [] }

/-- Compose all three logical retirements with shadow-stack restoration on a
normal nonempty execution.  The result is exactly `DriverSuccess`; allocator
identities and the final `AllRetired` fact are derived from the concrete
history transitions performed by the three proved deallocation calls. -/
theorem twp_func3_finish_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original sorted scratchValues : List UInt32)
    (capacity inputPtr valuesPtr scratchPtr : UInt32)
    (valuesId scratchId : Nat)
    (chunkBytes outputBytes reserveBytes : List UInt8)
    (storedCursor : UInt32) (frontier inputFrontier : Nat)
    (inputHistory : AllocationHistory)
    (outputCursor final6 : UInt32)
    (hsorted : SortedPermutation original sorted)
    (hpositive : 0 < original.length)
    (hscratchLength : scratchValues.length = sorted.length)
    (hgeo : GeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity inputPtr inputFrontier
        inputHistory)
    (hvaluesId : valuesId = inputHistory.nextId)
    (hscratchId : scratchId = inputHistory.nextId + 1)
    (hbyteBound : 4 * original.length < UInt32.size)
    (driverBody : Program)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    let workLayout : AllocLayout :=
      { size := 4 * original.length, alignment := 4 }
    let scratchHistory :=
      (inputHistory.allocate valuesPtr workLayout).allocate scratchPtr workLayout
    let locals :=
      func3AppendLocals (UInt32.ofNat sorted.length) outputCursor final6
        valuesPtr inputPtr 0 (UInt32.ofNat (4 * sorted.length)) scratchPtr
        (UInt32.ofNat sorted.length) (UInt32.ofNat (4 * sorted.length)) []
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId capacity inputPtr (serialize original) chunkBytes
        outputBytes ∗
      LiveWordBlock heapId valuesId valuesPtr sorted ∗
      LiveWordBlock heapId scratchId scratchPtr scratchValues ∗
      BumpHeap heapId storedCursor frontier scratchHistory ∗
      Streams [] (serialize sorted) false ∗
      (RuntimeContext -∗
        DriverSuccess heapId original -∗
        WP (.running
          ⟨func3AppendLocals (UInt32.ofNat sorted.length) capacity final6
              valuesPtr inputPtr 0 (UInt32.ofNat (4 * sorted.length))
              scratchPtr (UInt32.ofNat sorted.length)
              (UInt32.ofNat (4 * sorted.length)) [],
            [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨locals, func3NonemptyCleanup, 0, [],
          [func3CleanupOuterFrame driverBody],
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  dsimp only
  let workLayout : AllocLayout :=
    { size := 4 * original.length, alignment := 4 }
  let valuesHistory := inputHistory.allocate valuesPtr workLayout
  let scratchHistory := valuesHistory.allocate scratchPtr workLayout
  let afterValues := scratchHistory.retire valuesId valuesPtr workLayout
  let beforeInput := afterValues.retire scratchId scratchPtr workLayout
  let locals :=
    func3AppendLocals (UInt32.ofNat sorted.length) outputCursor final6 valuesPtr
      inputPtr 0 (UInt32.ofNat (4 * sorted.length)) scratchPtr
      (UInt32.ofNat sorted.length) (UInt32.ofNat (4 * sorted.length)) []
  have hsortedLength : sorted.length = original.length :=
    hsorted.2.length_eq.symm
  have hsortedPositive : 0 < sorted.length := by
    rw [hsortedLength]
    exact hpositive
  have hcapacityPositive : 0 < capacity.toNat := by
    rcases hgeo with hempty | hshort | hlarge
    · have hzero := hempty.2.2.1
      rw [serialize_length] at hzero
      omega
    · rcases hshort with ⟨_, _, _, hcapacity, _, _, _⟩
      rw [hcapacity]
      omega
    · rcases hlarge with ⟨exponent, _, _, hcapacity, _, _, _, _, _⟩
      rw [hcapacity]
      exact Nat.pow_pos (by omega)
  have hsortedByteBound : 4 * sorted.length < UInt32.size := by
    simpa only [hsortedLength] using hbyteBound
  have hscratchId' : scratchId = valuesHistory.nextId := by
    simp [valuesHistory, AllocationHistory.allocate, hscratchId]
  have hscratchHistory : scratchHistory =
      (inputHistory.allocate valuesPtr workLayout).allocate scratchPtr
        workLayout := rfl
  have hbeforeInput : beforeInput =
      completedDriverBeforeInputHistory inputHistory valuesPtr scratchPtr
        workLayout := by
    simp [beforeInput, afterValues, scratchHistory, valuesHistory,
      completedDriverBeforeInputHistory, hvaluesId, hscratchId]
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hvalues, Hscratch, Hbump,
    Hstreams, Hcont⟩
  have HvaluesCleanup := twp_func3_deallocate_values
    (hlc := hlc) heapId valuesId valuesPtr sorted storedCursor frontier
    scratchHistory outputCursor final6 inputPtr 0
    (UInt32.ofNat (4 * sorted.length)) scratchPtr
    (UInt32.ofNat (4 * sorted.length)) hsortedPositive hsortedByteBound
    (afterValues :=
      [.block 0 0 func3ScratchDeallocBlockBody] ++ func3InputDeallocTail)
    (arity := 0) (remainder := [])
    (controls := [func3CleanupOuterFrame driverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3NonemptyCleanup, func3AppendLocals,
    List.cons_append, List.nil_append] at HvaluesCleanup ⊢
  iapply HvaluesCleanup
  isplitl_exact Hruntime
  isplitl_exact Hbump
  isplitl_exact Hvalues
  iintro Hruntime Hbump
  have HscratchCleanup := twp_func3_deallocate_scratch
    (hlc := hlc) heapId scratchId scratchPtr valuesPtr sorted scratchValues
    storedCursor frontier afterValues outputCursor final6 inputPtr
    (UInt32.ofNat (4 * sorted.length)) hscratchLength hsortedByteBound
    (afterScratch := func3InputDeallocTail) (arity := 0) (remainder := [])
    (controls := [func3CleanupOuterFrame driverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3AppendLocals, List.cons_append, List.nil_append]
    at HscratchCleanup ⊢
  iapply HscratchCleanup
  isplitl_exact Hruntime
  isplitl [Hbump]
  · isimp only [afterValues, workLayout, hsortedLength] at Hbump
    iexact Hbump
  isplitl_exact Hscratch
  iintro Hruntime Hbump
  have HinputCleanup := twp_func3_deallocate_input
    (hlc := hlc) heapId capacity inputPtr (serialize original) chunkBytes
    outputBytes storedCursor frontier beforeInput
    (UInt32.ofNat sorted.length) outputCursor final6 valuesPtr 0
    (UInt32.ofNat (4 * sorted.length)) scratchPtr
    (UInt32.ofNat sorted.length) (UInt32.ofNat (4 * sorted.length))
    hcapacityPositive driverBody func3RestoreStackTail
    (arity := 0) (remainder := []) (controls := []) (calls := calls)
    (s := s) (E := E) (Phi := Phi)
  simp only [func3AppendLocals, func3CleanupOuterFrame] at HinputCleanup ⊢
  iapply HinputCleanup
  isplitl_exact Hruntime
  isplitl_exact Hframe
  isplitl [Hbump]
  · isimp only [beforeInput, afterValues, workLayout, hsortedLength]
      at Hbump
    iexact Hbump
  iintro %inputId %allBytes %spare %hinput Hruntime Hbump HframeBytes
  have hallRetired : AllRetired
      (beforeInput.retire inputId inputPtr
        { size := capacity.toNat, alignment := 1 }) := by
    rw [hbeforeInput]
    apply completedDriverHistory_allRetired
      (serialize original).length capacity inputPtr valuesPtr scratchPtr
      inputFrontier inputHistory inputId workLayout
    · rw [serialize_length]
      omega
    · exact hgeo
    · rw [← hbeforeInput]
      exact hinput.2.2.2.2.2
  have Hrestore := twp_func3_restore_stack reserveBytes
    (exportFrameBytes capacity inputPtr (serialize original) chunkBytes
      outputBytes)
    (UInt32.ofNat sorted.length) capacity final6 valuesPtr inputPtr 0
    (UInt32.ofNat (4 * sorted.length)) scratchPtr
    (UInt32.ofNat sorted.length) (UInt32.ofNat (4 * sorted.length))
    hinput.2.2.2.2.1
    [] (arity := 0) (remainder := []) (controls := []) (calls := calls)
    (s := s) (E := E) (Phi := Phi)
  simp only [List.append_nil, func3AppendLocals] at Hrestore ⊢
  iapply Hrestore
  isplitl_exact Hsp
  isplitl_exact Hreserve
  isplitl_exact HframeBytes
  iintro Hsp Hstack %hstackLength
  ihave Hsuccess : DriverSuccess heapId original $$
      [Hsp Hstack Hbump Hstreams]
  · unfold DriverSuccess
    iexists sorted, reserveBytes ++
      exportFrameBytes capacity inputPtr (serialize original) chunkBytes
        outputBytes,
      storedCursor, frontier,
      beforeInput.retire inputId inputPtr
        { size := capacity.toNat, alignment := 1 }
    isplitl_pureexact ⟨hsorted, hstackLength, hallRetired⟩
    · iframe
  iapply Hcont $$ Hruntime Hsuccess

private def func3EmptyAfterReadSetup : Program :=
  [.const 0, .localSet 10, .const 0, .localSet 9,
    .const 4, .localSet 8]

private def func3SortAndCleanup : Program :=
  [.localGet 2, .localGet 9, .localGet 8, .localGet 9, .call 5,
    .block 0 0 func3OutputBlockBody] ++ func3NonemptyCleanup

private def func3EmptyMiddleFrame (body : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := body, continuation := func3SortAndCleanup,
    belowStack := [] }

private def func3EmptyReadyLocals : Locals :=
  func3AppendLocals 0 0 0 4 1 1 0 4 0 0 []

/-- Complete the valid empty-input arm.  The generated sorter is called with
its aligned dangling pointer at length zero; output, values retirement,
scratch retirement, and input retirement then take their explicit skip edges.
No dynamic allocation is introduced, so the empty history already satisfies
`AllRetired`. -/
theorem twp_func3_finish_empty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (chunkBytes outputBytes reserveBytes : List UInt8)
    (middleBody driverBody : Program)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId 0 1 [] chunkBytes outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams [] [] false ∗
      (RuntimeContext -∗
        DriverSuccess heapId [] -∗
        WP (.running
          ⟨func3AppendLocals 0 0 0 4 1 1 0 4 0 0 [],
            [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }])) ⊢
      WP (.running
        ⟨func3EmptyLocals, func3EmptyAfterReadSetup, 0, [],
          [func3EmptyMiddleFrame middleBody,
            func3CleanupOuterFrame driverBody],
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  simp only [func3EmptyAfterReadSetup, func3EmptyLocals, func3AppendLocals]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_exitControl]
  simp only [func3EmptyMiddleFrame, List.take_zero, List.nil_append,
    func3SortAndCleanup, List.cons_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  have Hsort := Project.Mergesort.ContractProofs.func2_correct
    (hlc := hlc) (source := 4) (n := 0) (scratch := 4) (scratchN := 0)
    (input := []) (scratchInput := [])
    (callerLocals := func3EmptyReadyLocals) (stack := [])
    (code := [.block 0 0 func3OutputBlockBody] ++ func3NonemptyCleanup)
    (arity := 0) (remainder := [])
    (controls := [func3CleanupOuterFrame driverBody]) (calls := calls)
    (s := s) (E := E) (Φ := Phi)
  unfold Func2Spec CallContract callExpr at Hsort
  simp only [List.cons_append, List.nil_append, func3EmptyReadyLocals,
    func3AppendLocals] at Hsort
  iapply Hsort
  isplitl_exact Hruntime
  isplitl []
  · iapply SortBuffers_empty 4 (by decide)
    itrivial
  isplitl_pureexact (by decide)
  iintro %sorted Hruntime Hresult
  isimp only [SortResultBuffers] at Hresult
  icases Hresult with ⟨Hbuffers, %hsorted⟩
  have hsortedLength := hsorted.2.length_eq
  have hsortedNil : sorted = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using hsortedLength.symm
  subst sorted
  isimp only [SortBuffers, WordSlice,
    Project.Mergesort.Representations.ByteSlice, List.length_nil,
    List.replicate_zero, List.nil_append] at Hbuffers
  iclear Hbuffers
  unfold ResumeWP resumeExpr
  simp only [List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3OutputBlockBody]
  wasm_twp_pures [twp_localGet]
  iapply twp_eqz (result := 1) (by simp)
  iapply twp_brIf (condition := 1) (depth := 0) (arity := 0)
    (targetCode := func3NonemptyCleanup)
    (targetControl := [func3CleanupOuterFrame driverBody])
    (targetValues := []) (by decide) (by rfl)
  simp only [func3NonemptyCleanup, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3ValuesDeallocBlockBody]
  wasm_twp_pures [twp_localGet]
  iapply twp_eqz (result := 1) (by simp)
  iapply twp_brIf (condition := 1) (depth := 0) (arity := 0)
    (targetCode :=
      [.block 0 0 func3ScratchDeallocBlockBody] ++ func3InputDeallocTail)
    (targetControl := [func3CleanupOuterFrame driverBody])
    (targetValues := []) (by decide) (by rfl)
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3ScratchDeallocBlockBody]
  wasm_twp_pures [twp_localGet]
  iapply twp_brIf (condition := 1) (depth := 0) (arity := 0)
    (targetCode := func3InputDeallocTail)
    (targetControl := [func3CleanupOuterFrame driverBody])
    (targetValues := []) (by decide) (by rfl)
  have Hinput := twp_func3_skip_empty_input
    (hlc := hlc) heapId chunkBytes outputBytes 0 heapBase.toNat
    AllocationHistory.empty 0 0 0 4 1 0 4 0 0
    driverBody func3RestoreStackTail (arity := 0) (remainder := [])
    (controls := []) (calls := calls) (s := s) (E := E) (Phi := Phi)
  simp only [func3AppendLocals, func3CleanupOuterFrame] at Hinput ⊢
  iapply Hinput
  isplitl_exact Hruntime
  isplitl_exact Hframe
  isplitl_exact Hbump
  iintro Hruntime Hbump HframeBytes %hframeLength
  have Hrestore := twp_func3_restore_stack reserveBytes
    (exportFrameBytes 0 1 [] chunkBytes outputBytes)
    0 0 0 4 1 1 0 4 0 0 hframeLength []
    (arity := 0) (remainder := []) (controls := []) (calls := calls)
    (s := s) (E := E) (Phi := Phi)
  simp only [List.append_nil, func3AppendLocals] at Hrestore ⊢
  iapply Hrestore
  isplitl_exact Hsp
  isplitl_exact Hreserve
  isplitl_exact HframeBytes
  iintro Hsp Hstack %hstackLength
  have hallRetired : AllRetired AllocationHistory.empty := by
    intro allocationId metadata hlookup
    simp [AllocationHistory.empty, LawfulPartialMap.get?_empty] at hlookup
  have hserializeEmpty : serialize ([] : List UInt32) = [] := rfl
  ihave Hstreams' : Streams [] (serialize ([] : List UInt32)) false $$
      [Hstreams]
  · isimp only [hserializeEmpty]
    iexact Hstreams
  ihave Hsuccess : DriverSuccess heapId [] $$ [Hsp Hstack Hbump Hstreams']
  · unfold DriverSuccess
    iexists [], reserveBytes ++ exportFrameBytes 0 1 [] chunkBytes outputBytes,
      0, heapBase.toNat, AllocationHistory.empty
    isplitl_pureexact ⟨⟨by simp, by simp⟩,
        hstackLength, hallRetired⟩
    · iframe
  iapply Hcont $$ Hruntime Hsuccess

/-- All dynamic ownership and ghost state carried across a read-loop
back-edge. -/
private structure Func3ReadLoopState where
  capacity : UInt32
  dataPtr : UInt32
  initialized : List UInt8
  current : List UInt8
  remaining : List UInt8
  chunkTail : List UInt8
  shadow : List UInt8
  storedCursor : UInt32
  frontier : Nat
  history : AllocationHistory

private def func3ReadLoopLocals
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (state : Func3ReadLoopState) : Locals :=
  func3AppendLocals state.dataPtr (UInt32.ofNat state.current.length)
    (UInt32.ofNat state.initialized.length)
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 []

/-- Shared continuation of every read-loop state.  The normal arm exposes a
fully accumulated byte vector; the exceptional arm accepts only one of the
authoritative phase-indexed driver OOM states. -/
def Func3ReadLoopContinuation
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  ((∀ completed : List UInt8, ∀ chunkBytes : List UInt8,
    ∀ finalShadow : List UInt8,
    ∀ finalCapacity : UInt32, ∀ finalPtr : UInt32,
    ∀ finalStoredCursor : UInt32,
    ∀ finalFrontier : Nat, ∀ finalHistory : AllocationHistory,
      RuntimeContext -∗
      StackPointer driverBase -∗
      StackReserve reserveBase finalShadow -∗
      ExportFrame heapId finalCapacity finalPtr completed chunkBytes
        outputBytes -∗
      BumpHeap heapId finalStoredCursor finalFrontier finalHistory -∗
      Streams [] [] false -∗
      ⌜serialize original = completed ∧
        GeometricVecFacts (serialize original).length completed.length 0
          finalCapacity finalPtr finalFrontier finalHistory⌝ -∗
      WP (.running
        ⟨func3AppendLocals finalPtr 0 (UInt32.ofNat completed.length)
            aux2 aux4 aux5 aux7 aux8 aux9 aux10 [],
          afterLoop, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) ∧
    ((∃ phase : DriverOOMPhase, DriverOOMState heapId original phase) -∗
      Φ (.trapped (.host OOM.trapMessage)))))

private def Func3ReadLoopInv
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (state : Func3ReadLoopState) : HeapIProp := iprop(
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
    GeometricVecFacts (serialize original).length state.initialized.length
      (state.current.length + state.remaining.length)
      state.capacity state.dataPtr state.frontier state.history⌝ ∗
  Func3ReadLoopContinuation heapId original outputBytes
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 afterLoop arity remainder controls
    calls s E Φ)

/-- The generated input loop is well-founded on unread bytes.  Its normal
exit reaches the continuation after the enclosing phase block; the
oversized-read panic continuation is never entered, and reserve failure is
packaged as the exact `.reserve` `DriverOOMState`. -/
theorem twp_func3_read_loop
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (initial : Func3ReadLoopState)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    Func3ReadLoopInv heapId original outputBytes
        aux2 aux4 aux5 aux7 aux8 aux9 aux10 afterLoop arity remainder controls
        calls s E Φ initial ⊢
      WP (.running
        ⟨func3ReadLoopLocals aux2 aux4 aux5 aux7 aux8 aux9 aux10 initial,
          [.loop 0 0 func3ReadLoopBody], arity, remainder,
          func3ReadInnerFrame :: func3ReadPhaseFrame afterLoop :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iapply Project.Mergesort.SortProof.twp_loop_wf_family_from_terminal
    (ι := Func3ReadLoopState)
    (measure := fun state => state.current.length + state.remaining.length)
    (locals := func3ReadLoopLocals aux2 aux4 aux5 aux7 aux8 aux9 aux10)
    (I := Func3ReadLoopInv heapId original outputBytes
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
    simp only [Func3ReadLoopInv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, %hfacts, Hfinish⟩
    isimp only [Func3ReadLoopContinuation] at Hfinish
    have htotal :
        (serialize original).length = state.initialized.length +
          state.current.length + state.remaining.length := by
      have hbytes := congrArg List.length hfacts.1
      simp only [List.length_append] at hbytes
      omega
    have Hiteration := twp_func3_read_loop_iteration hfunc1
      (serialize original).length state.current state.remaining state.capacity
      state.dataPtr state.initialized state.chunkTail outputBytes state.shadow
      heapId state.storedCursor state.frontier state.history []
      aux2 aux4 aux5 aux7 aux8 aux9 aux10
      ⟨hfacts.2.1, hfacts.2.2.1, hfacts.2.2.2.1,
        hfacts.2.2.2.2.1, hfacts.2.2.2.2.2.1, htotal,
        hfacts.2.2.2.2.2.2⟩
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
    isplitl_exact Hruntime
    isplitl_exact Hsp
    isplitl_exact Hreserve
    isplitl_exact Hframe
    isplitl_exact Hbump
    isplitl_exact Hstreams
    unfold Func3IterationContinuation
    isplit
    · isplit
      · iintro %finalCapacity %finalPtr %finalStoredCursor %finalFrontier
          %finalHistory %finalShadow Hruntime Hsp Hreserve Hframe Hbump
          Hstreams %hdone
        simp only [func3AppendLocals]
        iapply twp_brIf (condition := 1) (depth := 2) (arity := arity)
          (code := [.br 0]) (targetCode := afterLoop)
          (targetControl := controls) (targetValues := [])
          (by decide) (by rfl)
        ihave Hnormal := BI.and_elim_l $$ Hfinish
        iapply Hnormal $$ %(state.initialized ++ state.current)
          %(state.current ++ state.chunkTail) %finalShadow %finalCapacity
          %finalPtr %finalStoredCursor %finalFrontier %finalHistory Hruntime
          Hsp Hreserve Hframe Hbump Hstreams
        · ipureintro
          constructor
          · simpa [hdone.1, List.append_assoc] using hfacts.1
          · simpa only [List.length_append] using hdone.2
      · iintro %finalCapacity %finalPtr %finalStoredCursor %finalFrontier
          %finalHistory %finalShadow Hruntime Hsp Hreserve Hframe Hbump
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
        isplitl_exact Hruntime
        isplitl_exact Hsp
        isplitl_exact Hreserve
        isplitl_exact Hframe
        isplitl_exact Hbump
        isplitl_exact Hstreams
        isplitl []
        · ipureintro
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
              GeometricVecFacts (serialize original).length
                (state.initialized ++ state.current).length
                ((state.remaining.take (min 256 state.remaining.length)).length +
                  (state.remaining.drop (min 256 state.remaining.length)).length)
                finalCapacity finalPtr finalFrontier finalHistory := by
            simpa only [List.length_append] using
              hnext.2.2.2.2.2.2.2.1
          exact ⟨hserializeNext, hnext.1, hnext.2.1, hnext.2.2.1,
            hnext.2.2.2.1, hnext.2.2.2.2.1,
            hgeoNext⟩
        · unfold Func3ReadLoopContinuation
          simp only [func3AppendLocals]
          iexact Hfinish
    · iintro Hsp Hreserve Hframe Hbump Hstreams
      ihave Hoom := BI.and_elim_r $$ Hfinish
      iapply Hoom
      iexists DriverOOMPhase.reserve
      isimp only [DriverOOMState]
      unfold DriverReserveOOM
      isimp only [ExportFrame] at Hframe
      icases Hframe with ⟨Hvec, Hchunk, Houtput, %hframeLengths⟩
      iexists state.capacity, state.dataPtr, state.initialized, state.current,
        state.remaining, state.chunkTail, outputBytes, state.shadow,
        state.storedCursor, state.frontier, state.history
      isplitl_pureexact ⟨hfacts.1, hfacts.2.2.1, hfacts.2.2.2.2.1,
          hfacts.2.1, hframeLengths.1, hfacts.2.2.2.2.2.2⟩
      isplitl_exact Hsp
      isplitl_exact Hreserve
      isplitl [Hvec Hchunk Houtput]
      · unfold ExportFrame
        iframe
        ipureexact hframeLengths
      isplitl_exact Hbump
      · iexact Hstreams

/-- Enter the two generated blocks surrounding the read loop.  This theorem
fixes the control-frame layout used by the loop proof: the inner block's
continuation is precisely the excluded oversized-read panic tail, while the
outer phase block continues with `afterLoop`. -/
theorem twp_func3_read_phase
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32) (outputBytes : List UInt8)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (initial : Func3ReadLoopState)
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    Func3ReadLoopInv heapId original outputBytes
        aux2 aux4 aux5 aux7 aux8 aux9 aux10 afterLoop arity remainder controls
        calls s E Φ initial ⊢
      WP (.running
        ⟨func3ReadLoopLocals aux2 aux4 aux5 aux7 aux8 aux9 aux10 initial,
          .block 0 0 func3ReadPhaseBody :: afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro Hinv
  wasm_twp_pures [twp_block]
  simp only [func3ReadPhaseBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3ReadLoopBlockBody]
  have Hloop := twp_func3_read_loop hfunc1 heapId original outputBytes
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 initial
    (afterLoop := afterLoop) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3ReadInnerFrame, func3ReadPhaseFrame, func3ReadPhaseBody,
    func3ReadLoopBlockBody, func3ReadLoopLocals, func3AppendLocals,
    List.cons_append, List.nil_append] at Hloop
  simp only [func3ReadLoopLocals, func3AppendLocals, List.drop_zero]
  iapply Hloop
  iexact Hinv

/-- Execute a nonempty public input's first generated read, take the actual
`br_if 0` edge out of the initial-read block, initialize the Vec cursor
locals, and enter the proved read phase. -/
theorem twp_func3_first_read_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32) (outputBytes shadow : List UInt8)
    (horiginal : original ≠ [])
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      Func3ReadLoopContinuation heapId original outputBytes
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
    dsimp only [input]
    exact serialize_length original
  have hinputPositive : 0 < input.length := by
    have horiginalPositive : 0 < original.length := by
      by_contra hzero
      apply horiginal
      exact List.eq_nil_of_length_eq_zero (by omega)
    omega
  have hinputMod : input.length % 4 = 0 := by
    rw [hinputLength]
    omega
  have hsplit := readChunk_mod_four input hinputMod
  dsimp only at hsplit
  have hcountPositive : 0 < count := by
    dsimp only [count]
    omega
  have hcountSize : count < UInt32.size := by
    norm_num [UInt32.size]
    omega
  have hcountWord : (UInt32.ofNat count).toNat = count :=
    UInt32.toNat_ofNat_of_lt' hcountSize
  have hcountNonzero : UInt32.ofNat count ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    rw [hcountWord] at hzeroNat
    simp only [UInt32.toNat_zero] at hzeroNat
    omega
  have hremainingLength :
      input.length = current.length + remaining.length := by
    dsimp only [current, remaining]
    rw [← List.length_append, List.take_append_drop count input]
  have hcurrentLength : current.length = count := by
    exact hsplit.1
  have hcurrentShape :
      current.length = min 256 (current.length + remaining.length) := by
    rw [← hremainingLength]
    exact hsplit.1
  have hcurrentPositive : 0 < current.length := by
    rw [hcurrentLength]
    exact hcountPositive
  have hcurrentBound : current.length ≤ 256 := by
    rw [hcurrentLength]
    exact min_le_left 256 input.length
  have hcurrentMod : current.length % 4 = 0 := by
    rw [hcurrentLength]
    exact hsplit.2.1
  have hserializeSplit :
      serialize original = [] ++ current ++ remaining := by
    calc
      serialize original = input := rfl
      _ = current ++ remaining := by
        exact (List.take_append_drop count input).symm
      _ = [] ++ current ++ remaining := by simp
  have hgeo :
      GeometricVecFacts input.length 0
        (current.length + remaining.length) 0 1 heapBase.toNat
        AllocationHistory.empty := by
    left
    exact ⟨rfl, rfl, rfl, hremainingLength.symm, rfl, rfl⟩
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hfinish⟩
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
  isplitl_exact Hruntime
  isplitl_exact Hstreams
  isplitl_exact Hframe
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
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
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
  have Hphase := twp_func3_read_phase hfunc1 heapId original outputBytes
    4 0 0 0 0 0 0 initial
    (afterLoop := afterLoop) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [initial, func3ReadLoopLocals, func3AppendLocals,
    hcurrentLength, List.length_nil, UInt32.reduceOfNat] at Hphase
  iapply Hphase
  unfold Func3ReadLoopInv
  isplitl_exact Hruntime
  isplitl_exact Hsp
  isplitl_exact Hreserve
  isplitl_exact Hframe
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isplitl_pureexact ⟨hserializeSplit, hcurrentShape, hcurrentPositive,
      hcurrentBound, hcurrentMod, hsplit.2.2, by
        change GeometricVecFacts input.length 0
          (current.length + remaining.length) 0 1 heapBase.toNat
          AllocationHistory.empty
        exact hgeo⟩
  · iexact Hfinish

/-- Enter the exact generated initial-read block for a nonempty public input.
The block body still contains the empty-input suffix, but the preceding theorem
proves the nonzero read count takes the block branch before that suffix. -/
theorem twp_func3_initial_read_block_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32) (outputBytes shadow : List UInt8)
    (horiginal : original ≠ [])
    {afterLoop : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      Func3ReadLoopContinuation heapId original outputBytes
        4 0 0 0 0 0 0 afterLoop arity remainder controls calls s E Φ) ⊢
      WP (.running
        ⟨func3InitializedLocals,
          .block 0 0 func3InitialReadBody :: func3AfterInitialRead afterLoop,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro Hresources
  wasm_twp_pures [twp_block]
  have Hread := twp_func3_first_read_nonempty hfunc1 heapId original
    outputBytes shadow horiginal
    (afterLoop := afterLoop) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3InitialReadFrame, func3InitializedLocals] at Hread
  simp only [func3InitializedLocals, List.drop_zero]
  iapply Hread
  iexact Hresources

/-- Execute the disjoint empty-input arm of the exact initial-read block.
The zero read falls through `br_if 0`, sets the two generated empty-case
flags, and `br 1` exits the enclosing driver block without entering any
allocator or sorting path. -/
theorem twp_func3_first_read_empty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (outputBytes shadow : List UInt8)
    (afterLoop enclosingBody afterEmpty : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams [] [] false ∗
      (RuntimeContext -∗
        StackPointer driverBase -∗
        StackReserve reserveBase shadow -∗
        ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes -∗
        BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty -∗
        Streams [] [] false -∗
        WP (.running
          ⟨func3EmptyLocals, afterEmpty, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3InitializedLocals, func3InitialReadBody,
          arity, remainder,
          func3InitialReadFrame afterLoop ::
            func3EnclosingDriverFrame enclosingBody afterEmpty :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  have Hread := twp_func3_read_chunk heapId 0 1 []
    (List.replicate 256 0) outputBytes [] [] false []
    [.i32 driverBase, .i32 0, .i32 4, .i32 0, .i32 0, .i32 0,
      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
    rfl
    (stack := [])
    (code := [.localTee 3, .br_if 0] ++ func3EmptyInputSuffix)
    (arity := arity) (remainder := remainder)
    (controls := func3InitialReadFrame afterLoop ::
      func3EnclosingDriverFrame enclosingBody afterEmpty :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3InitialReadBody, func3InitialReadPrefix,
    func3EmptyInputSuffix, func3InitializedLocals,
    List.cons_append, List.nil_append] at Hread ⊢
  iapply Hread
  isplitl_exact Hruntime
  isplitl_exact Hstreams
  isplitl_exact Hframe
  iintro Hruntime Hstreams Hframe %_hcountBound
  iapply twp_localTee
      (locals' := func3AppendLocals 0 0 0 4 0 0 0 0 0 0 [.i32 0])
      (by simp [func3AppendLocals])
  simp only [func3AppendLocals]
  iapply twp_brIfZero (depth := 0) (arity := arity)
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length, List.set]
  iapply twp_br (depth := 1) (arity := arity) (code := [])
    (targetCode := afterEmpty) (targetControl := controls)
    (targetValues := []) (by rfl)
  simp only [func3EmptyLocals, func3AppendLocals]
  isimp only [List.length_nil, min_zero, List.take_zero, List.drop_zero,
    List.nil_append] at Hframe
  isimp only [List.length_nil, min_zero, List.drop_zero] at Hstreams
  iapply Hcont $$ Hruntime Hsp Hreserve Hframe Hbump Hstreams

/-- Enter the exact initial-read block on empty input, with the enclosing
driver frame made explicit so the generated `br 1` target is checked. -/
theorem twp_func3_initial_read_block_empty
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (outputBytes shadow : List UInt8)
    (afterLoop enclosingBody afterEmpty : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams [] [] false ∗
      (RuntimeContext -∗
        StackPointer driverBase -∗
        StackReserve reserveBase shadow -∗
        ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes -∗
        BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty -∗
        Streams [] [] false -∗
        WP (.running
          ⟨func3EmptyLocals, afterEmpty, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨func3InitializedLocals,
          .block 0 0 func3InitialReadBody :: func3AfterInitialRead afterLoop,
          arity, remainder,
          func3EnclosingDriverFrame enclosingBody afterEmpty :: controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro Hresources
  wasm_twp_pures [twp_block]
  have Hread := twp_func3_first_read_empty heapId outputBytes shadow
    afterLoop enclosingBody afterEmpty
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [func3InitialReadFrame, func3InitializedLocals] at Hread
  simp only [func3InitializedLocals, List.drop_zero]
  iapply Hread
  iexact Hresources

/-- Execute the generated `func3` prologue from raw entry ownership to the
reviewed initialized-frame representation.  No allocator, host call, or
driver semantic assumption is used here. -/
theorem twp_func3_initialize
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (entryBytes : List UInt8)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      StackPointer entryStackTop ∗
      StackRegion entryStackLow entryBytes ∗
      ⌜entryBytes.length = 288⌝ ∗
      (∀ reserveBytes : List UInt8,
        ∀ outputBytes : List UInt8,
        StackPointer driverBase -∗
        StackReserve reserveBase reserveBytes -∗
        ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes -∗
        WP (.running
          ⟨func3InitializedLocals, func3AfterInit, 0, [], [], calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
        ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
          0, [], [], calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hsp, Hentry, %hentryLength, Hcont⟩
  ihave HentryParts :
      iprop(StackRegion entryStackLow entryBytes ∗
        ⌜entryBytes.length = 288⌝) $$ [Hentry]
  · isplitl_exact Hentry
    · ipureexact hentryLength
  icases (EntryStack_split entryBytes).mp $$ HentryParts with
    ⟨%reserveBytes, %frameBytes, %hentryParts, Hreserve, Hframe⟩
  icases (DriverFrame_split frameBytes hentryParts.2.2).mp $$ Hframe with
    ⟨%headerBytes, %chunkBytes, %outputBytes, %hframeParts,
      Hheader, Hchunk, Houtput⟩
  have hdecode := serialize_decodeWords_of_length headerBytes 3 (by omega)
  obtain ⟨oldCapacity, oldPointer, oldLength, hdecoded⟩ :
      ∃ a b c : UInt32, decodeWords headerBytes = [a, b, c] := by
    rcases hwords : decodeWords headerBytes with _ | ⟨a, rest⟩
    · simp [hwords] at hdecode
    rcases hrest : rest with _ | ⟨b, rest⟩
    · simp [hwords, hrest] at hdecode
    rcases hrest2 : rest with _ | ⟨c, rest⟩
    · simp [hwords, hrest, hrest2] at hdecode
    rcases rest with _ | ⟨d, rest⟩
    · exact ⟨a, b, c, by simp⟩
    · simp [hwords, hrest, hrest2] at hdecode
  ihave HwordSlice := (ByteSlice_as_decodedWordSlice
      driverBase headerBytes 3 (by decide) hframeParts.2.1).mp $$ Hheader
  isimp only [WordSlice,
    Project.Mergesort.Representations.ByteSlice] at HwordSlice
  icases HwordSlice with ⟨%_halign, %_hwordNowrap, HwordBytes⟩
  ihave Harray : arrayAt 0 driverBase (decodeWords headerBytes) $$
      [HwordBytes]
  · iapply (arrayAt_eq_wordCells driverBase
      (decodeWords headerBytes)).mpr
    iexact HwordBytes
  isimp only [hdecoded] at Harray
  isimp only [arrayAt] at Harray
  icases Harray with ⟨HoldCapacity, HoldPointer, HoldLength, _Hemp⟩
  ihave HoldLength' :
      pointsTo_u32 0 (driverBase + 8) oldLength $$ [HoldLength]
  · rw [← show driverBase + 4 + 4 = driverBase + 8 by decide]
    iexact HoldLength
  ihave HoldPair := (pointsTo_u32_pair_as_u64
      driverBase oldCapacity oldPointer).mp $$ [HoldCapacity HoldPointer]
  · iframe
  isimp only [StackPointer] at Hsp
  simp only [Project.Mergesort.func3]
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  rw [show entryStackTop - 272 = driverBase by decide]
  wasm_twp_pures [twp_localTee]
  simp [Project.Mergesort.func3Def, Function.toLocals]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length_nil, Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_bind twp_store32 oldLength (by decide) (by decide) (by decide)
      (by decide) with HoldLength' => Hlength
  wasm_twp_pures [twp_localGet]
  iapply twp_pureStep _ _ _ (fun _ => Step.constI64)
  wasm_twp_bind twp_store64_zero (address := driverBase)
      (value := 4294967296)
      (oldCapacity.toUInt64 ||| (oldPointer.toUInt64 <<< 32))
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) with HoldPair => Hpair
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show 12 + driverBase = driverBase + 12 by decide]
  wasm_twp_pures [twp_const twp_const]
  isimp only [Project.Mergesort.Representations.ByteSlice] at Hchunk
  icases Hchunk with ⟨%hchunkNowrap, HchunkBytes⟩
  iapply twp_memoryFill32 chunkBytes (by
      simp [hframeParts.2.2.1]) (by decide) (by
      simpa [hframeParts.2.2.1, UInt32.size] using hchunkNowrap) $$
      HchunkBytes
  iintro HchunkBytes
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length_nil, Nat.reduceSub, List.set]
  ihave HpairWords :
      iprop(pointsTo_u32 0 driverBase 0 ∗
        pointsTo_u32 0 (driverBase + 4) 1) $$ [Hpair]
  · iapply (pointsTo_u32_pair_as_u64 driverBase 0 1).mpr
    rw [show (0 : UInt32).toUInt64 ||| ((1 : UInt32).toUInt64 <<< 32) =
      (4294967296 : UInt64) by decide]
    iexact Hpair
  icases HpairWords with ⟨Hcapacity, Hpointer⟩
  ihave Harray :
      arrayAt 0 driverBase [0, 1, 0] $$ [Hcapacity Hpointer Hlength]
  · isimp only [arrayAt]
    isplitl_exact Hcapacity
    isplitl_exact Hpointer
    isplitl_rw_exact [show driverBase + 4 + 4 = driverBase + 8 by decide] with Hlength
    · itrivial
  ihave HheaderBytes : WordCells driverBase [0, 1, 0] $$ [Harray]
  · iapply (arrayAt_eq_wordCells driverBase [0, 1, 0]).mp
    iexact Harray
  ihave Hheader : Project.Mergesort.Representations.ByteSlice
      driverBase emptyVecHeaderBytes $$ [HheaderBytes]
  · unfold Project.Mergesort.Representations.ByteSlice emptyVecHeaderBytes
    isplitl_pureexact (by decide)
    · iexact HheaderBytes
  ihave Hchunk : Project.Mergesort.Representations.ByteSlice
      (driverBase + 12) (List.replicate 256 0) $$ [HchunkBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    isplitl_pureexact (by simpa [hframeParts.2.2.1] using hchunkNowrap)
    · rw [← hframeParts.2.2.1]
      rw [← show (0 : UInt32).toUInt8 = (0 : UInt8) by decide]
      iexact HchunkBytes
  ihave Hexport := ExportFrame_empty heapId (List.replicate 256 0)
      outputBytes (by simp) hframeParts.2.2.2 $$ [Hheader Hchunk Houtput]
  · iframe
  ihave Hsp' : StackPointer driverBase $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  isimp only [List.replicate] at Hexport
  ihave Hdone := Hcont $$ %reserveBytes %outputBytes Hsp' Hreserve Hexport
  isimp only [func3InitializedLocals, func3AfterInit,
    Project.Mergesort.func3, List.drop_succ_cons, List.drop_zero,
    ValueType.zero] at Hdone
  isimp only [ValueType.zero]
  iexact Hdone

/-! ## Exact whole-driver control structure -/

/-- Values-allocation, decode, and scratch-allocation code in the innermost
generated nonempty block. -/
private def func3AllocationBody : Program :=
  [.call 7, .localGet 7, .const 4, .call 8,
    .localTee 2, .eqz, .br_if 1] ++ func3DecodeSetup ++
    [.block 0 0 func3DecodeOuterBlockBody,
      .call 7, .localGet 9, .const 2, .shl, .localTee 10,
      .const 4, .call 12] ++ func3ScratchSuccessTail

/-- Complete body of the innermost nonempty block, including the two guards
which establish whole-word, nonempty input before allocation. -/
private def func3DecodeAllocationBody : Program :=
  func3CompletedLengthGuard ++
    [.block 0 0 func3AlignedLengthBlockBody] ++ func3AllocationBody

/-- Cleanup edge retained by the compiler for a null values result.  The
allocator contract makes this edge unreachable on a normal return. -/
private def func3EarlyInputCleanup : Program :=
  [.localGet 0, .load32 0, .localTee 3, .eqz, .br_if 4,
    .localGet 4, .localGet 3, .const 1, .call 10, .br 4]

private def func3ValuesAllocationPanic : Program :=
  [.const 4, .localGet 7, .call 46, .unreachable]

private def func3ScratchAllocationPanic : Program :=
  [.const 4, .localGet 10, .call 46, .unreachable]

private def func3ValuesOuterBody : Program :=
  [.block 0 0 func3DecodeAllocationBody] ++ func3EarlyInputCleanup

private def func3ScratchOuterBody : Program :=
  [.block 0 0 func3ValuesOuterBody] ++ func3ValuesAllocationPanic

/-- Body of the block containing the initial read, the read loop, and the
complete nonempty allocation/decode dispatch. -/
private def func3ReadAndDispatchBody : Program :=
  [.block 0 0 func3InitialReadBody] ++
    func3AfterInitialRead
      (func3CompletedPtrReload ++
        [.block 0 0 func3ScratchOuterBody] ++
        func3ScratchAllocationPanic)

/-- Body of the block whose fallthrough is the valid empty-input setup. -/
private def func3MiddleBody : Program :=
  [.block 0 0 func3ReadAndDispatchBody] ++ func3EmptyAfterReadSetup

/-- Exact body of the outermost generated driver block. -/
private def func3DriverBody : Program :=
  [.block 0 0 func3MiddleBody] ++ func3SortAndCleanup

private def func3DecodeAllocationFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3DecodeAllocationBody,
    continuation := func3EarlyInputCleanup, belowStack := [] }

private def func3ValuesOuterFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3ValuesOuterBody,
    continuation := func3ValuesAllocationPanic, belowStack := [] }

private def func3ScratchOuterFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := func3ScratchOuterBody,
    continuation := func3ScratchAllocationPanic, belowStack := [] }

private def func3ReadAndDispatchFrame : ControlFrame :=
  func3EnclosingDriverFrame func3ReadAndDispatchBody func3EmptyAfterReadSetup

/-- The six exact frames surrounding the successful scratch-allocation tail. -/
private def func3ScratchSuccessControls : List ControlFrame :=
  [func3DecodeAllocationFrame,
    func3ValuesOuterFrame,
    func3ScratchOuterFrame,
    func3ReadAndDispatchFrame,
    func3EmptyMiddleFrame func3MiddleBody,
    func3CleanupOuterFrame func3DriverBody]

private theorem func3_scratch_success_branch :
    branchTarget? 0 4 func3ScratchSuccessControls [] =
      some (func3SortAndCleanup,
        [func3CleanupOuterFrame func3DriverBody], []) := by
  rfl

private theorem geometricVec_frontier_ge_heapBase
    (total length remaining : Nat) (capacity ptr : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (hgeo : GeometricVecFacts total length remaining capacity ptr frontier
      history) :
    heapBase.toNat ≤ frontier := by
  rcases hgeo with hinitial | hshort | hlarge
  · rw [hinitial.2.2.2.2.1]
  · rw [hshort.2.2.2.2.2.1]
    omega
  · rcases hlarge with
      ⟨exponent, hexponent, _hexponentUpper, _hcapacity, _hlength,
        _htotal, _hptr, hfrontier, _hhistory⟩
    rw [hfrontier]
    unfold vectorBlockBase
    have hpow : 256 ≤ 2 ^ exponent := by
      rw [show 256 = 2 ^ 8 by norm_num]
      exact Nat.pow_le_pow_right (by decide) hexponent
    omega

/-- Compose the complete valid nonempty allocation/decode/sort/output path.
The only terminal alternatives admitted by the two allocator contracts are
the phase-indexed `talos.oom` outcomes. -/
theorem twp_func3_complete_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (hfunc5 : Func5Spec (hlc := hlc))
    (hfunc9 : Func9Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32)
    (capacity inputPtr : UInt32)
    (chunkBytes outputBytes reserveBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hgeo : GeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity inputPtr frontier history)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId capacity inputPtr (serialize original) chunkBytes
        outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      (∀ finalLocals : Locals,
        RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }]) ∗
      ((∃ phase : DriverOOMPhase, DriverOOMState heapId original phase) -∗
        Phi (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
        ⟨func3AppendLocals inputPtr 0
            (UInt32.ofNat (4 * original.length)) 4 inputPtr 0
            (UInt32.ofNat (4 * original.length)) 0 0 0 [],
          func3AllocationBody, 0, [], func3ScratchSuccessControls, calls⟩ :
            Expr Universal.State) @ s; E [{ Phi }] := by
  let layout : AllocLayout :=
    { size := 4 * original.length, alignment := 4 }
  have hpositive : 0 < original.length :=
    List.length_pos_iff_ne_nil.mpr horiginal
  have hbyteBoundSigned : 4 * original.length < 2147483648 := by
    have htotal := GeometricVecFacts.completed_lt_signed
      (serialize original).length (serialize original).length 0 capacity
      inputPtr frontier history hgeo rfl
    simpa only [serialize_length] using htotal
  have hbyteBound : 4 * original.length < UInt32.size := by
    norm_num [UInt32.size] at hbyteBoundSigned ⊢
    omega
  have hlayoutValid : layout.Valid := by
    exact align4Layout_valid_of_bounds (4 * original.length)
      (by omega) hbyteBoundSigned (by omega)
  have hfrontier : heapBase.toNat ≤ frontier :=
    geometricVec_frontier_ge_heapBase _ _ _ _ _ _ _ hgeo
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone, Hoom⟩
  have HvaluesAlloc := twp_func3_allocate_values hfunc5 heapId original
    capacity inputPtr (serialize original) chunkBytes outputBytes reserveBytes
    storedCursor frontier history horiginal rfl hgeo
    (func3AppendLocals inputPtr 0 (UInt32.ofNat (4 * original.length)) 4
      inputPtr 0 (UInt32.ofNat (4 * original.length)) 0 0 0 [])
    (by
      simp [func3AppendLocals, U32Codec, Spec.u32Codec])
    (stack := [])
    (code := [.localTee 2, .eqz, .br_if 1] ++ func3DecodeSetup ++
      [.block 0 0 func3DecodeOuterBlockBody,
        .call 7, .localGet 9, .const 2, .shl, .localTee 10,
        .const 4, .call 12] ++ func3ScratchSuccessTail)
    (arity := 0) (remainder := [])
    (controls := func3ScratchSuccessControls) (calls := calls)
    (s := s) (E := E) (Φ := Phi)
  simp only [func3AllocationBody, func3AppendLocals, List.cons_append,
    List.nil_append]
    at HvaluesAlloc ⊢
  iapply HvaluesAlloc
  isplitl_exact Hruntime
  isplitl_exact Hsp
  isplitl_exact Hreserve
  isplitl_exact Hframe
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isplit
  · iintro %valuesPtr %valuesFinish %valuesBytes %hvaluesClassify
      Hruntime Hsp Hreserve Hframe Hbump Hvalues Hstreams
    have hvaluesFacts := classifyBump_success_reachable frontier layout
      valuesPtr valuesFinish hfrontier hlayoutValid (Or.inr rfl)
      (by simpa only [layout, serialize_length] using hvaluesClassify)
    have hvaluesEnd :
        valuesPtr.toNat + 4 * original.length ≤ valuesFinish.toNat := by
      rw [hvaluesFacts.2.2.2.2.2.1]
    have hvaluesFrontier : heapBase.toNat ≤ valuesFinish.toNat := by
      exact Nat.le_trans hfrontier
        (Nat.le_trans hvaluesFacts.1 (by omega))
    unfold ResumeWP resumeExpr
    have Hdecode := twp_func3_decode_allocated heapId history.nextId capacity
      inputPtr valuesPtr original chunkBytes outputBytes valuesBytes frontier
      history 0 4 0 0 0 horiginal hgeo
      (afterDecode := [.call 7, .localGet 9, .const 2, .shl,
        .localTee 10, .const 4, .call 12] ++ func3ScratchSuccessTail)
      (arity := 0) (remainder := [])
      (controls := func3ScratchSuccessControls) (calls := calls)
      (s := s) (E := E) (Φ := Phi)
    simp only [func3AppendLocals, List.append_assoc, List.cons_append,
      List.nil_append]
      at Hdecode ⊢
    iapply Hdecode
    isplitl_exact Hframe
    isplitl [Hvalues]
    · isimp only [serialize_length] at Hvalues
      iexact Hvalues
    iintro %final1 %final3 %final6 %final5 %final8 Hframe Hvalues
    have HscratchAlloc := twp_func3_allocate_scratch hfunc9 heapId
      history.nextId capacity inputPtr valuesPtr original chunkBytes outputBytes
      reserveBytes valuesFinish valuesFinish.toNat
      (history.allocate valuesPtr layout) final1 final3 final6 final5 final8 0
      hpositive hbyteBoundSigned hvaluesFrontier hvaluesEnd
      (code := func3ScratchSuccessTail) (arity := 0) (remainder := [])
      (controls := func3ScratchSuccessControls) (calls := calls)
      (s := s) (E := E) (Φ := Phi)
    simp only [func3AppendLocals, List.cons_append, List.nil_append]
      at HscratchAlloc ⊢
    iapply HscratchAlloc
    isplitl_exact Hruntime
    isplitl_exact Hsp
    isplitl_exact Hreserve
    isplitl_exact Hframe
    isplitl_exact Hvalues
    isplitl [Hbump]
    · isimp only [serialize_length] at Hbump
      iexact Hbump
    isplitl_exact Hstreams
    isplit
    · iintro %scratchPtr %scratchFinish %hscratchClassify
        Hruntime Hsp Hreserve Hframe Hvalues Hbump Hscratch Hstreams
        %hdisjoint
      unfold ResumeWP resumeExpr
      have HscratchTail := twp_func3_scratch_success_tail heapId
        (history.allocate valuesPtr layout).nextId scratchPtr layout
        (List.replicate layout.size 0) original.length final1 final3 final6
        valuesPtr inputPtr final5 final8 hbyteBound
        func3_scratch_success_branch
        (arity := 0) (remainder := [])
        (controls := func3ScratchSuccessControls)
        (targetControls := [func3CleanupOuterFrame func3DriverBody])
        (targetCode := func3SortAndCleanup) (calls := calls)
        (s := s) (E := E) (Phi := Phi)
      simp only [func3AppendLocals, List.append_nil] at HscratchTail ⊢
      iapply HscratchTail
      iframe; iintro Hscratch
      have Hsort := twp_func3_sort heapId history.nextId
        (history.allocate valuesPtr layout).nextId valuesPtr scratchPtr inputPtr
        original (UInt32.ofNat original.length) final3 final6 0
        (UInt32.ofNat (4 * original.length)) hdisjoint hbyteBound
        (code := [.block 0 0 func3OutputBlockBody] ++ func3NonemptyCleanup)
        (arity := 0) (remainder := [])
        (controls := [func3CleanupOuterFrame func3DriverBody])
        (calls := calls) (s := s) (E := E) (Φ := Phi)
      simp only [func3SortAndCleanup, func3AppendLocals, List.cons_append,
        List.nil_append] at Hsort ⊢
      iapply Hsort
      isplitl_exact Hruntime
      isplitl_exact Hvalues
      isplitl_exact Hscratch
      iintro %sorted Hruntime Hvalues Hscratch %hsorted
      have hsortedLength : sorted.length = original.length :=
        hsorted.2.length_eq.symm
      have hsortedByteBound : 4 * sorted.length < UInt32.size := by
        simpa only [hsortedLength] using hbyteBound
      let scratchValues : List UInt32 :=
        if original.length ≤ 1 then List.replicate original.length 0
        else sorted
      have hscratchLength : scratchValues.length = sorted.length := by
        dsimp only [scratchValues]
        split <;> simp [hsortedLength]
      have Houtput := twp_func3_output heapId history.nextId capacity inputPtr
        valuesPtr (serialize original) chunkBytes outputBytes sorted
        (UInt32.ofNat original.length) final3 final6 inputPtr 0
        (UInt32.ofNat (4 * original.length)) scratchPtr
        (UInt32.ofNat (4 * original.length)) hsortedByteBound
        (afterOutput := func3NonemptyCleanup) (arity := 0) (remainder := [])
        (controls := [func3CleanupOuterFrame func3DriverBody])
        (calls := calls) (s := s) (E := E) (Φ := Phi)
      simp only [func3AppendLocals, hsortedLength, List.cons_append,
        List.nil_append] at Houtput ⊢
      iapply Houtput
      isplitl_exact Hruntime
      isplitl_exact Hframe
      isplitl_exact Hvalues
      isplitl_exact Hstreams
      iintro %outputCursor %final6' %finalOutput Hruntime Hframe Hvalues
        Hstreams
      have Hfinish := twp_func3_finish_nonempty heapId original sorted
        scratchValues capacity inputPtr valuesPtr scratchPtr history.nextId
        (history.allocate valuesPtr layout).nextId chunkBytes finalOutput
        reserveBytes scratchFinish scratchFinish.toNat frontier history
        outputCursor final6' hsorted hpositive hscratchLength hgeo rfl
        (by simp [AllocationHistory.allocate]) hbyteBound func3DriverBody
        (calls := calls) (s := s) (E := E) (Phi := Phi)
      simp only [func3AppendLocals, hsortedLength] at Hfinish ⊢
      iapply Hfinish
      isplitl_exact Hruntime
      isplitl_exact Hsp
      isplitl_exact Hreserve
      isplitl_exact Hframe
      isplitl_exact Hvalues
      isplitl [Hscratch]
      · isimp only [scratchValues]
        iexact Hscratch
      isplitl [Hbump]
      · isimp only [layout] at Hbump
        iexact Hbump
      isplitl_exact Hstreams
      iintro Hruntime Hsuccess
      iapply Hdone $$ Hruntime Hsuccess
    · iintro HscratchOOM
      iapply Hoom
      iexists DriverOOMPhase.scratch
      isimp only [DriverOOMState]
      iexact HscratchOOM
  · iintro HvaluesOOM
    iapply Hoom
    iexists DriverOOMPhase.values
    isimp only [DriverOOMState]
    iexact HvaluesOOM

/-- Enter the three generated allocation-error blocks after the completed
read, discharge the canonical whole-word/nonempty guards, and hand the exact
innermost continuation to `twp_func3_complete_nonempty`. -/
theorem twp_func3_completed_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (hfunc5 : Func5Spec (hlc := hlc))
    (hfunc9 : Func9Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32)
    (capacity inputPtr : UInt32)
    (chunkBytes outputBytes reserveBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hgeo : GeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity inputPtr frontier history)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId capacity inputPtr (serialize original) chunkBytes
        outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      (∀ finalLocals : Locals,
        RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }]) ∗
      ((∃ phase : DriverOOMPhase, DriverOOMState heapId original phase) -∗
        Phi (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
        ⟨func3AppendLocals inputPtr 0
            (UInt32.ofNat (4 * original.length)) 4 0 0 0 0 0 0 [],
          func3CompletedPtrReload ++
            [.block 0 0 func3ScratchOuterBody] ++
            func3ScratchAllocationPanic,
          0, [],
          [func3ReadAndDispatchFrame,
            func3EmptyMiddleFrame func3MiddleBody,
            func3CleanupOuterFrame func3DriverBody],
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone, Hoom⟩
  have Hreload := twp_func3_reload_completed_ptr heapId capacity inputPtr
    (serialize original) chunkBytes outputBytes 0 4 0 0 0 0 0 0
    (stack := [])
    (code := [.block 0 0 func3ScratchOuterBody] ++
      func3ScratchAllocationPanic)
    (arity := 0) (remainder := [])
    (controls := [func3ReadAndDispatchFrame,
      func3EmptyMiddleFrame func3MiddleBody,
      func3CleanupOuterFrame func3DriverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3CompletedPtrReload, func3AppendLocals, serialize_length,
    List.cons_append, List.nil_append] at Hreload ⊢
  iapply Hreload
  iframe; iintro Hframe
  wasm_twp_pures [twp_block]
  simp only [func3ScratchOuterBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3ValuesOuterBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3DecodeAllocationBody]
  have Hguards := twp_func3_enter_nonempty_decode original
    (serialize original) capacity inputPtr frontier history horiginal rfl hgeo
    0 4 inputPtr 0 0 0 0 0
    (stack := []) (afterBlock := func3AllocationBody)
    (arity := 0) (remainder := [])
    (controls := func3ScratchSuccessControls) (calls := calls)
    (s := s) (E := E) (Φ := Phi)
  simp only [func3CompletedLengthGuard, func3AppendLocals, serialize_length,
    func3ScratchSuccessControls, func3DecodeAllocationFrame,
    func3ValuesOuterFrame, func3ScratchOuterFrame, List.drop_zero,
    func3DecodeAllocationBody, func3ValuesOuterBody, func3ScratchOuterBody,
    List.cons_append, List.nil_append] at Hguards ⊢
  iapply Hguards
  have Hcomplete := twp_func3_complete_nonempty hfunc5 hfunc9 heapId original
    capacity inputPtr chunkBytes outputBytes reserveBytes storedCursor frontier
    history horiginal hgeo (calls := calls) (s := s) (E := E) (Phi := Phi)
  simp only [func3AppendLocals, func3ScratchSuccessControls,
    func3DecodeAllocationFrame, func3ValuesOuterFrame,
    func3ScratchOuterFrame, func3DecodeAllocationBody,
    func3ValuesOuterBody, func3ScratchOuterBody,
    func3CompletedLengthGuard, List.cons_append, List.nil_append]
    at Hcomplete ⊢
  iapply_frame Hcomplete

/-- Execute the exact initial-read block and well-founded read loop for a
nonempty public input, then compose its authoritative completed-Vec result
with the full nonempty suffix. -/
theorem twp_func3_read_dispatch_nonempty
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (hfunc5 : Func5Spec (hlc := hlc))
    (hfunc9 : Func9Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32)
    (outputBytes reserveBytes : List UInt8)
    (horiginal : original ≠ [])
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      (∀ finalLocals : Locals,
        RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }]) ∗
      ((∃ phase : DriverOOMPhase, DriverOOMState heapId original phase) -∗
        Phi (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
        ⟨func3InitializedLocals, func3ReadAndDispatchBody, 0, [],
          [func3ReadAndDispatchFrame,
            func3EmptyMiddleFrame func3MiddleBody,
            func3CleanupOuterFrame func3DriverBody],
          calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone, Hoom⟩
  have Hread := twp_func3_initial_read_block_nonempty hfunc1 heapId original
    outputBytes reserveBytes horiginal
    (afterLoop := func3CompletedPtrReload ++
      [.block 0 0 func3ScratchOuterBody] ++
      func3ScratchAllocationPanic)
    (arity := 0) (remainder := [])
    (controls := [func3ReadAndDispatchFrame,
      func3EmptyMiddleFrame func3MiddleBody,
      func3CleanupOuterFrame func3DriverBody])
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  simp only [func3ReadAndDispatchBody, func3AfterInitialRead,
    func3InitializedLocals, List.cons_append, List.nil_append] at Hread ⊢
  iapply Hread
  isplitl_exact Hruntime
  isplitl_exact Hsp
  isplitl_exact Hreserve
  isplitl_exact Hframe
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isimp only [Func3ReadLoopContinuation]
  isplit
  · iintro %completed %chunkBytes %finalShadow %finalCapacity %finalPtr
      %finalStoredCursor %finalFrontier %finalHistory Hruntime Hsp Hreserve
      Hframe Hbump Hstreams %hfacts
    have hgeo : GeometricVecFacts (serialize original).length
        (serialize original).length 0 finalCapacity finalPtr finalFrontier
        finalHistory := by
      simpa only [← hfacts.1] using hfacts.2
    isimp only [← hfacts.1] at Hframe
    have Hcompleted := twp_func3_completed_nonempty hfunc5 hfunc9 heapId
      original finalCapacity finalPtr chunkBytes outputBytes finalShadow
      finalStoredCursor finalFrontier finalHistory horiginal hgeo
      (calls := calls) (s := s) (E := E) (Phi := Phi)
    simp only [← hfacts.1, func3AppendLocals, serialize_length]
      at Hcompleted ⊢
    iapply_frame Hcompleted
  · iintro HOOM
    iapply Hoom
    iexact HOOM

/-- Audited decomposition of the generated body following its 21-instruction
prologue. -/
private theorem func3_after_init_exact :
    func3AfterInit =
      [.block 0 0 func3DriverBody] ++ func3RestoreStackTail := by
  simp [func3AfterInit, func3DriverBody, func3MiddleBody,
    func3ReadAndDispatchBody, func3AfterInitialRead, func3ReadPhaseBody,
    func3ReadLoopBlockBody, func3ReadLoopBody, func3AppendBody,
    func3ReadClassifyBody, func3InitialReadBody, func3InitialReadPrefix,
    func3EmptyInputSuffix, func3CapacityBody, func3AppendCopyBody,
    func3OversizedReadPanic, func3ScratchOuterBody, func3ValuesOuterBody,
    func3DecodeAllocationBody, func3AllocationBody, func3EarlyInputCleanup,
    func3CompletedPtrReload, func3CompletedLengthGuard,
    func3AlignedLengthBlockBody, func3DecodeSetup, func3DecodeOuterBlockBody,
    func3DecodeBulkBlockBody, func3DecodeTailContinuation,
    func3DecodeBulkLoopBody, func3DecodeTailLoopBody,
    func3ScratchSuccessTail, func3ValuesAllocationPanic,
    func3ScratchAllocationPanic,
    func3SortAndCleanup, func3NonemptyCleanup, func3InputDeallocTail,
    func3EmptyAfterReadSetup, func3OutputBlockBody, func3OutputLoopBody,
    func3ValuesDeallocBlockBody, func3ScratchDeallocBlockBody,
    func3RestoreStackTail, Project.Mergesort.func3]

/-- Compose the exact nested driver blocks.  The public input is split once:
the empty arm takes the compiler's early branch, while the nonempty arm uses
the read-loop and allocation composition above. -/
theorem twp_func3_after_initialize
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (hfunc5 : Func5Spec (hlc := hlc))
    (hfunc9 : Func9Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32)
    (outputBytes reserveBytes : List UInt8)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase reserveBytes ∗
      ExportFrame heapId 0 1 [] (List.replicate 256 0) outputBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      (∀ finalLocals : Locals,
        RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }]) ∗
      ((∃ phase : DriverOOMPhase, DriverOOMState heapId original phase) -∗
        Phi (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
        ⟨func3InitializedLocals, func3AfterInit, 0, [], [], calls⟩ :
          Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hdone, Hoom⟩
  rw [func3_after_init_exact]
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3DriverBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3MiddleBody, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_block]
  simp only [func3InitializedLocals, List.drop_zero]
  by_cases horiginal : original = []
  · subst original
    have Hread := twp_func3_initial_read_block_empty heapId outputBytes
      reserveBytes
      (func3CompletedPtrReload ++ [.block 0 0 func3ScratchOuterBody] ++
        func3ScratchAllocationPanic)
      func3ReadAndDispatchBody func3EmptyAfterReadSetup
      (arity := 0) (remainder := [])
      (controls := [func3EmptyMiddleFrame func3MiddleBody,
        func3CleanupOuterFrame func3DriverBody])
      (calls := calls) (s := s) (E := E) (Φ := Phi)
    simp only [func3ReadAndDispatchBody, func3AfterInitialRead,
      func3InitializedLocals, func3EnclosingDriverFrame,
      func3EmptyMiddleFrame, func3CleanupOuterFrame, func3MiddleBody,
      func3DriverBody, func3SortAndCleanup,
      List.cons_append, List.nil_append] at Hread ⊢
    iapply Hread
    isplitl_exact Hruntime
    isplitl_exact Hsp
    isplitl_exact Hreserve
    isplitl_exact Hframe
    isplitl_exact Hbump
    isplitl [Hstreams]
    · isimp only [serialize, WordCodec.serialize, List.flatMap_nil] at Hstreams
      iexact Hstreams
    iintro Hruntime Hsp Hreserve Hframe Hbump Hstreams
    have Hempty := twp_func3_finish_empty heapId
      (List.replicate 256 0) outputBytes reserveBytes func3MiddleBody
      func3DriverBody (calls := calls) (s := s) (E := E) (Phi := Phi)
    simp only [func3EmptyLocals, func3AppendLocals,
      func3EmptyMiddleFrame, func3CleanupOuterFrame, func3MiddleBody,
      func3DriverBody, func3ReadAndDispatchBody, func3AfterInitialRead,
      func3SortAndCleanup, List.cons_append, List.nil_append] at Hempty ⊢
    iapply Hempty
    isplitl_exact Hruntime
    isplitl_exact Hsp
    isplitl_exact Hreserve
    isplitl_exact Hframe
    isplitl_exact Hbump
    isplitl_exact Hstreams
    iintro Hruntime Hsuccess
    iapply Hdone $$ Hruntime Hsuccess
  · have Hnonempty := twp_func3_read_dispatch_nonempty hfunc1 hfunc5
      hfunc9 heapId original outputBytes reserveBytes horiginal
      (calls := calls) (s := s) (E := E) (Phi := Phi)
    simp only [func3InitializedLocals, func3ReadAndDispatchFrame,
      func3EnclosingDriverFrame, func3EmptyMiddleFrame,
      func3CleanupOuterFrame, func3MiddleBody, func3DriverBody,
      func3SortAndCleanup, List.cons_append,
      List.nil_append] at Hnonempty ⊢
    iapply_frame Hnonempty

/-- Execute the generated prologue and the complete reviewed driver body,
stopping at the administrative return boundary. -/
theorem twp_func3_body
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (hfunc5 : Func5Spec (hlc := hlc))
    (hfunc9 : Func9Spec (hlc := hlc))
    (heapId : GName) (original : List UInt32) (entryBytes : List UInt8)
    (hentryLength : entryBytes.length = 288)
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer entryStackTop ∗
      StackRegion entryStackLow entryBytes ∗
      BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
      Streams (serialize original) [] false ∗
      (∀ finalLocals : Locals,
        RuntimeContext -∗ DriverSuccess heapId original -∗
        WP (.running
          ⟨finalLocals, [], 0, [], [], calls⟩ : Expr Universal.State)
          @ s; E [{ Phi }]) ∗
      ((∃ phase : DriverOOMPhase, DriverOOMState heapId original phase) -∗
        Phi (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
        ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
          0, [], [], calls⟩ : Expr Universal.State) @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, Hsp, Hstack, Hbump, Hstreams, Hdone, Hoom⟩
  have Hinitialize := twp_func3_initialize heapId entryBytes
    (calls := calls) (s := s) (E := E) (Φ := Phi)
  iapply Hinitialize
  isplitl_exact Hsp
  isplitl_exact Hstack
  isplitl_pureexact hentryLength
  iintro %reserveBytes %outputBytes Hsp Hreserve Hframe
  have Hbody := twp_func3_after_initialize hfunc1 hfunc5 hfunc9 heapId
    original outputBytes reserveBytes (calls := calls) (s := s) (E := E)
    (Phi := Phi)
  iapply_frame Hbody

private theorem func3_index :
    Project.Mergesort.module.funcs[3]? =
      some Project.Mergesort.func3Def := by
  rfl

/-- The authoritative `func3` call contract, conditional only on the three
reachable allocator/Vec contracts that are proved in their own files. -/
theorem func3_correct_of
    [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc))
    (hfunc5 : Func5Spec (hlc := hlc))
    (hfunc9 : Func9Spec (hlc := hlc)) :
    Func3Spec (hlc := hlc) := by
  unfold Func3Spec CallContract callExpr
  intro heapId original entryBytes callerLocals stack code arity remainder
    controls calls s E Phi
  iintro ⟨Hruntime, Hsp, Hstack, Hbump, Hstreams, %hentryLength,
    Hnormal, Hoom⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.Mergesort.module 6
      Project.Mergesort.func3Def (by decide) func3_index with Hmodule
  simp [Project.Mergesort.func3Def, Function.toLocals, Function.numParams]
  let callerFrame : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := ⟨0⟩ }
  have Hbody := twp_func3_body hfunc1 hfunc5 hfunc9 heapId original
    entryBytes hentryLength (calls := callerFrame :: calls)
    (s := s) (E := E) (Phi := Phi)
  simp [Project.Mergesort.func3Def, Function.toLocals, callerFrame] at Hbody
  iapply Hbody
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe
  isplitl_exact Hsp
  isplitl_exact Hstack
  isplitl_exact Hbump
  isplitl_exact Hstreams
  isplitl [Hnormal]
  · iintro %finalLocals Hruntime Hsuccess
    iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
    simp only [List.take_zero, List.nil_append]
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
    ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
    · unfold RuntimeContext
      iframe
    iapply Hnormal $$ Hruntime Hsuccess
  · iexact Hoom

end Project.Mergesort.DriverProof
