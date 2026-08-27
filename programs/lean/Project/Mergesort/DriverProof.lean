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
  · iintro H
    icases H with ⟨Hlo, Hhi⟩
    icases Hlo with ⟨H0, H1, H2, H3⟩
    icases Hhi with ⟨H4, H5, H6, H7⟩
    iframe
  · iintro H
    icases H with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
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
  iapply twp_const
  iapply twp_add
  rw [show 12 + driverBase = driverBase + 12 by decide]
  iapply twp_const
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
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [Hchunk]
  · iexact Hchunk
  isplitl []
  · ipureintro
    exact ⟨by simpa using hframeLengths.1.symm, by decide⟩
  iintro Hruntime Hstreams Hchunk %hcount
  ihave Hframe : ExportFrame heapId capacity ptr initialized
      (input.take count ++ chunkBytes.drop count) outputBytes $$
      [Hvec Hchunk Houtput]
  · unfold ExportFrame
    isplitl [Hvec]
    · iexact Hvec
    isplitl [Hchunk]
    · iexact Hchunk
    isplitl [Houtput]
    · iexact Houtput
    ipureintro
    constructor
    · have htake := List.length_take_le count input
      simp [count, hframeLengths.1]
    · exact hframeLengths.2
  unfold ResumeWP resumeExpr
  simp only [List.cons_append, List.nil_append]
  iapply Hcont $$ Hruntime Hstreams Hframe
  · ipureintro
    exact hcount

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
  iapply twp_block
  simp only [func3AppendCopyBody, func3AppendLocals]
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [hcurrentNonzero])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show 12 + driverBase = driverBase + 12 by decide]
  iapply twp_localGet rfl
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
    ipureintro
    exact hcurrentNowrap
  ihave Hchunk : Project.Mergesort.Representations.ByteSlice
      (driverBase + 12) (current ++ chunkTail) $$ [Hcurrent HchunkTail]
  · iapply (ByteSlice_append (driverBase + 12) current chunkTail).mpr
    iframe
  ihave HnewBytes : Project.Mergesort.Representations.ByteSlice
      (dataPtr + UInt32.ofNat initialized.length) current $$
      [HoldChunkBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    iframe
    ipureintro
    rw [holdChunkLength] at holdChunkNowrap
    exact holdChunkNowrap
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
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
  iapply twp_store32 (UInt32.ofNat initialized.length)
      (by decide) (by decide) (by decide) (by decide) $$ HoldLength
  iintro HnewLength
  ihave Hvec := HcloseVec $$ HnewBytes HnewLength
  ihave Hframe : ExportFrame heapId capacity dataPtr
      (initialized ++ current) (current ++ chunkTail) outputBytes $$
      [Hvec Hchunk Houtput]
  · unfold ExportFrame
    iframe
    ipureintro
    exact hframeLengths
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
  iapply twp_localGet rfl
  iapply twp_load32 ptr (by decide) (by decide) (by decide) (by decide) $$
    Hpointer
  iintro Hpointer
  iapply twp_localSet rfl
  simp only [List.length, List.set]
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat initialized.length)
      (by decide) (by decide) (by decide) (by decide) $$ Hlength
  iintro Hlength
  iapply twp_localSet rfl
  simp only [List.length, List.set]
  ihave Hframe : ExportFrame heapId capacity ptr initialized
      chunkBytes outputBytes $$
      [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
  · unfold ExportFrame VecU8 RawVecHeader
    iframe
    ipureintro
    exact hframeLengths
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
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_const
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
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsp]
  · iexact Hsp
  isplitl [Hreserve]
  · iexact Hreserve
  isplitl [Hvec]
  · iexact Hvec
  isplitl [Hbump]
  · iexact Hbump
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl []
  · ipureintro
    exact ⟨True.intro, True.intro, True.intro,
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
        ipureintro
        exact hframeLengths
      iapply Hcont $$ Hsp Hreserve Hframe Hbump Hstreams
  | success newPtr finish =>
      isimp only [hdecision] at Hcont
      isplit
      · iintro %finalHistory Hruntime Hsp Hreserve Hvec Hbump %hpure Hstreams
        ihave Hframe : ExportFrame heapId newCapacity newPtr initialized
            chunkBytes outputBytes $$ [Hvec Hchunk Houtput]
        · unfold ExportFrame
          iframe
          ipureintro
          exact hframeLengths
        ihave Hnormal := BI.and_elim_l $$ Hcont
        iapply Hnormal $$ %finalHistory Hruntime Hsp Hreserve Hframe Hbump
          %hpure Hstreams
      · iintro Hsp Hreserve Hvec Hbump Hstreams
        ihave Hframe : ExportFrame heapId capacity dataPtr initialized
            chunkBytes outputBytes $$ [Hvec Hchunk Houtput]
        · unfold ExportFrame
          iframe
          ipureintro
          exact hframeLengths
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
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_geU (result := 0)
    (by simp [UInt32.not_le.mpr hlt])
  iapply twp_brIfZero
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
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [Hframe]
  · iexact Hframe
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
    · ipureintro
      exact hempty
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
    · ipureintro
      exact ⟨hempty, hsplit.1, hcountPositive, hcountBound,
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
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hcapacity' : pointsTo_u32 0 (driverBase + 0) capacity $$ [Hcapacity]
  · simp only [UInt32.add_zero]
    iexact Hcapacity
  iapply twp_load32 (address := driverBase) (offset := 0) capacity
      (by decide) (by decide) (by decide) (by decide) $$ Hcapacity'
  iintro Hcapacity
  isimp only [UInt32.add_zero] at Hcapacity
  iapply twp_localGet rfl
  iapply twp_sub
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
      ipureintro
      exact hframeLengths
    have Happend := twp_func3_append_without_reserve heapId capacity dataPtr
      initialized current chunkTail outputBytes hfacts.2.1 hfits hlayout.1
      aux2 aux4 aux5 aux7 aux8 aux9 aux10
      (stack := stack) (code := code) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls)
      (s := s) (E := E) (Φ := Φ)
    simp only [func3AppendLocals, func3AppendBody] at Happend
    iapply Happend
    isplitl [Hframe]
    · iexact Hframe
    iintro Hframe
    have hgeo := GeometricVecFacts.appendWithoutReserve totalBytes
      initialized.length current.length remaining.length capacity dataPtr
      frontier history hfacts.2.2.2.2 hfacts.2.1 hfits
    ihave Hnormal := BI.and_elim_l $$ Hcont
    iapply Hnormal $$ %capacity %dataPtr %storedCursor %frontier %history
      %shadow Hruntime Hsp Hreserve Hframe Hbump Hstreams
    · ipureintro
      exact hgeo
  · iapply twp_leU (result := 0)
      (by
        have hfitsWord :
            ¬UInt32.ofNat current.length ≤
              capacity - UInt32.ofNat initialized.length := by
          rw [UInt32.le_iff_toNat_le_toNat, hcurrentWord, hspareWord]
          exact hfits
        simp [hfitsWord])
    iapply twp_brIfZero
    simp only [func3AppendLocals, List.drop_zero]
    ihave Hframe : ExportFrame heapId capacity dataPtr initialized
        (current ++ chunkTail) outputBytes $$
        [Hcapacity Hpointer Hlength Hstorage Hchunk Houtput]
    · unfold ExportFrame VecU8 RawVecHeader
      iframe
      ipureintro
      exact hframeLengths
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
    isplitl [Hruntime]
    · iexact Hruntime
    isplitl [Hsp]
    · iexact Hsp
    isplitl [Hreserve]
    · iexact Hreserve
    isplitl [Hframe]
    · iexact Hframe
    isplitl [Hbump]
    · iexact Hbump
    isplitl [Hstreams]
    · iexact Hstreams
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
          isplitl [Hframe]
          · iexact Hframe
          iintro Hframe
          iapply twp_exitControl (by rfl)
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
          isplitl [Hframe]
          · iexact Hframe
          iintro Hframe
          ihave Hnormal := BI.and_elim_l $$ Hcont
          iapply Hnormal $$
            %(UInt32.ofNat
              (selectedCapacity initialized.length current.length
                capacity.toNat)) %newPtr %finish %finish.toNat %finalHistory
            %(reserveSuccessShadow shadow newPtr
              (UInt32.ofNat
                (selectedCapacity initialized.length current.length
                  capacity.toNat))) Hruntime Hsp Hreserve Hframe Hbump Hstreams
          · ipureintro
            exact hpure.2
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
        ⌜GeometricVecFacts totalBytes
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
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsp]
  · iexact Hsp
  isplitl [Hreserve]
  · iexact Hreserve
  isplitl [Hframe]
  · iexact Hframe
  isplitl [Hbump]
  · iexact Hbump
  isplitl [Hstreams]
  · iexact Hstreams
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
    isplitl [Hruntime]
    · iexact Hruntime
    isplitl [Hstreams]
    · iexact Hstreams
    isplitl [Hframe]
    · iexact Hframe
    isplit
    · iintro Hruntime Hstreams Hframe %hremainingEmpty
      ihave HdonePair := BI.and_elim_l $$ Hcont
      ihave Hdone := BI.and_elim_l $$ HdonePair
      iapply Hdone $$ %finalCapacity %finalPtr %finalStoredCursor
        %finalFrontier %finalHistory %finalShadow Hruntime Hsp Hreserve Hframe
        Hbump Hstreams
      · ipureintro
        simpa [hremainingEmpty] using hgeo
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
      · ipureintro
        exact ⟨hreadShape, hnextPositive, hnextBound,
          hnextMod, hnext.2.2.2.2.2.1, htotalNext,
          hgeoNext, hmeasure⟩
  · iintro Hsp Hreserve Hframe Hbump Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    iapply Hoom $$ Hsp Hreserve Hframe Hbump Hstreams

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
  · isplitl [Hentry]
    · iexact Hentry
    · ipureintro
      exact hentryLength
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
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  rw [show entryStackTop - 272 = driverBase by decide]
  iapply twp_localTee rfl
  simp [Project.Mergesort.func3Def, Function.toLocals]
  iapply twp_globalSet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length_nil, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldLength (by decide) (by decide) (by decide)
      (by decide) $$ HoldLength'
  iintro Hlength
  iapply twp_localGet rfl
  iapply twp_pureStep _ _ _ (fun _ => Step.constI64)
  iapply twp_store64_zero (address := driverBase)
      (value := 4294967296)
      (oldCapacity.toUInt64 ||| (oldPointer.toUInt64 <<< 32))
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ HoldPair
  iintro Hpair
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show 12 + driverBase = driverBase + 12 by decide]
  iapply twp_const
  iapply twp_const
  isimp only [Project.Mergesort.Representations.ByteSlice] at Hchunk
  icases Hchunk with ⟨%hchunkNowrap, HchunkBytes⟩
  iapply twp_memoryFill32 chunkBytes (by
      simp [hframeParts.2.2.1]) (by decide) (by
      simpa [hframeParts.2.2.1, UInt32.size] using hchunkNowrap) $$
      HchunkBytes
  iintro HchunkBytes
  iapply twp_const
  iapply twp_localSet rfl
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
    isplitl [Hcapacity]
    · iexact Hcapacity
    isplitl [Hpointer]
    · iexact Hpointer
    isplitl [Hlength]
    · rw [show driverBase + 4 + 4 = driverBase + 8 by decide]
      iexact Hlength
    · itrivial
  ihave HheaderBytes : WordCells driverBase [0, 1, 0] $$ [Harray]
  · iapply (arrayAt_eq_wordCells driverBase [0, 1, 0]).mp
    iexact Harray
  ihave Hheader : Project.Mergesort.Representations.ByteSlice
      driverBase emptyVecHeaderBytes $$ [HheaderBytes]
  · unfold Project.Mergesort.Representations.ByteSlice emptyVecHeaderBytes
    isplitl []
    · ipureintro
      decide
    · iexact HheaderBytes
  ihave Hchunk : Project.Mergesort.Representations.ByteSlice
      (driverBase + 12) (List.replicate 256 0) $$ [HchunkBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    isplitl []
    · ipureintro
      simpa [hframeParts.2.2.1] using hchunkNowrap
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

end Project.Mergesort.DriverProof
