import Project.Mergesort.DriverProof
import Project.Mergesort.FormatProof
import Project.Mergesort.VecFromElemProof
import Project.Mergesort.VectorProof
import Project.Mergesort.SortFunctionProof

/-!
# Generated driver sort pipeline

This file isolates the middle of exported `func127`: reading the collected
vector length, constructing its zero-filled scratch vector, obtaining both
mutable slices, and calling the verified recursive sort at absolute index 128.

The allocator-backed success path of `Vec::from_elem` is deliberately exposed
as a linear contract at the exact generated `.call 107`.  This keeps the driver
proof composable without pretending that allocation succeeds; once the
allocator proof is available, it can discharge precisely that contract.
-/

namespace Project.Mergesort.DriverSortProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.DriverProof
open Project.Mergesort.VectorProof
open Project.Mergesort.SortFunctionProof
open Project.Mergesort.FormatProof
open Project.Mergesort.Pure
open Project.Mergesort.CoreProof

private theorem twp_constI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .constI64 value :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.constI64)

def driverAtVecLen : Program := func127.drop 98
def driverAtScratchCtor : Program := func127.drop 108
def driverAfterScratchCtor : Program := func127.drop 109
def driverAtInputDerefMut : Program := func127.drop 115
def driverAfterInputDerefMut : Program := func127.drop 116
def driverAtScratchDerefMut : Program := func127.drop 128
def driverAfterScratchDerefMut : Program := func127.drop 129
def driverAtSort : Program := func127.drop 137
def driverAfterSort : Program := func127.drop 138

def driverSortLenLocals (frame length : UInt32) : List Value :=
  (exportFramedLocals frame).set 7 (.i32 length)

def driverSortInputLocals
    (frame length inputLength inputData : UInt32) : List Value :=
  ((driverSortLenLocals frame length).set 8 (.i32 inputLength)).set 9
    (.i32 inputData)

def driverSortCallLocals
    (frame length inputLength inputData scratchLength : UInt32) : List Value :=
  (driverSortInputLocals frame length inputLength inputData).set 10
    (.i32 scratchLength)

theorem driverAtVecLen_eq :
    driverAtVecLen =
      [.localGet 0, .const 148, .add, .call 105, .localSet 7,
       .localGet 0, .const 240, .add, .constI64 0, .localGet 7] ++
        driverAtScratchCtor := by
  rfl

theorem driverAtScratchCtor_eq :
    driverAtScratchCtor = .call 107 :: driverAfterScratchCtor := by
  rfl

theorem driverAtInputDerefMut_eq :
    driverAtInputDerefMut = .call 124 :: driverAfterInputDerefMut := by
  rfl

theorem driverAtScratchDerefMut_eq :
    driverAtScratchDerefMut = .call 124 :: driverAfterScratchDerefMut := by
  rfl

theorem driverAtSort_eq :
    driverAtSort = .call 128 :: driverAfterSort := by
  rfl

theorem driverAfterScratchCtor_eq :
    driverAfterScratchCtor =
      [.localGet 0, .const 32, .add, .localGet 0, .const 148, .add] ++
        driverAtInputDerefMut := by
  rfl

theorem driverAfterInputDerefMut_eq :
    driverAfterInputDerefMut =
      [.localGet 0, .load32 36, .localSet 8,
       .localGet 0, .load32 32, .localSet 9,
       .localGet 0, .const 40, .add,
       .localGet 0, .const 240, .add] ++ driverAtScratchDerefMut := by
  rfl

theorem driverAfterScratchDerefMut_eq :
    driverAfterScratchDerefMut =
      [.localGet 0, .load32 44, .localSet 10,
       .localGet 9, .localGet 8, .localGet 0, .load32 40, .localGet 10] ++
        driverAtSort := by
  rfl

/-! The constructor boundary is useful independently of allocation: it proves
the exact generated `vecLen` call and argument preparation for `.call 107`. -/
theorem driver_vecLen_to_scratchCtor_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame length : UInt32)
    (hvecRoom : (148 + frame).toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 ((148 + frame) + 8) length ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 ((148 + frame) + 8) length -∗
        WP (.running
          ⟨⟨[], driverSortLenLocals frame length,
              [.i32 length, .i64 0, .i32 (240 + frame)]⟩,
            driverAtScratchCtor, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], exportFramedLocals frame, []⟩,
        driverAtVecLen, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hlength, Hdone⟩
  rw [driverAtVecLen_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  have Hlen := vecLen_call_twp (α := α) (148 + frame) length hvecRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[], exportFramedLocals frame, []⟩) (stack := [])
    (code := .localSet 7 :: .localGet 0 :: .const 240 :: .add ::
      .constI64 0 :: .localGet 7 :: driverAtScratchCtor)
    (arity := 0) (remainder := []) (controls := []) (calls := calls)
  iapply Hlen
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hlength]
  · iexact Hlength
  iintro Hruntime Hlength
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_constI64
  iapply twp_localGet rfl
  isimp [driverSortLenLocals, exportFramedLocals, exportZeroLocals] at Hdone
  isimp [driverSortLenLocals, exportFramedLocals, exportZeroLocals]
  iapply Hdone $$ Hruntime Hlength

/-! Exact constructor-return-to-sort pipeline.  The vector capacities and both
source descriptors are framed throughout; the two generated dereference calls
populate the temporary slice descriptors at frame offsets 32 and 40. -/
theorem driver_after_scratchCtor_to_sort_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame length inputCapacity dataPtr scratchCapacity scratchPtr : UInt32)
    (oldInputData oldInputLength oldScratchData oldScratchLength : UInt32)
    (input scratch : List UInt64)
    (hframeRoom : frame.toNat + 48 ≤ UInt32.size)
    (hinputVecRoom : (148 + frame).toNat + 12 ≤ UInt32.size)
    (hscratchVecRoom : (240 + frame).toNat + 12 ≤ UInt32.size)
    (hinputResultRoom : (32 + frame).toNat + 8 ≤ UInt32.size)
    (hscratchResultRoom : (40 + frame).toNat + 8 ≤ UInt32.size)
    (hinputLength : input.length = length.toNat)
    (hscratchLength : scratch.length = input.length)
    (hdataFit : dataPtr.toNat + 8 * input.length ≤ UInt32.size)
    (hscratchFit : scratchPtr.toNat + 8 * input.length ≤ UInt32.size)
    (hbytes : 8 * input.length < UInt32.size)
    (hsafe : 48 * (input.length + 2) ≤ frame.toNat)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      vecDescriptorAt (148 + frame) inputCapacity dataPtr length ∗
      vecDescriptorAt (240 + frame) scratchCapacity scratchPtr length ∗
      pointsTo_u32 ((32 + frame) + 0) oldInputData ∗
      pointsTo_u32 ((32 + frame) + 4) oldInputLength ∗
      pointsTo_u32 ((40 + frame) + 0) oldScratchData ∗
      pointsTo_u32 ((40 + frame) + 4) oldScratchLength ∗
      array64At dataPtr input ∗
      array64At scratchPtr scratch ∗
      SortWorkspace frame (input.length + 2) ∗
      (∀ (output scratchFinal : List UInt64),
        ⌜SortRel input output⌝ -∗
        ⌜SortPost input output⌝ -∗
        ⌜scratchFinal.length = input.length⌝ -∗
        runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        vecDescriptorAt (148 + frame) inputCapacity dataPtr length -∗
        vecDescriptorAt (240 + frame) scratchCapacity scratchPtr length -∗
        pointsTo_u32 ((32 + frame) + 0) dataPtr -∗
        pointsTo_u32 ((32 + frame) + 4) length -∗
        pointsTo_u32 ((40 + frame) + 0) scratchPtr -∗
        pointsTo_u32 ((40 + frame) + 4) length -∗
        array64At dataPtr output -∗
        array64At scratchPtr scratchFinal -∗
        SortWorkspace frame (input.length + 2) -∗
        WP (.running
          ⟨⟨[], driverSortCallLocals frame length length dataPtr length, []⟩,
            driverAfterSort, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], driverSortLenLocals frame length, []⟩,
        driverAfterScratchCtor, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h320, h321, h322, h323⟩ :=
    descriptorSlot32Facts frame 32 48 hframeRoom (by decide)
  obtain ⟨h360, h361, h362, h363⟩ :=
    descriptorSlot32Facts frame 36 48 hframeRoom (by decide)
  obtain ⟨h400, h401, h402, h403⟩ :=
    descriptorSlot32Facts frame 40 48 hframeRoom (by decide)
  obtain ⟨h440, h441, h442, h443⟩ :=
    descriptorSlot32Facts frame 44 48 hframeRoom (by decide)
  have hframe32 : frame + 32 = 32 + frame := by
    exact UInt32.add_comm frame 32
  have hframe36 : frame + 36 = (32 + frame) + 4 := by
    calc
      frame + 36 = frame + (32 + 4) := congrArg (fun x : UInt32 => frame + x)
        (by decide)
      _ = (frame + 32) + 4 := (UInt32.add_assoc frame 32 4).symm
      _ = (32 + frame) + 4 := congrArg (fun x : UInt32 => x + 4)
        (UInt32.add_comm frame 32)
  have hframe40 : frame + 40 = 40 + frame := by
    exact UInt32.add_comm frame 40
  have hframe44 : frame + 44 = (40 + frame) + 4 := by
    calc
      frame + 44 = frame + (40 + 4) := congrArg (fun x : UInt32 => frame + x)
        (by decide)
      _ = (frame + 40) + 4 := (UInt32.add_assoc frame 40 4).symm
      _ = (40 + frame) + 4 := congrArg (fun x : UInt32 => x + 4)
        (UInt32.add_comm frame 40)
  iintro ⟨Hruntime, Hglobal, HinputVec, HscratchVec,
    HinputResultData, HinputResultLength, HscratchResultData,
    HscratchResultLength, Hinput, Hscratch, Hworkspace, Hdone⟩
  isimp [vecDescriptorAt] at HinputVec
  isimp [vecDescriptorAt] at HscratchVec
  icases HinputVec with ⟨HinputCapacity, HinputData, HinputLength⟩
  icases HscratchVec with ⟨HscratchCapacity, HscratchData, HscratchLength⟩
  rw [driverAfterScratchCtor_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [driverAtInputDerefMut_eq]
  have HinputDeref := vecDerefMut_call_twp (α := α)
    (32 + frame) (148 + frame) dataPtr length oldInputData oldInputLength
    hinputVecRoom hinputResultRoom (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[], driverSortLenLocals frame length, []⟩)
    (stack := []) (code := driverAfterInputDerefMut) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
  simp only [List.append_nil] at HinputDeref
  iapply HinputDeref
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [HinputData]
  · iexact HinputData
  isplitl [HinputLength]
  · iexact HinputLength
  isplitl [HinputResultData]
  · iexact HinputResultData
  isplitl [HinputResultLength]
  · iexact HinputResultLength
  iintro Hruntime HinputData HinputLength HinputResultData HinputResultLength
  isimp [UInt32.add_zero] at HinputResultData
  rw [driverAfterInputDerefMut_eq]
  simp only [List.cons_append, List.nil_append]
  ihave HinputLengthAt : pointsTo_u32 (frame + 36) length $$
      [HinputResultLength]
  · rw [hframe36]
    iexact HinputResultLength
  ihave HinputDataAt : pointsTo_u32 (frame + 32) dataPtr $$
      [HinputResultData]
  · rw [hframe32]
    iexact HinputResultData
  iapply twp_localGet rfl
  iapply twp_load32 length h360 h361 h362 h363 $$ HinputLengthAt
  iintro HinputLengthAt
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 dataPtr h320 h321 h322 h323 $$ HinputDataAt
  iintro HinputDataAt
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [driverAtScratchDerefMut_eq]
  have HscratchDeref := vecDerefMut_call_twp (α := α)
    (40 + frame) (240 + frame) scratchPtr length
    oldScratchData oldScratchLength hscratchVecRoom hscratchResultRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[], driverSortInputLocals frame length length dataPtr, []⟩)
    (stack := []) (code := driverAfterScratchDerefMut) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
  simp only [driverSortInputLocals, List.append_nil] at HscratchDeref
  iapply HscratchDeref
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [HscratchData]
  · iexact HscratchData
  isplitl [HscratchLength]
  · iexact HscratchLength
  isplitl [HscratchResultData]
  · iexact HscratchResultData
  isplitl [HscratchResultLength]
  · iexact HscratchResultLength
  iintro Hruntime HscratchData HscratchLength HscratchResultData
    HscratchResultLength
  isimp [UInt32.add_zero] at HscratchResultData
  rw [driverAfterScratchDerefMut_eq]
  simp only [List.cons_append, List.nil_append]
  ihave HscratchLengthAt : pointsTo_u32 (frame + 44) length $$
      [HscratchResultLength]
  · rw [hframe44]
    iexact HscratchResultLength
  ihave HscratchDataAt : pointsTo_u32 (frame + 40) scratchPtr $$
      [HscratchResultData]
  · rw [hframe40]
    iexact HscratchResultData
  iapply twp_localGet rfl
  iapply twp_load32 length h440 h441 h442 h443 $$ HscratchLengthAt
  iintro HscratchLengthAt
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 scratchPtr h400 h401 h402 h403 $$ HscratchDataAt
  iintro HscratchDataAt
  iapply twp_localGet rfl
  rw [driverAtSort_eq]
  have Hsort := sort_call_twp (α := α)
    dataPtr length scratchPtr length frame input scratch hinputLength
    hscratchLength rfl hdataFit hscratchFit hbytes hsafe
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[], (((driverSortLenLocals frame length).set 8 (.i32 length)).set 9
        (.i32 dataPtr)).set 10 (.i32 length), []⟩)
    (stack := []) (code := driverAfterSort) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
  simp only [List.append_nil] at Hsort
  iapply Hsort
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinput]
  · iexact Hinput
  isplitl [Hscratch]
  · iexact Hscratch
  isplitl [Hworkspace]
  · iexact Hworkspace
  iintro %output %scratchFinal %HsortRel %HsortPost %HscratchFinalLength
    Hruntime Hglobal Hinput Hscratch Hworkspace
  isimp [driverSortCallLocals, driverSortInputLocals] at Hdone
  ihave HinputVecOut : vecDescriptorAt (148 + frame) inputCapacity dataPtr
      length $$ [HinputCapacity HinputData HinputLength]
  · isimp [vecDescriptorAt]
    isplitl [HinputCapacity]
    · iexact HinputCapacity
    isplitl [HinputData]
    · iexact HinputData
    iexact HinputLength
  ihave HscratchVecOut : vecDescriptorAt (240 + frame) scratchCapacity
      scratchPtr length $$ [HscratchCapacity HscratchData HscratchLength]
  · isimp [vecDescriptorAt]
    isplitl [HscratchCapacity]
    · iexact HscratchCapacity
    isplitl [HscratchData]
    · iexact HscratchData
    iexact HscratchLength
  ihave HinputResultDataOut : pointsTo_u32 (32 + frame) dataPtr $$
      [HinputDataAt]
  · rw [← hframe32]
    iexact HinputDataAt
  ihave HinputResultLengthOut : pointsTo_u32 ((32 + frame) + 4) length $$
      [HinputLengthAt]
  · rw [← hframe36]
    iexact HinputLengthAt
  ihave HscratchResultDataOut : pointsTo_u32 (40 + frame) scratchPtr $$
      [HscratchDataAt]
  · rw [← hframe40]
    iexact HscratchDataAt
  ihave HscratchResultLengthOut : pointsTo_u32 ((40 + frame) + 4) length $$
      [HscratchLengthAt]
  · rw [← hframe44]
    iexact HscratchLengthAt
  iapply Hdone $$ %output %scratchFinal %HsortRel %HsortPost
    %HscratchFinalLength Hruntime Hglobal HinputVecOut HscratchVecOut
    HinputResultDataOut HinputResultLengthOut HscratchResultDataOut
    HscratchResultLengthOut Hinput Hscratch Hworkspace

end Project.Mergesort.DriverSortProof
