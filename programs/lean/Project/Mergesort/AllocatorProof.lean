import Project.Mergesort.FormatProof
import Project.Mergesort.MemoryFillProof

/-!
# Generated allocator wrapper checkpoints

Successful-path contracts around the zeroed allocation chain used by
`Vec<u64>::from_elem`.  Fresh-region ownership is explicit and is threaded
unchanged by the wrapper code.  The remaining core boundary is local
`func143` (absolute index 145), whose implementation reaches dlmalloc.
-/

namespace Project.Mergesort.AllocatorProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.FormatProof
open Project.Mergesort.MemoryFillProof

def allocationPairAt [WasmHeapGS]
    (base data size : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 base data ∗ pointsTo_u32 (base + 4) size

private theorem pointsTo_u32_add_zero [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 base value ⊢ pointsTo_u32 (base + 0) value := by
  rw [UInt32.add_zero]

private theorem pointsTo_byte_add_zero [WasmHeapGS]
    (base : UInt32) (byte : UInt8) :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        base (DFrac.own 1) (some byte) ⊢
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (base + 0) (DFrac.own 1) (some byte) := by
  rw [UInt32.add_zero]

private theorem pointsTo_byte_zero_add [WasmHeapGS]
    (base : UInt32) (byte : UInt8) :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (base + 0) (DFrac.own 1) (some byte) ⊢
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        base (DFrac.own 1) (some byte) := by
  rw [UInt32.add_zero]

def zeroedAllocatorWrapperAfterCall : Program :=
  [.localGet 4, .load32 8, .localSet 6,
    .localGet 0, .localGet 4, .load32 12, .store32 4,
    .localGet 0, .localGet 6, .store32 0,
    .localGet 4, .const 16, .add, .globalSet 0, .ret]

/- Exact successful suffix of local `func145` after local `func143` has
returned the allocated pointer and byte size in the 16-byte wrapper frame. -/
set_option maxHeartbeats 2000000 in
theorem zeroedAllocatorWrapper_success_suffix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr metaPtr align size frame data : UInt32)
    (oldResultData oldResultSize : UInt32)
    (fresh : List UInt64)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      allocationPairAt (frame + 8) data size ∗
      allocationPairAt resultPtr oldResultData oldResultSize ∗
      array64At data fresh ∗
      (globalPointsTo 0 (.i32 (frame + 16)) -∗
        allocationPairAt (frame + 8) data size -∗
        allocationPairAt resultPtr data size -∗
        array64At data fresh -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 metaPtr, .i32 align, .i32 size],
              [.i32 frame, .i32 1, .i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 metaPtr, .i32 align, .i32 size],
          [.i32 frame, .i32 1, .i32 0], []⟩,
        zeroedAllocatorWrapperAfterCall, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 16 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 16 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    descriptorSlot32Facts resultPtr 0 8 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 8 hresultRoom (by decide)
  iintro ⟨Hglobal, Hframe, Hresult, Hfresh, Hdone⟩
  isimp only [allocationPairAt] at Hframe
  icases Hframe with ⟨Hf8, Hf12⟩
  isimp only [allocationPairAt] at Hresult
  icases Hresult with ⟨Hr0, Hr4⟩
  simp only [zeroedAllocatorWrapperAfterCall]
  iapply twp_localGet rfl
  iapply twp_load32 data hf80 hf81 hf82 hf83 $$ Hf8
  iintro Hf8
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hf12At : pointsTo_u32 (frame + 12) size $$ [Hf12]
  · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
    iexact Hf12
  iapply twp_load32 size hf120 hf121 hf122 hf123 $$ Hf12At
  iintro Hf12At
  iapply twp_store32 oldResultSize hr40 hr41 hr42 hr43 $$ Hr4
  iintro Hr4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hr0At : pointsTo_u32 (resultPtr + 0) oldResultData $$ [Hr0]
  · iapply pointsTo_u32_add_zero
    iexact Hr0
  iapply twp_store32 oldResultData hr0 hr1 hr2 hr3 $$ Hr0At
  iintro Hr0At
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (16 : UInt32) frame]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave Hr0 : pointsTo_u32 resultPtr data $$ [Hr0At]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact Hr0At
  ihave Hframe : allocationPairAt (frame + 8) data size $$ [Hf8 Hf12At]
  · isimp only [allocationPairAt]
    isplitl [Hf8]
    · iexact Hf8
    · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
      iexact Hf12At
  ihave Hresult : allocationPairAt resultPtr data size $$ [Hr0 Hr4]
  · isimp only [allocationPairAt]
    iframe
  iapply Hdone $$ Hglobal Hframe Hresult Hfresh

/- Exact pure/frame prefix of local `func145`, stopping at its absolute-index
145 call to local `func143`. -/
theorem zeroedAllocatorWrapper_to_core_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (resultPtr metaPtr align size stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗ R ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗ R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 metaPtr, .i32 align, .i32 size],
              [.i32 (stackTop - 16), .i32 1, .i32 0],
              [.i32 1, .i32 size, .i32 align,
                .i32 ((stackTop - 16) + 8)]⟩,
            .call 145 :: zeroedAllocatorWrapperAfterCall,
            0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 metaPtr, .i32 align, .i32 size],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func145, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, HR, Hdone⟩
  simp only [func145]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (8 : UInt32) (stackTop - 16)]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  isimp only [zeroedAllocatorWrapperAfterCall] at Hdone
  iapply Hdone $$ Hglobal HR

/- `func131` does not allocate by itself: it forwards the requested size and
alignment to local `func170` (absolute index 172).  Keeping this rule generic
makes the eventual dlmalloc contract the only place that must describe the
pre-owned region which is initialized by the allocator. -/
theorem allocatorForward_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align : UInt32)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 align], [], []⟩,
            func170, 1, [], [],
            { locals := ⟨[.i32 size, .i32 align], [], []⟩
              continuation := [.ret]
              resultArity := 1
              callerRemainder := []
              control := [] } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 align], [], []⟩,
        func131, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Himpl⟩
  simp only [func131]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_call (α := α) «module» 172 func170Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func170Def, Function.toLocals, Function.numParams]
  iapply Himpl $$ Hruntime

/- Absolute-index-133 call rule for the allocator forwarding shim, preserving
an arbitrary caller frame and arbitrary resources owned by its continuation. -/
theorem allocatorForward_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 align], [], []⟩,
            func170, 1, [], [],
            { locals := ⟨[.i32 size, .i32 align], [], []⟩
              continuation := [.ret]
              resultArity := 1
              callerRemainder := []
              control := [] } ::
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 align, .i32 size] ++ stack },
        .call 133 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Himpl⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 133 func131Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func131Def, Function.toLocals, Function.numParams]
  have Hbody := allocatorForward_body_twp (α := α)
    size align (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  iapply Himpl $$ Hruntime

def dlmallocFillBlockBody : Program :=
  [.localGet 1, .eqz, .br_if 0,
    .localGet 1, .const 4294967292, .add, .load8U 0,
    .const 3, .and, .eqz, .br_if 0,
    .localGet 0, .eqz, .br_if 0,
    .localGet 1, .const 0, .localGet 0, .memoryFill]

def dlmallocAfterSelect : Program :=
  [.block 0 0 dlmallocFillBlockBody, .localGet 1]

def dlmallocFillFrame (size data : UInt32) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := dlmallocFillBlockBody
    continuation := [.localGet 1]
    belowStack :=
      (⟨[.i32 size, .i32 data], [], []⟩ : Locals).values.drop 0 }

/- The final dlmalloc zeroing tail after its generated non-null/header/size
guards have succeeded.  This is the exact point where `memory.fill` consumes
the explicitly pre-owned allocation region and returns the data pointer. -/
theorem dlmalloc_zeroFill_tail_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size data : UInt32) (oldWord : UInt64) (oldWords : List UInt64)
    (hlength : size.toNat = 8 * (oldWord :: oldWords).length)
    (hroom : data.toNat + 8 * (oldWord :: oldWords).length ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    array64At data (oldWord :: oldWords) ∗
      (array64At data (List.replicate (oldWord :: oldWords).length 0) -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 data], [], [.i32 data]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 data], [], []⟩,
        [.localGet 1, .const 0, .localGet 0, .memoryFill],
        1, [], dlmallocFillFrame size data :: controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hdone⟩
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_memoryFill_zero_array64
      (s := s) (E := E) (Φ := Φ)
      (params := [.i32 size, .i32 data]) (localValues := []) (values := [])
      (destination := data) (length := size)
      (oldWord := oldWord) (oldWords := oldWords)
      (code := []) (arity := 1) (remainder := [])
      (controls := dlmallocFillFrame size data :: controls) (calls := calls)
      hlength hroom
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  iapply twp_exitControl rfl
  simp only [dlmallocFillFrame, List.drop_zero, List.take_zero,
    List.nil_append]
  iapply twp_localGet rfl
  iapply Hdone $$ Harray

/- The complete post-selection fill case of local `func170`.  A nonzero
header low-bit marker means the payload is not known zero, so the generated
code executes `memory.fill` over the owned interval. -/
theorem dlmalloc_afterSelect_fill_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size data : UInt32) (headerByte : UInt8)
    (oldWord : UInt64) (oldWords : List UInt64)
    (hdata : data ≠ 0) (hsize : size ≠ 0)
    (hneedsFill : (headerByte.toUInt32 &&& 3) ≠ 0)
    (hlength : size.toNat = 8 * (oldWord :: oldWords).length)
    (hroom : data.toNat + 8 * (oldWord :: oldWords).length ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (data + 4294967292) (DFrac.own 1) (some headerByte) ∗
      array64At data (oldWord :: oldWords) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1) (some headerByte) -∗
        array64At data (List.replicate (oldWord :: oldWords).length 0) -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 data], [], [.i32 data]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 data], [], []⟩,
        dlmallocAfterSelect, 1, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hheader, Harray, Hdone⟩
  simp only [dlmallocAfterSelect, dlmallocFillBlockBody]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_eqz (value := data) (result := 0) (by simp [hdata])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (4294967292 : UInt32) data]
  ihave Hheader0 : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      ((data + 4294967292) + 0) (DFrac.own 1) (some headerByte) $$ [Hheader]
  · iapply pointsTo_byte_add_zero
    iexact Hheader
  iapply twp_load8U_owned
      (s := s) (E := E) (Φ := Φ)
      (params := [.i32 size, .i32 data]) (localValues := []) (values := [])
      (address := data + 4294967292) (offset := 0)
      (code := [.const 3, .and, .eqz, .br_if 0,
        .localGet 0, .eqz, .br_if 0,
        .localGet 1, .const 0, .localGet 0, .memoryFill])
      (arity := 1) (remainder := [])
      (calls := calls)
      headerByte (by rw [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]) $$
      Hheader0
  iintro Hheader0
  ihave HheaderAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (data + 4294967292) (DFrac.own 1) (some headerByte) $$ [Hheader0]
  · iapply pointsTo_byte_zero_add
    iexact Hheader0
  iapply twp_const
  iapply twp_and
  iapply twp_eqz (value := headerByte.toUInt32 &&& 3) (result := 0)
      (by simp [hneedsFill])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_eqz (value := size) (result := 0) (by simp [hsize])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_memoryFill_zero_array64
      (s := s) (E := E) (Φ := Φ)
      (params := [.i32 size, .i32 data]) (localValues := []) (values := [])
      (destination := data) (length := size)
      (oldWord := oldWord) (oldWords := oldWords)
      (code := []) (arity := 1) (remainder := []) (calls := calls)
      hlength hroom
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  iapply twp_exitControl rfl
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply Hdone $$ HheaderAt Harray

/- Header low bits equal to zero means the underlying allocator already
returned zeroed storage.  The generated block skips `memory.fill`; this rule
therefore requires and preserves the zero-array ownership explicitly. -/
theorem dlmalloc_afterSelect_alreadyZero_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size data : UInt32) (headerByte : UInt8) (count : Nat)
    (hdata : data ≠ 0)
    (halreadyZero : headerByte.toUInt32 &&& 3 = 0)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (data + 4294967292) (DFrac.own 1) (some headerByte) ∗
      array64At data (List.replicate count 0) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1) (some headerByte) -∗
        array64At data (List.replicate count 0) -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 data], [], [.i32 data]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 data], [], []⟩,
        dlmallocAfterSelect, 1, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hheader, Harray, Hdone⟩
  simp only [dlmallocAfterSelect, dlmallocFillBlockBody]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_eqz (value := data) (result := 0) (by simp [hdata])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (4294967292 : UInt32) data]
  ihave Hheader0 : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      ((data + 4294967292) + 0) (DFrac.own 1) (some headerByte) $$ [Hheader]
  · iapply pointsTo_byte_add_zero
    iexact Hheader
  iapply twp_load8U_owned
      (s := s) (E := E) (Φ := Φ)
      (params := [.i32 size, .i32 data]) (localValues := []) (values := [])
      (address := data + 4294967292) (offset := 0)
      (code := [.const 3, .and, .eqz, .br_if 0,
        .localGet 0, .eqz, .br_if 0,
        .localGet 1, .const 0, .localGet 0, .memoryFill])
      (arity := 1) (remainder := [])
      (calls := calls)
      headerByte (by rw [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]) $$
      Hheader0
  iintro Hheader0
  ihave HheaderAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (data + 4294967292) (DFrac.own 1) (some headerByte) $$ [Hheader0]
  · iapply pointsTo_byte_zero_add
    iexact Hheader0
  iapply twp_const
  iapply twp_and
  rw [halreadyZero]
  iapply twp_eqz (value := 0) (result := 1) (by simp)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply Hdone $$ HheaderAt Harray

/- Result ownership supplied by the underlying allocator selectors.  The
header bit distinguishes payloads which are already known zero from payloads
which local `func170` must zero itself. -/
def dlmallocOwnedResult [WasmHeapGS]
    (data : UInt32) (headerByte : UInt8) (oldValues : List UInt64) :
    IProp WasmHeapGF :=
  iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (data + 4294967292) (DFrac.own 1) (some headerByte) ∗
    ((⌜headerByte.toUInt32 &&& 3 = 0⌝ ∗
        array64At data (List.replicate oldValues.length 0)) ∨
      (⌜headerByte.toUInt32 &&& 3 ≠ 0⌝ ∗ array64At data oldValues))

/- Complete post-selection contract, covering both generated header cases
without claiming that local `func170` created the payload ownership. -/
theorem dlmalloc_afterSelect_ownedResult_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size data : UInt32) (headerByte : UInt8)
    (oldWord : UInt64) (oldWords : List UInt64)
    (hdata : data ≠ 0) (hsize : size ≠ 0)
    (hlength : size.toNat = 8 * (oldWord :: oldWords).length)
    (hroom : data.toNat + 8 * (oldWord :: oldWords).length ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    dlmallocOwnedResult data headerByte (oldWord :: oldWords) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1) (some headerByte) -∗
        array64At data (List.replicate (oldWord :: oldWords).length 0) -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 data], [], [.i32 data]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 data], [], []⟩,
        dlmallocAfterSelect, 1, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hresult, Hdone⟩
  isimp only [dlmallocOwnedResult] at Hresult
  icases Hresult with ⟨Hheader, Hcase⟩
  icases Hcase with (Hzero | Hfill)
  · icases Hzero with ⟨%hzero, Harray⟩
    have Halready := dlmalloc_afterSelect_alreadyZero_twp (α := α)
      size data headerByte (oldWord :: oldWords).length hdata hzero
      (s := s) (E := E) (Φ := Φ) (controls := controls) (calls := calls)
    iapply Halready
    iframe
  · icases Hfill with ⟨%hfill, Harray⟩
    have Hneeds := dlmalloc_afterSelect_fill_twp (α := α)
      size data headerByte oldWord oldWords hdata hsize hfill hlength hroom
      (s := s) (E := E) (Φ := Φ) (controls := controls) (calls := calls)
    iapply Hneeds
    iframe

def dlmallocSelectInnerBody : Program :=
  [.localGet 1, .const 9, .ltU, .br_if 0,
    .localGet 1, .localGet 0, .call 163, .localSet 1, .br 1]

def dlmallocSelectOuterBody : Program :=
  [.block 0 0 dlmallocSelectInnerBody,
    .localGet 0, .call 164, .localSet 1]

def dlmallocSelectOuterFrame (size align : UInt32) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := dlmallocSelectOuterBody
    continuation := dlmallocAfterSelect
    belowStack := (⟨[.i32 size, .i32 align], [], []⟩ : Locals).values.drop 0 }

def dlmallocSelectInnerFrame (size align : UInt32) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := dlmallocSelectInnerBody
    continuation := [.localGet 0, .call 164, .localSet 1]
    belowStack := (⟨[.i32 size, .i32 align], [], []⟩ : Locals).values.drop 0 }

/- Large alignments enter local `func161` at absolute index 163.  The rule
exposes that exact callee state and call frame, allowing its eventual owned
allocation-result contract to be proved independently. -/
theorem dlmalloc_to_alignedAllocator_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align : UInt32) (halign : ¬ align < 9)
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨func161Def.toLocals [.i32 align, .i32 size],
            func161, 1, [], [],
            { locals := ⟨[.i32 size, .i32 align], [], []⟩
              continuation := [.localSet 1, .br 1]
              resultArity := 1
              callerRemainder := []
              control :=
                [dlmallocSelectInnerFrame size align,
                  dlmallocSelectOuterFrame size align] ++ controls } :: calls⟩ :
            Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 align], [], []⟩,
        func170, 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Himpl⟩
  simp only [func170]
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := 0) (by simp [halign])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_call (α := α) «module» 163 func161Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  isimp [func161Def, Function.toLocals, Function.numParams,
    dlmallocSelectInnerFrame, dlmallocSelectOuterFrame,
    dlmallocSelectInnerBody, dlmallocSelectOuterBody,
    dlmallocAfterSelect, dlmallocFillBlockBody] at Himpl
  simp [func161Def, Function.toLocals, Function.numParams]
  iapply Himpl $$ Hruntime

/- Small alignments exit the inner selector and enter local `func162` at
absolute index 164, again preserving the exact generated continuation. -/
theorem dlmalloc_to_smallAllocator_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align : UInt32) (halign : align < 9)
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨func162Def.toLocals [.i32 size],
            func162, 1, [], [],
            { locals := ⟨[.i32 size, .i32 align], [], []⟩
              continuation := [.localSet 1]
              resultArity := 1
              callerRemainder := []
              control := dlmallocSelectOuterFrame size align :: controls } ::
              calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 align], [], []⟩,
        func170, 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Himpl⟩
  simp only [func170]
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := 1) (by simp [halign])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_call (α := α) «module» 164 func162Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  isimp [func162Def, Function.toLocals, Function.numParams,
    dlmallocSelectOuterFrame, dlmallocSelectInnerBody,
    dlmallocSelectOuterBody, dlmallocAfterSelect, dlmallocFillBlockBody] at Himpl
  simp [func162Def, Function.toLocals, Function.numParams]
  iapply Himpl $$ Hruntime

def allocatorForwardFrame (size align : UInt32) : CallFrame :=
  { locals := ⟨[.i32 size, .i32 align], [], []⟩
    continuation := [.ret]
    resultArity := 1
    callerRemainder := []
    control := [] }

/- Composition used by the scratch constructor: local `func131` forwards
`(size, 8)` to local `func170`, whose small-alignment selector enters
local `func162`. -/
theorem allocatorForward_to_smallAllocator_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align : UInt32) (halign : align < 9)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨func162Def.toLocals [.i32 size],
            func162, 1, [], [],
            { locals := ⟨[.i32 size, .i32 align], [], []⟩
              continuation := [.localSet 1]
              resultArity := 1
              callerRemainder := []
              control := [dlmallocSelectOuterFrame size align] } ::
            allocatorForwardFrame size align :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 align], [], []⟩,
        func131, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Himpl⟩
  have Hforward := allocatorForward_body_twp (α := α)
    size align (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hforward
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  have Hselect := dlmalloc_to_smallAllocator_twp (α := α)
    size align halign (s := s) (E := E) (Φ := Φ)
    (controls := [])
    (calls :=
      { locals := ⟨[.i32 size, .i32 align], [], []⟩
        continuation := [.ret]
        resultArity := 1
        callerRemainder := []
        control := [] } :: calls)
  iapply Hselect
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  isimp only [allocatorForwardFrame] at Himpl
  iapply Himpl $$ Hruntime

/- The first six instructions of local `func162` reserve its 16-byte stack
frame.  Naming the exact residual program and locals keeps the large allocator
body opaque to its callers while it is proved in smaller pieces. -/
def smallAllocatorAfterFrame : Program := func162.drop 6

def smallAllocatorFrameLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i64 0]

private theorem func162_take_frame_prefix :
    func162.take 6 =
      [.globalGet 0, .const (16 : UInt32), .sub, .localSet 1,
        .localGet 1, .globalSet 0] := by
  rfl

/- Exact entry rule for local `func162`.  The candidate block's header and
payload are deliberately supplied by the caller and merely framed across this
pure stack-frame prefix: this rule does not mint memory ownership. -/
theorem smallAllocator_owned_frame_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size stackTop data : UInt32) (headerByte : UInt8)
    (oldValues : List UInt64)
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      dlmallocOwnedResult data headerByte oldValues ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        dlmallocOwnedResult data headerByte oldValues -∗
        WP (.running
          ⟨⟨[.i32 size], smallAllocatorFrameLocals (stackTop - 16), []⟩,
            smallAllocatorAfterFrame, 1, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size], smallAllocatorFrameLocals 0, []⟩,
        func162, 1, [], controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Howned, Hdone⟩
  rw [← List.take_append_drop 6 func162, func162_take_frame_prefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [smallAllocatorFrameLocals, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  isimp only [smallAllocatorAfterFrame] at Hdone
  iapply Hdone $$ Hglobal Howned

/- The same prefix rule at the exact callee state produced by absolute-index
164 calls.  Keeping this corollary separate avoids exposing the generated
function's zero-local expansion at every composition site. -/
theorem smallAllocator_owned_entry_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size stackTop data : UInt32) (headerByte : UInt8)
    (oldValues : List UInt64)
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      dlmallocOwnedResult data headerByte oldValues ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        dlmallocOwnedResult data headerByte oldValues -∗
        WP (.running
          ⟨⟨[.i32 size], smallAllocatorFrameLocals (stackTop - 16), []⟩,
            smallAllocatorAfterFrame, 1, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨func162Def.toLocals [.i32 size], func162, 1, [], controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  have Hprefix := smallAllocator_owned_frame_prefix_twp (α := α)
    size stackTop data headerByte oldValues
    (s := s) (E := E) (Φ := Φ) (controls := controls) (calls := calls)
  simpa only [func162Def, Function.toLocals, Function.numParams,
    smallAllocatorFrameLocals, List.map, ValueType.zero] using Hprefix

end Project.Mergesort.AllocatorProof
