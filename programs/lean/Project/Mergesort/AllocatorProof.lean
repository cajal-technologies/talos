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
open Project.Mergesort.SplitAtProof

def allocationPairAt [WasmHeapGS]
    (base data size : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 base data ∗ pointsTo_u32 (base + 4) size

private theorem pointsTo_u32_add_zero [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 base value ⊢ pointsTo_u32 (base + 0) value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u32_zero_add [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 (base + 0) value ⊢ pointsTo_u32 base value := by
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

private def firstBlockBody : Program → Program
  | .block _ _ body :: _ => body
  | _ => []

private def afterFirstInstruction (code : Program) : Program := code.drop 1

def smallAllocatorOuterBody : Program := firstBlockBody smallAllocatorAfterFrame
def smallAllocatorAfterOuter : Program :=
  afterFirstInstruction smallAllocatorAfterFrame
def smallAllocatorSecondBody : Program := firstBlockBody smallAllocatorOuterBody
def smallAllocatorAfterSecond : Program :=
  afterFirstInstruction smallAllocatorOuterBody
def smallAllocatorThirdBody : Program := firstBlockBody smallAllocatorSecondBody
def smallAllocatorAfterThird : Program :=
  afterFirstInstruction smallAllocatorSecondBody
def smallAllocatorClassifierBody : Program :=
  firstBlockBody smallAllocatorThirdBody
def smallAllocatorSmallPath : Program :=
  afterFirstInstruction smallAllocatorThirdBody

def smallAllocatorBlockFrame (body continuation : Program) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := body
    continuation := continuation
    belowStack := [] }

private theorem smallAllocator_afterFrame_shape :
    smallAllocatorAfterFrame =
      .block 0 0 smallAllocatorOuterBody :: smallAllocatorAfterOuter := by
  rfl

private theorem smallAllocator_epilogue_program :
    smallAllocatorAfterOuter =
      [.localGet 1, .const (16 : UInt32), .add, .globalSet 0,
        .localGet 0] := by
  rfl

/- Restore local `func162`'s 16-byte stack frame and leave its selected data
pointer on the operand stack. -/
theorem smallAllocator_epilogue_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (data frame : UInt32) (rest : List Value) (R : IProp WasmHeapGF)
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗ R ∗
      (globalPointsTo 0 (.i32 (frame + 16)) -∗ R -∗
        WP (.running
          ⟨⟨[.i32 data], .i32 frame :: rest, [.i32 data]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 data], .i32 frame :: rest, []⟩,
        smallAllocatorAfterOuter, 1, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, HR, Hdone⟩
  rw [smallAllocator_epilogue_program]
  iapply twp_localGet (value := .i32 frame) (by simp [Locals.get])
  iapply twp_const
  iapply twp_add
  rw [show (16 : UInt32) + frame = frame + 16 by bv_decide]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply Hdone $$ Hglobal HR

private theorem smallAllocator_outer_shape :
    smallAllocatorOuterBody =
      .block 0 0 smallAllocatorSecondBody :: smallAllocatorAfterSecond := by
  rfl

private theorem smallAllocator_second_shape :
    smallAllocatorSecondBody =
      .block 0 0 smallAllocatorThirdBody :: smallAllocatorAfterThird := by
  rfl

private theorem smallAllocator_third_shape :
    smallAllocatorThirdBody =
      .block 0 0 smallAllocatorClassifierBody :: smallAllocatorSmallPath := by
  rfl

private theorem smallAllocator_classifier_prefix :
    smallAllocatorClassifierBody.take 4 =
      [.localGet 0, .const (245 : UInt32), .ltU, .br_if 0] := by
  rfl

/- The first exact size-class decision in local `func162`: requests below 245
bytes leave the large-bin classifier and enter the generated small-bin tree.
The pre-owned candidate block is preserved unchanged across this pure branch. -/
theorem smallAllocator_to_smallBinTree_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame data : UInt32) (headerByte : UInt8)
    (oldValues : List UInt64) (hsmall : size < 245)
    {controls : List ControlFrame} {calls : List CallFrame} :
    dlmallocOwnedResult data headerByte oldValues ∗
      (dlmallocOwnedResult data headerByte oldValues -∗
        WP (.running
          ⟨⟨[.i32 size], smallAllocatorFrameLocals frame, []⟩,
            smallAllocatorSmallPath, 1, [],
            [smallAllocatorBlockFrame smallAllocatorThirdBody
                smallAllocatorAfterThird,
              smallAllocatorBlockFrame smallAllocatorSecondBody
                smallAllocatorAfterSecond,
              smallAllocatorBlockFrame smallAllocatorOuterBody
                smallAllocatorAfterOuter] ++ controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size], smallAllocatorFrameLocals frame, []⟩,
        smallAllocatorAfterFrame, 1, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Howned, Hdone⟩
  rw [smallAllocator_afterFrame_shape]
  iapply twp_block
  rw [smallAllocator_outer_shape]
  iapply twp_block
  rw [smallAllocator_second_shape]
  iapply twp_block
  rw [smallAllocator_third_shape]
  iapply twp_block
  rw [← List.take_append_drop 4 smallAllocatorClassifierBody,
    smallAllocator_classifier_prefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := 1) (by simp [hsmall])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  isimp only [smallAllocatorBlockFrame] at Hdone
  iapply Hdone $$ Howned

def smallAllocatorBinLevel1Body : Program :=
  firstBlockBody smallAllocatorSmallPath
def smallAllocatorAfterBinLevel1 : Program :=
  afterFirstInstruction smallAllocatorSmallPath
def smallAllocatorBinLevel2Body : Program :=
  firstBlockBody smallAllocatorBinLevel1Body
def smallAllocatorAfterBinLevel2 : Program :=
  afterFirstInstruction smallAllocatorBinLevel1Body
def smallAllocatorBinLevel3Body : Program :=
  firstBlockBody smallAllocatorBinLevel2Body
def smallAllocatorAfterBinLevel3 : Program :=
  afterFirstInstruction smallAllocatorBinLevel2Body
def smallAllocatorBinLevel4Body : Program :=
  firstBlockBody smallAllocatorBinLevel3Body
def smallAllocatorAfterBinLevel4 : Program :=
  afterFirstInstruction smallAllocatorBinLevel3Body
def smallAllocatorBinLevel5Body : Program :=
  firstBlockBody smallAllocatorBinLevel4Body
def smallAllocatorAfterBinLevel5 : Program :=
  afterFirstInstruction smallAllocatorBinLevel4Body
def smallAllocatorBinSelectorBody : Program :=
  firstBlockBody smallAllocatorBinLevel5Body
def smallAllocatorAfterBinSelector : Program :=
  afterFirstInstruction smallAllocatorBinLevel5Body

private theorem smallAllocator_smallPath_shape :
    smallAllocatorSmallPath =
      .block 0 0 smallAllocatorBinLevel1Body ::
        smallAllocatorAfterBinLevel1 := by
  rfl

private theorem smallAllocator_binLevel1_shape :
    smallAllocatorBinLevel1Body =
      .block 0 0 smallAllocatorBinLevel2Body ::
        smallAllocatorAfterBinLevel2 := by
  rfl

private theorem smallAllocator_binLevel2_shape :
    smallAllocatorBinLevel2Body =
      .block 0 0 smallAllocatorBinLevel3Body ::
        smallAllocatorAfterBinLevel3 := by
  rfl

private theorem smallAllocator_binLevel3_shape :
    smallAllocatorBinLevel3Body =
      .block 0 0 smallAllocatorBinLevel4Body ::
        smallAllocatorAfterBinLevel4 := by
  rfl

private theorem smallAllocator_binLevel4_shape :
    smallAllocatorBinLevel4Body =
      .block 0 0 smallAllocatorBinLevel5Body ::
        smallAllocatorAfterBinLevel5 := by
  rfl

private theorem smallAllocator_binLevel5_shape :
    smallAllocatorBinLevel5Body =
      .block 0 0 smallAllocatorBinSelectorBody ::
        smallAllocatorAfterBinSelector := by
  rfl

def smallAllocatorOuterControls : List ControlFrame :=
  [smallAllocatorBlockFrame smallAllocatorThirdBody smallAllocatorAfterThird,
    smallAllocatorBlockFrame smallAllocatorSecondBody smallAllocatorAfterSecond,
    smallAllocatorBlockFrame smallAllocatorOuterBody smallAllocatorAfterOuter]

def smallAllocatorBinControls : List ControlFrame :=
  [smallAllocatorBlockFrame smallAllocatorBinSelectorBody
      smallAllocatorAfterBinSelector,
    smallAllocatorBlockFrame smallAllocatorBinLevel5Body
      smallAllocatorAfterBinLevel5,
    smallAllocatorBlockFrame smallAllocatorBinLevel4Body
      smallAllocatorAfterBinLevel4,
    smallAllocatorBlockFrame smallAllocatorBinLevel3Body
      smallAllocatorAfterBinLevel3,
    smallAllocatorBlockFrame smallAllocatorBinLevel2Body
      smallAllocatorAfterBinLevel2,
    smallAllocatorBlockFrame smallAllocatorBinLevel1Body
      smallAllocatorAfterBinLevel1]

/- Enter the six generated small-bin control blocks without changing locals or
heap ownership.  The following theorem can therefore focus solely on the
selector's metadata loads and branch conditions. -/
theorem smallAllocator_enter_smallBinSelector_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF) (size frame : UInt32)
    {controls : List ControlFrame} {calls : List CallFrame} :
    R ∗
      (R -∗
        WP (.running
          ⟨⟨[.i32 size], smallAllocatorFrameLocals frame, []⟩,
            smallAllocatorBinSelectorBody, 1, [],
            smallAllocatorBinControls ++ smallAllocatorOuterControls ++ controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size], smallAllocatorFrameLocals frame, []⟩,
        smallAllocatorSmallPath, 1, [],
        smallAllocatorOuterControls ++ controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨HR, Hdone⟩
  rw [smallAllocator_smallPath_shape]
  iapply twp_block
  rw [smallAllocator_binLevel1_shape]
  iapply twp_block
  rw [smallAllocator_binLevel2_shape]
  iapply twp_block
  rw [smallAllocator_binLevel3_shape]
  iapply twp_block
  rw [smallAllocator_binLevel4_shape]
  iapply twp_block
  rw [smallAllocator_binLevel5_shape]
  iapply twp_block
  simp only [List.drop_zero, ← smallAllocator_binLevel5_shape,
    ← smallAllocator_binLevel4_shape, ← smallAllocator_binLevel3_shape,
    ← smallAllocator_binLevel2_shape, ← smallAllocator_binLevel1_shape]
  isimp only [smallAllocatorBinControls, smallAllocatorBlockFrame,
    List.append_assoc, List.cons_append, List.nil_append] at Hdone
  iapply Hdone $$ HR

def smallAllocatorChunkSize (size : UInt32) : UInt32 :=
  if size < 11 then 16 else (11 + size) &&& 504

def smallAllocatorTinyFlag (size : UInt32) : UInt32 :=
  if size < 11 then 1 else 0

def smallAllocatorBinIndex (size : UInt32) : UInt32 :=
  smallAllocatorChunkSize size >>> 3

def smallAllocatorShiftedMap (size smallMap : UInt32) : UInt32 :=
  smallMap >>> (smallAllocatorBinIndex size % 32)

def smallAllocatorAfterAvailability : Program :=
  smallAllocatorBinSelectorBody.drop 27

private theorem smallAllocator_selector_availability_prefix :
    smallAllocatorBinSelectorBody.take 27 =
      [.const (0 : UInt32), .load32 (1056608 : UInt32), .localSet 6,
        .localGet 6, .const (16 : UInt32), .localGet 0,
        .const (11 : UInt32), .add, .const (504 : UInt32), .and,
        .localGet 0, .const (11 : UInt32), .ltU, .select, .localSet 3,
        .localGet 3, .const (3 : UInt32), .shrU, .localSet 2,
        .localGet 2, .shrU, .localSet 0, .localGet 0,
        .const (3 : UInt32), .and, .eqz, .br_if 0] := by
  rfl

private theorem twp_select_i32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {condition first second selected : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hselected : selected = if condition ≠ 0 then first else second) :
    WP (.running
      ⟨⟨params, localValues, .i32 selected :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 condition :: .i32 second :: .i32 first :: values⟩,
        .select :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.select (by
    rw [hselected]
    by_cases hzero : condition = 0 <;> simp [hzero]))

private theorem twp_xor_i32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs ^^^ rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .xor :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.xor)

def smallAllocatorRotateLeft (value count : UInt32) : UInt32 :=
  let count := count % 32
  if count = 0 then value
  else (value <<< count) ||| (value >>> (32 - count))

private theorem twp_eq_i32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .eq :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.eq hresult)

private theorem twp_returnFromCallFallthrough
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {calleeLocals callerLocals : Locals} {calleeArity callerArity : Nat}
    {calleeRemainder callerRemainder : List Value}
    {callerCode : Program} {callerControls : List ControlFrame}
    {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := callerLocals
        continuation := callerCode
        resultArity := callerArity
        callerRemainder := callerRemainder
        control := callerControls }
    WP (.running
      ⟨{ callerLocals with
          values := calleeLocals.values.take calleeArity ++ callerLocals.values },
        callerCode, callerArity, callerRemainder, callerControls, calls⟩ :
        Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨calleeLocals, [], calleeArity, calleeRemainder, [], caller :: calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.returnFromCallFallthrough)

private theorem twp_rotl_i32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues,
          .i32 (smallAllocatorRotateLeft lhs rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .rotl :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.rotl)

/- Successful small-map availability decision.  This exact prefix reads the
allocator's small-bin bitmap and reaches the selected-bin arithmetic only when
one of the requested bin or its successor is populated.  Candidate payload
ownership is framed and the bitmap cell remains owned by the continuation. -/
theorem smallAllocator_smallBin_available_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap : UInt32)
    (havailable : smallAllocatorShiftedMap size smallMap &&& 3 ≠ 0)
    (R : IProp WasmHeapGF)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 1056608 smallMap ∗ R ∗
      (pointsTo_u32 1056608 smallMap -∗ R -∗
        WP (.running
          ⟨⟨[.i32 (smallAllocatorShiftedMap size smallMap)],
              [.i32 frame, .i32 (smallAllocatorBinIndex size),
                .i32 (smallAllocatorChunkSize size), .i32 0, .i32 0,
                .i32 smallMap, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
            smallAllocatorAfterAvailability, 1, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size], smallAllocatorFrameLocals frame, []⟩,
        smallAllocatorBinSelectorBody, 1, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hm0, hm1, hm2, hm3⟩ :=
    descriptorSlot32Facts 0 1056608 1056612 (by decide) (by decide)
  iintro ⟨Hmap, HR, Hdone⟩
  rw [← List.take_append_drop 27 smallAllocatorBinSelectorBody,
    smallAllocator_selector_availability_prefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_const
  ihave HmapAt : pointsTo_u32 (0 + UInt32.ofNat 1056608) smallMap $$ [Hmap]
  · rw [show 0 + UInt32.ofNat 1056608 = 1056608 by decide]
    iexact Hmap
  iapply twp_load32 smallMap hm0 hm1 hm2 hm3 $$ HmapAt
  iintro HmapAt
  ihave Hmap : pointsTo_u32 1056608 smallMap $$ [HmapAt]
  · rw [← show 0 + UInt32.ofNat 1056608 = 1056608 by decide]
    iexact HmapAt
  iapply twp_localSet rfl
  simp only [smallAllocatorFrameLocals, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_const
  iapply twp_and
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := smallAllocatorTinyFlag size)
    (by simp [smallAllocatorTinyFlag])
  iapply twp_select_i32 (selected := smallAllocatorChunkSize size)
    (by simp [smallAllocatorChunkSize, smallAllocatorTinyFlag])
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shrU
  iapply twp_localSet rfl
  simp only [smallAllocatorBinIndex, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_shrU
  iapply twp_localSet rfl
  simp only [smallAllocatorShiftedMap, List.set]
  simp only [show (3 : UInt32) % 32 = 3 by decide]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  iapply twp_eqz (result := 0)
    (by simpa [smallAllocatorShiftedMap, smallAllocatorBinIndex] using havailable)
  iapply twp_brIfZero
  simp only [smallAllocatorBinIndex]
  isimp only [smallAllocatorAfterAvailability] at Hdone
  iapply Hdone $$ Hmap HR

def smallBinPayloadAt [WasmHeapGS]
    (data next previous : UInt32) (tail : List UInt64) : IProp WasmHeapGF :=
  iprop% sliceDescriptorAt data next previous ∗ array64At (data + 8) tail

def headerWordTailAt [WasmHeapGS]
    (address value : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (address + 1) (DFrac.own 1) (some (u32Byte value 1)) ∗
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (address + 2) (DFrac.own 1) (some (u32Byte value 2)) ∗
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (address + 3) (DFrac.own 1) (some (u32Byte value 3))

theorem pointsTo_u32_eq_headerByteTail [WasmHeapGS]
    (address value : UInt32) :
    pointsTo_u32 address value ⊣⊢
      (iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) (some (u32Byte value 0)) ∗
        headerWordTailAt address value) := by
  simp only [pointsTo_u32, headerWordTailAt]
  constructor <;> iintro ⟨H0, H1, H2, H3⟩ <;> iframe

theorem smallBinPayloadAt_eq_array64 [WasmHeapGS]
    (data next previous : UInt32) (tail : List UInt64) :
    smallBinPayloadAt data next previous tail ⊣⊢
      array64At data (packU32 next previous :: tail) := by
  simp only [smallBinPayloadAt, array64At]
  exact BI.sep_congr_left (sliceDescriptorAt_eq_u64 data next previous)

theorem dlmallocOwnedResult_nonzero_eq_smallBin
    [WasmSmallStepGS hlc]
    (data : UInt32) (headerByte : UInt8) (next previous : UInt32)
    (tail : List UInt64)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0) :
    dlmallocOwnedResult data headerByte
        (packU32 next previous :: tail) ⊣⊢
      (iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1) (some headerByte) ∗
        smallBinPayloadAt data next previous tail) := by
  constructor
  · iintro Hresult
    isimp only [dlmallocOwnedResult] at Hresult
    icases Hresult with ⟨Hheader, Hcase⟩
    icases Hcase with (Hzero | Hnonzero)
    · icases Hzero with ⟨%hzero, Harray⟩
      exact (hnonzero hzero).elim
    · icases Hnonzero with ⟨%_, Harray⟩
      ihave Hpayload : smallBinPayloadAt data next previous tail $$ [Harray]
      · iapply (smallBinPayloadAt_eq_array64 data next previous tail).mpr
        iexact Harray
      iframe
  · iintro ⟨Hheader, Hpayload⟩
    ihave Harray : array64At data (packU32 next previous :: tail) $$ [Hpayload]
    · iapply (smallBinPayloadAt_eq_array64 data next previous tail).mp
      iexact Hpayload
    isimp only [dlmallocOwnedResult]
    isplitl [Hheader]
    · iexact Hheader
    iright
    isplit
    · ipureintro
      exact hnonzero
    · iexact Harray

theorem dlmallocOwnedResult_nonzero_eq_payload
    [WasmSmallStepGS hlc]
    (data : UInt32) (headerByte : UInt8) (oldValues : List UInt64)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0) :
    dlmallocOwnedResult data headerByte oldValues ⊣⊢
      (iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1) (some headerByte) ∗
        array64At data oldValues) := by
  constructor
  · iintro Hresult
    isimp only [dlmallocOwnedResult] at Hresult
    icases Hresult with ⟨Hheader, Hcase⟩
    icases Hcase with (Hzero | Hnonzero)
    · icases Hzero with ⟨%hzero, Harray⟩
      exact (hnonzero hzero).elim
    · icases Hnonzero with ⟨%_, Harray⟩
      iframe
  · iintro ⟨Hheader, Harray⟩
    isimp only [dlmallocOwnedResult]
    isplitl [Hheader]
    · iexact Hheader
    iright
    isplit
    · ipureintro
      exact hnonzero
    · iexact Harray

def smallAllocatorSelectedBin (size smallMap : UInt32) : UInt32 :=
  smallAllocatorBinIndex size +
    ((smallAllocatorShiftedMap size smallMap ^^^ 4294967295) &&& 1)

def smallAllocatorSelectedSize (size smallMap : UInt32) : UInt32 :=
  smallAllocatorSelectedBin size smallMap <<< (3 % 32)

def smallAllocatorBinSentinel (size smallMap : UInt32) : UInt32 :=
  1056344 + smallAllocatorSelectedSize size smallMap

def smallAllocatorBinHeadAddress (size smallMap : UInt32) : UInt32 :=
  1056352 + smallAllocatorSelectedSize size smallMap

def smallAllocatorClearedSmallMap (size smallMap : UInt32) : UInt32 :=
  smallMap &&&
    smallAllocatorRotateLeft 4294967294
      (smallAllocatorSelectedBin size smallMap)

def smallAllocatorAllocatedHeader (size smallMap : UInt32) : UInt32 :=
  smallAllocatorSelectedSize size smallMap ||| 3

def smallAllocatorNextChunk
    (size smallMap chunk : UInt32) : UInt32 :=
  chunk + smallAllocatorSelectedSize size smallMap

def smallAllocatorAfterSingleBinChoice : Program :=
  smallAllocatorAfterAvailability.drop 28

private theorem smallAllocator_multiBinUnlink_prefix :
    smallAllocatorAfterSingleBinChoice.take 7 =
      [.localGet 8, .localGet 0, .store32 (12 : UInt32),
        .localGet 0, .localGet 8, .store32 (8 : UInt32), .br 2] := by
  rfl

private theorem smallAllocator_singleBinBitmapClear_prefix :
    smallAllocatorAfterBinLevel5.take 7 =
      [.const (0 : UInt32), .localGet 6, .const (4294967294 : UInt32),
        .localGet 7, .rotl, .and, .store32 (1056608 : UInt32)] := by
  rfl

private theorem smallAllocator_commonAllocation_prefix :
    smallAllocatorAfterBinLevel4.take 20 =
      [.localGet 2, .const (8 : UInt32), .add, .localSet 0,
        .localGet 2, .localGet 3, .const (3 : UInt32), .or,
        .store32 (4 : UInt32),
        .localGet 2, .localGet 3, .add, .localSet 3,
        .localGet 3, .localGet 3, .load32 (4 : UInt32),
        .const (1 : UInt32), .or, .store32 (4 : UInt32), .br 5] := by
  rfl

private theorem smallAllocator_singleBinChoice_prefix :
    smallAllocatorAfterAvailability.take 28 =
      [.localGet 0, .const (4294967295 : UInt32), .xor,
        .const (1 : UInt32), .and, .localGet 2, .add, .localSet 7,
        .localGet 7, .const (3 : UInt32), .shl, .localSet 3,
        .localGet 3, .const (1056344 : UInt32), .add, .localSet 0,
        .localGet 0, .localGet 3, .const (1056352 : UInt32), .add,
        .load32 (0 : UInt32), .localSet 2,
        .localGet 2, .load32 (8 : UInt32), .localSet 8,
        .localGet 8, .eq, .br_if 1] := by
  rfl

def smallAllocatorAfterSingleBinControls : List ControlFrame :=
  smallAllocatorBinControls.drop 2

/- Exact successful single-entry small-bin selection.  The free-list `next`
word is obtained by decomposing the first owned payload `u64`, loaded without
mutation, and reassembled before the continuation. -/
theorem smallAllocator_singleBinChoice_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap chunk previous data : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hdata : data = chunk + 8)
    (hheadRoom : (smallAllocatorBinHeadAddress size smallMap).toNat + 4 ≤
      UInt32.size)
    (hchunkRoom : chunk.toNat + 12 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      (pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk -∗
        dlmallocOwnedResult data headerByte
          (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) -∗
        WP (.running
          ⟨⟨[.i32 (smallAllocatorBinSentinel size smallMap)],
              [.i32 frame, .i32 chunk,
                .i32 (smallAllocatorSelectedSize size smallMap),
                .i32 0, .i32 0, .i32 smallMap,
                .i32 (smallAllocatorSelectedBin size smallMap),
                .i32 (smallAllocatorBinSentinel size smallMap),
                .i32 0, .i64 0], []⟩,
            smallAllocatorAfterBinLevel5, 1, [],
            List.append
              [smallAllocatorBlockFrame smallAllocatorBinLevel4Body
                  smallAllocatorAfterBinLevel4,
                smallAllocatorBlockFrame smallAllocatorBinLevel3Body
                  smallAllocatorAfterBinLevel3,
                smallAllocatorBlockFrame smallAllocatorBinLevel2Body
                  smallAllocatorAfterBinLevel2,
                smallAllocatorBlockFrame smallAllocatorBinLevel1Body
                  smallAllocatorAfterBinLevel1]
              controls,
            calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (smallAllocatorShiftedMap size smallMap)],
          [.i32 frame, .i32 (smallAllocatorBinIndex size),
            .i32 (smallAllocatorChunkSize size), .i32 0, .i32 0,
            .i32 smallMap, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
        smallAllocatorAfterAvailability, 1, [],
        smallAllocatorBinControls ++ controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hh0, hh1, hh2, hh3⟩ := descriptorSlot32Facts
    (smallAllocatorBinHeadAddress size smallMap) 0 4 hheadRoom (by decide)
  obtain ⟨hn0, hn1, hn2, hn3⟩ :=
    descriptorSlot32Facts chunk 8 12 hchunkRoom (by decide)
  iintro ⟨Hhead, Howned, Hdone⟩
  ihave Hsplit :
      (iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1) (some headerByte) ∗
        smallBinPayloadAt data (smallAllocatorBinSentinel size smallMap)
          previous tail) $$ [Howned]
  · iapply (dlmallocOwnedResult_nonzero_eq_smallBin data headerByte
      (smallAllocatorBinSentinel size smallMap) previous tail hnonzero).mp
    iexact Howned
  icases Hsplit with ⟨Hheader, Hpayload⟩
  isimp only [smallBinPayloadAt, sliceDescriptorAt] at Hpayload
  icases Hpayload with ⟨Hlinks, Htail⟩
  icases Hlinks with ⟨Hnext, Hprevious⟩
  rw [← List.take_append_drop 28 smallAllocatorAfterAvailability,
    smallAllocator_singleBinChoice_prefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_xor_i32
  iapply twp_const
  iapply twp_and
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localSet rfl
  simp only [smallAllocatorSelectedBin, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_localSet rfl
  simp only [smallAllocatorSelectedSize, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localSet rfl
  simp only [smallAllocatorBinSentinel, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  have hheadAddress :
      (1056352 : UInt32) +
        (
          (smallAllocatorBinIndex size +
            ((smallAllocatorShiftedMap size smallMap ^^^ 4294967295) &&& 1)) <<<
            (3 % 32)) = smallAllocatorBinHeadAddress size smallMap := by
    rfl
  rw [hheadAddress]
  ihave HheadAt : pointsTo_u32
      (smallAllocatorBinHeadAddress size smallMap + 0) chunk $$ [Hhead]
  · iapply pointsTo_u32_add_zero
    iexact Hhead
  iapply twp_load32 (address := smallAllocatorBinHeadAddress size smallMap)
      (offset := 0) chunk hh0 hh1 hh2 hh3 $$ HheadAt
  iintro HheadAt
  ihave Hhead : pointsTo_u32
      (smallAllocatorBinHeadAddress size smallMap) chunk $$ [HheadAt]
  · iapply pointsTo_u32_zero_add
    iexact HheadAt
  iapply twp_localSet rfl
  simp only [smallAllocatorBinHeadAddress, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  have hdata' : data = chunk + UInt32.ofNat 8 := by
    rw [show UInt32.ofNat 8 = (8 : UInt32) by decide]
    exact hdata
  ihave HnextAt : pointsTo_u32 (chunk + UInt32.ofNat 8)
      (1056344 + smallAllocatorSelectedSize size smallMap) $$ [Hnext]
  · rw [← hdata']
    iexact Hnext
  iapply twp_load32 (address := chunk) (offset := 8)
      (1056344 + smallAllocatorSelectedSize size smallMap)
      hn0 hn1 hn2 hn3 $$ HnextAt
  iintro HnextAt
  ihave Hnext : pointsTo_u32 data
      (1056344 + smallAllocatorSelectedSize size smallMap) $$ [HnextAt]
  · rw [hdata]
    iexact HnextAt
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_eq_i32 (result := 1)
    (by simp [smallAllocatorSelectedSize, smallAllocatorSelectedBin,
      show (3 : UInt32) % 32 = 3 by decide])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append, smallAllocatorBlockFrame]
  ihave Hpayload : smallBinPayloadAt data
      (1056344 + smallAllocatorSelectedSize size smallMap) previous tail $$
      [Hnext Hprevious Htail]
  · isimp only [smallBinPayloadAt, sliceDescriptorAt]
    iframe
  ihave Howned : dlmallocOwnedResult data headerByte
      (packU32 (1056344 + smallAllocatorSelectedSize size smallMap)
        previous :: tail) $$
      [Hheader Hpayload]
  · iapply (dlmallocOwnedResult_nonzero_eq_smallBin data headerByte
      (1056344 + smallAllocatorSelectedSize size smallMap)
      previous tail hnonzero).mpr
    iframe
  ihave HownedNamed : dlmallocOwnedResult data headerByte
      (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) $$
      [Howned]
  · rw [smallAllocatorBinSentinel]
    iexact Howned
  rw [show smallAllocatorBinIndex size +
        ((smallAllocatorShiftedMap size smallMap ^^^ 4294967295) &&& 1) =
      smallAllocatorSelectedBin size smallMap by rfl]
  rw [show smallAllocatorSelectedBin size smallMap <<< (3 % 32) =
      smallAllocatorSelectedSize size smallMap by rfl]
  rw [show 1056344 + smallAllocatorSelectedSize size smallMap =
      smallAllocatorBinSentinel size smallMap by rfl]
  iapply Hdone $$ Hhead HownedNamed

/- A singleton small-bin removal clears precisely the selected bitmap bit and
then falls through to the same header-update path used by multi-entry bins. -/
theorem smallAllocator_singleBinBitmapClear_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap chunk : UInt32) (R : IProp WasmHeapGF)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 1056608 smallMap ∗ R ∗
      (pointsTo_u32 1056608
          (smallAllocatorClearedSmallMap size smallMap) -∗
        R -∗
        WP (.running
          ⟨⟨[.i32 (smallAllocatorBinSentinel size smallMap)],
              [.i32 frame, .i32 chunk,
                .i32 (smallAllocatorSelectedSize size smallMap),
                .i32 0, .i32 0, .i32 smallMap,
                .i32 (smallAllocatorSelectedBin size smallMap),
                .i32 (smallAllocatorBinSentinel size smallMap),
                .i32 0, .i64 0], []⟩,
            smallAllocatorAfterBinLevel4, 1, [],
            List.append
              [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
                  smallAllocatorAfterBinLevel3,
                smallAllocatorBlockFrame smallAllocatorBinLevel2Body
                  smallAllocatorAfterBinLevel2,
                smallAllocatorBlockFrame smallAllocatorBinLevel1Body
                  smallAllocatorAfterBinLevel1]
              controls,
            calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (smallAllocatorBinSentinel size smallMap)],
          [.i32 frame, .i32 chunk,
            .i32 (smallAllocatorSelectedSize size smallMap),
            .i32 0, .i32 0, .i32 smallMap,
            .i32 (smallAllocatorSelectedBin size smallMap),
            .i32 (smallAllocatorBinSentinel size smallMap),
            .i32 0, .i64 0], []⟩,
        smallAllocatorAfterBinLevel5, 1, [],
        List.append
          [smallAllocatorBlockFrame smallAllocatorBinLevel4Body
              smallAllocatorAfterBinLevel4,
            smallAllocatorBlockFrame smallAllocatorBinLevel3Body
              smallAllocatorAfterBinLevel3,
            smallAllocatorBlockFrame smallAllocatorBinLevel2Body
              smallAllocatorAfterBinLevel2,
            smallAllocatorBlockFrame smallAllocatorBinLevel1Body
              smallAllocatorAfterBinLevel1]
          controls,
        calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hm0, hm1, hm2, hm3⟩ :=
    descriptorSlot32Facts 0 1056608 1056612 (by decide) (by decide)
  iintro ⟨Hmap, HR, Hdone⟩
  rw [← List.take_append_drop 7 smallAllocatorAfterBinLevel5,
    smallAllocator_singleBinBitmapClear_prefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_rotl_i32
  iapply twp_and
  ihave HmapAt : pointsTo_u32 (0 + UInt32.ofNat 1056608) smallMap $$ [Hmap]
  · rw [show 0 + UInt32.ofNat 1056608 = 1056608 by decide]
    iexact Hmap
  iapply twp_store32 smallMap hm0 hm1 hm2 hm3 $$ HmapAt
  iintro HmapAt
  rw [show smallAllocatorAfterBinLevel5.drop 7 = [] by rfl]
  rw [show List.append
      [smallAllocatorBlockFrame smallAllocatorBinLevel4Body
          smallAllocatorAfterBinLevel4,
        smallAllocatorBlockFrame smallAllocatorBinLevel3Body
          smallAllocatorAfterBinLevel3,
        smallAllocatorBlockFrame smallAllocatorBinLevel2Body
          smallAllocatorAfterBinLevel2,
        smallAllocatorBlockFrame smallAllocatorBinLevel1Body
          smallAllocatorAfterBinLevel1]
      controls =
      smallAllocatorBlockFrame smallAllocatorBinLevel4Body
          smallAllocatorAfterBinLevel4 ::
        List.append
          [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
              smallAllocatorAfterBinLevel3,
            smallAllocatorBlockFrame smallAllocatorBinLevel2Body
              smallAllocatorAfterBinLevel2,
            smallAllocatorBlockFrame smallAllocatorBinLevel1Body
              smallAllocatorAfterBinLevel1]
          controls by rfl]
  iapply twp_exitControl (by rfl)
  simp only [smallAllocatorBlockFrame, List.take_zero, List.nil_append]
  ihave Hmap : pointsTo_u32 1056608
      (smallAllocatorClearedSmallMap size smallMap) $$ [HmapAt]
  · rw [← show 0 + UInt32.ofNat 1056608 = 1056608 by decide]
    simp only [smallAllocatorClearedSmallMap]
    iexact HmapAt
  iapply Hdone $$ Hmap HR

/- Common successful allocation tail for either small-bin removal path.  The
three non-low bytes of the candidate header are kept separate only long enough
to supply the generated 32-bit header store; afterwards the public
`dlmallocOwnedResult` contract is restored with the new low header byte. -/
theorem smallAllocator_commonAllocation_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap chunk link data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (oldValues : List UInt64)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hnextRoom : (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤
      UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte oldValues ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (headerWordTailAt (data + 4294967292)
          (smallAllocatorAllocatedHeader size smallMap) -∗
        dlmallocOwnedResult data
          (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)
          oldValues -∗
        pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
          (nextHeader ||| 1) -∗
        WP (.running
          ⟨⟨[.i32 (chunk + 8)],
              [.i32 frame, .i32 chunk,
                .i32 (smallAllocatorNextChunk size smallMap chunk),
                .i32 0, .i32 0, .i32 smallMap,
                .i32 (smallAllocatorSelectedBin size smallMap),
                .i32 link, .i32 0, .i64 0], []⟩,
            smallAllocatorAfterOuter, 1, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (smallAllocatorBinSentinel size smallMap)],
          [.i32 frame, .i32 chunk,
            .i32 (smallAllocatorSelectedSize size smallMap),
            .i32 0, .i32 0, .i32 smallMap,
            .i32 (smallAllocatorSelectedBin size smallMap),
            .i32 link, .i32 0, .i64 0], []⟩,
        smallAllocatorAfterBinLevel4, 1, [],
        [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
            smallAllocatorAfterBinLevel3,
          smallAllocatorBlockFrame smallAllocatorBinLevel2Body
            smallAllocatorAfterBinLevel2,
          smallAllocatorBlockFrame smallAllocatorBinLevel1Body
            smallAllocatorAfterBinLevel1,
          smallAllocatorBlockFrame smallAllocatorThirdBody
            smallAllocatorAfterThird,
          smallAllocatorBlockFrame smallAllocatorSecondBody
            smallAllocatorAfterSecond,
          smallAllocatorBlockFrame smallAllocatorOuterBody
            smallAllocatorAfterOuter] ++ controls,
        calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hc0, hc1, hc2, hc3⟩ :=
    descriptorSlot32Facts chunk 4 8 hchunkRoom (by decide)
  obtain ⟨hn0, hn1, hn2, hn3⟩ := descriptorSlot32Facts
    (smallAllocatorNextChunk size smallMap chunk) 4 8 hnextRoom (by decide)
  have hheaderAddress : data + 4294967292 = chunk + 4 := by
    rw [hdata]
    bv_decide
  have hnewNonzero :
      (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0).toUInt32 &&&
          3 ≠ 0 := by
    simp only [smallAllocatorAllocatedHeader, u32Byte]
    bv_decide
  iintro ⟨HheaderTail, Howned, HnextHeader, Hdone⟩
  ihave Hsplit :
      (iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1) (some headerByte) ∗
        array64At data oldValues) $$ [Howned]
  · iapply (dlmallocOwnedResult_nonzero_eq_payload data headerByte oldValues
      hnonzero).mp
    iexact Howned
  icases Hsplit with ⟨HheaderByte, Hpayload⟩
  ihave HheaderByteOld :
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (data + 4294967292) (DFrac.own 1) (some (u32Byte oldHeader 0)) $$
      [HheaderByte]
  · rw [← hheaderByte]
    iexact HheaderByte
  ihave HheaderWord : pointsTo_u32 (data + 4294967292) oldHeader $$
      [HheaderByteOld HheaderTail]
  · iapply (pointsTo_u32_eq_headerByteTail
      (data + 4294967292) oldHeader).mpr
    iframe
  ihave HheaderWordAt : pointsTo_u32 (chunk + 4) oldHeader $$ [HheaderWord]
  · rw [← hheaderAddress]
    iexact HheaderWord
  rw [← List.take_append_drop 20 smallAllocatorAfterBinLevel4,
    smallAllocator_commonAllocation_prefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (8 : UInt32) + chunk = chunk + 8 by bv_decide]
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_or
  iapply twp_store32 oldHeader hc0 hc1 hc2 hc3 $$ HheaderWordAt
  iintro HheaderWordAt
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  rw [show smallAllocatorSelectedSize size smallMap + chunk =
      smallAllocatorNextChunk size smallMap chunk by
    simp only [smallAllocatorNextChunk]
    bv_decide]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HnextHeaderAt : pointsTo_u32
      (smallAllocatorNextChunk size smallMap chunk + UInt32.ofNat 4)
      nextHeader $$ [HnextHeader]
  · simp only [smallAllocatorNextChunk]
    iexact HnextHeader
  iapply twp_load32 nextHeader hn0 hn1 hn2 hn3 $$ HnextHeaderAt
  iintro HnextHeaderAt
  iapply twp_const
  iapply twp_or
  iapply twp_store32 nextHeader hn0 hn1 hn2 hn3 $$ HnextHeaderAt
  iintro HnextHeaderAt
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append, smallAllocatorBlockFrame]
  ihave HheaderWord : pointsTo_u32 (data + 4294967292)
      (smallAllocatorAllocatedHeader size smallMap) $$ [HheaderWordAt]
  · rw [hheaderAddress]
    simp only [smallAllocatorAllocatedHeader]
    iexact HheaderWordAt
  ihave HheaderParts :
      (iprop% pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1)
            (some (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)) ∗
        headerWordTailAt (data + 4294967292)
          (smallAllocatorAllocatedHeader size smallMap)) $$ [HheaderWord]
  · iapply (pointsTo_u32_eq_headerByteTail (data + 4294967292)
      (smallAllocatorAllocatedHeader size smallMap)).mp
    iexact HheaderWord
  icases HheaderParts with ⟨HheaderByte, HheaderTail⟩
  ihave Howned : dlmallocOwnedResult data
      (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0) oldValues $$
      [HheaderByte Hpayload]
  · iapply (dlmallocOwnedResult_nonzero_eq_payload data
      (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0) oldValues
      hnewNonzero).mpr
    iframe
  ihave HnextHeader : pointsTo_u32
      (smallAllocatorNextChunk size smallMap chunk + 4) (nextHeader ||| 1) $$
      [HnextHeaderAt]
  · simp only [smallAllocatorNextChunk]
    iexact HnextHeaderAt
  iapply Hdone $$ HheaderTail Howned HnextHeader

/- Complete singleton-bin path from the selected-bin arithmetic through the
bitmap clear and common allocation stores. -/
theorem smallAllocator_singleBinAllocation_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8)
    (hheadRoom : (smallAllocatorBinHeadAddress size smallMap).toNat + 4 ≤
      UInt32.size)
    (hchunkLinksRoom : chunk.toNat + 12 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hnextRoom : (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤
      UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (pointsTo_u32 1056608 (smallAllocatorClearedSmallMap size smallMap) -∗
        pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk -∗
        headerWordTailAt (data + 4294967292)
          (smallAllocatorAllocatedHeader size smallMap) -∗
        dlmallocOwnedResult data
          (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)
          (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) -∗
        pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
          (nextHeader ||| 1) -∗
        WP (.running
          ⟨⟨[.i32 (chunk + 8)],
              [.i32 frame, .i32 chunk,
                .i32 (smallAllocatorNextChunk size smallMap chunk),
                .i32 0, .i32 0, .i32 smallMap,
                .i32 (smallAllocatorSelectedBin size smallMap),
                .i32 (smallAllocatorBinSentinel size smallMap),
                .i32 0, .i64 0], []⟩,
            smallAllocatorAfterOuter, 1, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (smallAllocatorShiftedMap size smallMap)],
          [.i32 frame, .i32 (smallAllocatorBinIndex size),
            .i32 (smallAllocatorChunkSize size), .i32 0, .i32 0,
            .i32 smallMap, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
        smallAllocatorAfterAvailability, 1, [],
        smallAllocatorBinControls ++ smallAllocatorOuterControls ++ controls,
        calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  have Hchoice := smallAllocator_singleBinChoice_twp (α := α)
    size frame smallMap chunk previous data headerByte tail hnonzero hdata
    hheadRoom hchunkLinksRoom
    (s := s) (E := E) (Φ := Φ)
    (controls := smallAllocatorOuterControls ++ controls) (calls := calls)
  rw [List.append_assoc]
  iapply Hchoice
  isplitl [Hhead]
  · iexact Hhead
  isplitl [Howned]
  · iexact Howned
  iintro Hhead Howned
  have Hclear := smallAllocator_singleBinBitmapClear_twp (α := α)
    size frame smallMap chunk
    (iprop% pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader)
    (s := s) (E := E) (Φ := Φ)
    (controls := smallAllocatorOuterControls ++ controls) (calls := calls)
  iapply Hclear
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hhead HheaderTail Howned HnextHeader]
  · iframe
  iintro Hmap HR
  icases HR with ⟨Hhead, HheaderTail, Howned, HnextHeader⟩
  have Hcommon := smallAllocator_commonAllocation_twp (α := α)
    size frame smallMap chunk (smallAllocatorBinSentinel size smallMap)
    data oldHeader nextHeader headerByte
    (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail)
    hnonzero hheaderByte hdata hchunkRoom hnextRoom
    (s := s) (E := E) (Φ := Φ) (controls := controls) (calls := calls)
  have hcontrols :
      List.append
        [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
            smallAllocatorAfterBinLevel3,
          smallAllocatorBlockFrame smallAllocatorBinLevel2Body
            smallAllocatorAfterBinLevel2,
          smallAllocatorBlockFrame smallAllocatorBinLevel1Body
            smallAllocatorAfterBinLevel1]
        (smallAllocatorOuterControls ++ controls) =
      [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
          smallAllocatorAfterBinLevel3,
        smallAllocatorBlockFrame smallAllocatorBinLevel2Body
          smallAllocatorAfterBinLevel2,
        smallAllocatorBlockFrame smallAllocatorBinLevel1Body
          smallAllocatorAfterBinLevel1,
        smallAllocatorBlockFrame smallAllocatorThirdBody
          smallAllocatorAfterThird,
        smallAllocatorBlockFrame smallAllocatorSecondBody
          smallAllocatorAfterSecond,
        smallAllocatorBlockFrame smallAllocatorOuterBody
          smallAllocatorAfterOuter] ++ controls := by
    rfl
  rw [hcontrols]
  iapply Hcommon
  isplitl [HheaderTail]
  · iexact HheaderTail
  isplitl [Howned]
  · iexact Howned
  isplitl [HnextHeader]
  · iexact HnextHeader
  iintro HheaderTail Howned HnextHeader
  iapply Hdone $$ Hmap Hhead HheaderTail Howned HnextHeader

/- Exact unlink performed after the selected small bin contains more than one
free chunk.  Ownership of both mutated link words is required explicitly; the
candidate chunk's owned header and payload are only read and are returned
unchanged. -/
theorem smallAllocator_multiBinUnlink_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap chunk next previous data : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (hnextRoom : next.toNat + 16 ≤ UInt32.size)
    (hsentinelRoom : (smallAllocatorBinSentinel size smallMap).toNat + 12 ≤
      UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 (next + 12) chunk ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      dlmallocOwnedResult data headerByte (packU32 next previous :: tail) ∗
      (pointsTo_u32 (next + 12) (smallAllocatorBinSentinel size smallMap) -∗
        pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) next -∗
        dlmallocOwnedResult data headerByte (packU32 next previous :: tail) -∗
        WP (.running
          ⟨⟨[.i32 (smallAllocatorBinSentinel size smallMap)],
              [.i32 frame, .i32 chunk,
                .i32 (smallAllocatorSelectedSize size smallMap),
                .i32 0, .i32 0, .i32 smallMap,
                .i32 (smallAllocatorSelectedBin size smallMap),
                .i32 next, .i32 0, .i64 0], []⟩,
            smallAllocatorAfterBinLevel4, 1, [],
            List.append
              [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
                  smallAllocatorAfterBinLevel3,
                smallAllocatorBlockFrame smallAllocatorBinLevel2Body
                  smallAllocatorAfterBinLevel2,
                smallAllocatorBlockFrame smallAllocatorBinLevel1Body
                  smallAllocatorAfterBinLevel1]
              controls,
            calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (smallAllocatorBinSentinel size smallMap)],
          [.i32 frame, .i32 chunk,
            .i32 (smallAllocatorSelectedSize size smallMap),
            .i32 0, .i32 0, .i32 smallMap,
            .i32 (smallAllocatorSelectedBin size smallMap),
            .i32 next, .i32 0, .i64 0], []⟩,
        smallAllocatorAfterSingleBinChoice, 1, [],
        smallAllocatorBinControls ++ controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hn0, hn1, hn2, hn3⟩ :=
    descriptorSlot32Facts next 12 16 hnextRoom (by decide)
  obtain ⟨hs0, hs1, hs2, hs3⟩ := descriptorSlot32Facts
    (smallAllocatorBinSentinel size smallMap) 8 12 hsentinelRoom (by decide)
  have hheadAddress :
      smallAllocatorBinSentinel size smallMap + UInt32.ofNat 8 =
        smallAllocatorBinHeadAddress size smallMap := by
    rw [show UInt32.ofNat 8 = (8 : UInt32) by decide]
    simp only [smallAllocatorBinSentinel, smallAllocatorBinHeadAddress]
    bv_decide
  iintro ⟨HnextPrevious, Hhead, Howned, Hdone⟩
  rw [← List.take_append_drop 7 smallAllocatorAfterSingleBinChoice,
    smallAllocator_multiBinUnlink_prefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 chunk hn0 hn1 hn2 hn3 $$ HnextPrevious
  iintro HnextPrevious
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HheadAt : pointsTo_u32
      (smallAllocatorBinSentinel size smallMap + UInt32.ofNat 8) chunk $$ [Hhead]
  · rw [hheadAddress]
    iexact Hhead
  iapply twp_store32 chunk hs0 hs1 hs2 hs3 $$ HheadAt
  iintro HheadAt
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append, smallAllocatorBlockFrame]
  ihave Hhead : pointsTo_u32
      (smallAllocatorBinHeadAddress size smallMap) next $$ [HheadAt]
  · rw [← hheadAddress]
    iexact HheadAt
  iapply Hdone $$ HnextPrevious Hhead Howned

/- Complete non-singleton small-bin path after the false equality branch:
unlink the chosen chunk and run the shared header/allocation tail. -/
theorem smallAllocator_multiBinAllocation_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap chunk next previous data oldHeader
      followingHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8)
    (hnextLinkRoom : next.toNat + 16 ≤ UInt32.size)
    (hsentinelRoom : (smallAllocatorBinSentinel size smallMap).toNat + 12 ≤
      UInt32.size)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hfollowingRoom :
      (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 (next + 12) chunk ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte (packU32 next previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        followingHeader ∗
      (pointsTo_u32 (next + 12) (smallAllocatorBinSentinel size smallMap) -∗
        pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) next -∗
        headerWordTailAt (data + 4294967292)
          (smallAllocatorAllocatedHeader size smallMap) -∗
        dlmallocOwnedResult data
          (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)
          (packU32 next previous :: tail) -∗
        pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
          (followingHeader ||| 1) -∗
        WP (.running
          ⟨⟨[.i32 (chunk + 8)],
              [.i32 frame, .i32 chunk,
                .i32 (smallAllocatorNextChunk size smallMap chunk),
                .i32 0, .i32 0, .i32 smallMap,
                .i32 (smallAllocatorSelectedBin size smallMap),
                .i32 next, .i32 0, .i64 0], []⟩,
            smallAllocatorAfterOuter, 1, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 (smallAllocatorBinSentinel size smallMap)],
          [.i32 frame, .i32 chunk,
            .i32 (smallAllocatorSelectedSize size smallMap),
            .i32 0, .i32 0, .i32 smallMap,
            .i32 (smallAllocatorSelectedBin size smallMap),
            .i32 next, .i32 0, .i64 0], []⟩,
        smallAllocatorAfterSingleBinChoice, 1, [],
        smallAllocatorBinControls ++ smallAllocatorOuterControls ++ controls,
        calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨HnextPrevious, Hhead, HheaderTail, Howned,
    HfollowingHeader, Hdone⟩
  have Hunlink := smallAllocator_multiBinUnlink_twp (α := α)
    size frame smallMap chunk next previous data headerByte tail
    hnextLinkRoom hsentinelRoom
    (s := s) (E := E) (Φ := Φ)
    (controls := smallAllocatorOuterControls ++ controls) (calls := calls)
  rw [List.append_assoc]
  iapply Hunlink
  isplitl [HnextPrevious]
  · iexact HnextPrevious
  isplitl [Hhead]
  · iexact Hhead
  isplitl [Howned]
  · iexact Howned
  iintro HnextPrevious Hhead Howned
  have Hcommon := smallAllocator_commonAllocation_twp (α := α)
    size frame smallMap chunk next data oldHeader followingHeader headerByte
    (packU32 next previous :: tail) hnonzero hheaderByte hdata
    hchunkRoom hfollowingRoom
    (s := s) (E := E) (Φ := Φ) (controls := controls) (calls := calls)
  have hcontrols :
      List.append
        [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
            smallAllocatorAfterBinLevel3,
          smallAllocatorBlockFrame smallAllocatorBinLevel2Body
            smallAllocatorAfterBinLevel2,
          smallAllocatorBlockFrame smallAllocatorBinLevel1Body
            smallAllocatorAfterBinLevel1]
        (smallAllocatorOuterControls ++ controls) =
      [smallAllocatorBlockFrame smallAllocatorBinLevel3Body
          smallAllocatorAfterBinLevel3,
        smallAllocatorBlockFrame smallAllocatorBinLevel2Body
          smallAllocatorAfterBinLevel2,
        smallAllocatorBlockFrame smallAllocatorBinLevel1Body
          smallAllocatorAfterBinLevel1,
        smallAllocatorBlockFrame smallAllocatorThirdBody
          smallAllocatorAfterThird,
        smallAllocatorBlockFrame smallAllocatorSecondBody
          smallAllocatorAfterSecond,
        smallAllocatorBlockFrame smallAllocatorOuterBody
          smallAllocatorAfterOuter] ++ controls := by
    rfl
  rw [hcontrols]
  iapply Hcommon
  isplitl [HheaderTail]
  · iexact HheaderTail
  isplitl [Howned]
  · iexact Howned
  isplitl [HfollowingHeader]
  · iexact HfollowingHeader
  iintro HheaderTail Howned HfollowingHeader
  iapply Hdone $$ HnextPrevious Hhead HheaderTail Howned HfollowingHeader

/- One complete sound successful path through local `func162`: a small request
selects a populated singleton bin, clears its bitmap bit, updates both chunk
headers, restores the stack pointer, and returns the candidate data pointer. -/
theorem smallAllocator_singleton_afterFrame_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size frame smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (hsmall : size < 245)
    (havailable : smallAllocatorShiftedMap size smallMap &&& 3 ≠ 0)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8)
    (hheadRoom : (smallAllocatorBinHeadAddress size smallMap).toNat + 4 ≤
      UInt32.size)
    (hchunkLinksRoom : chunk.toNat + 12 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hnextRoom : (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤
      UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (globalPointsTo 0 (.i32 (frame + 16)) -∗
        pointsTo_u32 1056608 (smallAllocatorClearedSmallMap size smallMap) -∗
        pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk -∗
        headerWordTailAt (data + 4294967292)
          (smallAllocatorAllocatedHeader size smallMap) -∗
        dlmallocOwnedResult data
          (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)
          (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) -∗
        pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
          (nextHeader ||| 1) -∗
        WP (.running
          ⟨⟨[.i32 (chunk + 8)],
              [.i32 frame, .i32 chunk,
                .i32 (smallAllocatorNextChunk size smallMap chunk),
                .i32 0, .i32 0, .i32 smallMap,
                .i32 (smallAllocatorSelectedBin size smallMap),
                .i32 (smallAllocatorBinSentinel size smallMap),
                .i32 0, .i64 0], [.i32 (chunk + 8)]⟩,
            [], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size], smallAllocatorFrameLocals frame, []⟩,
        smallAllocatorAfterFrame, 1, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  have Htree := smallAllocator_to_smallBinTree_twp (α := α)
    size frame data headerByte
    (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail)
    hsmall (s := s) (E := E) (Φ := Φ) (controls := []) (calls := calls)
  iapply Htree
  isplitl [Howned]
  · iexact Howned
  iintro Howned
  have Henter := smallAllocator_enter_smallBinSelector_twp (α := α)
    (dlmallocOwnedResult data headerByte
      (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail))
    size frame (s := s) (E := E) (Φ := Φ) (controls := []) (calls := calls)
  simp only [smallAllocatorOuterControls] at Henter
  iapply Henter
  isplitl [Howned]
  · iexact Howned
  iintro Howned
  have Havailable := smallAllocator_smallBin_available_twp (α := α)
    size frame smallMap havailable
    (dlmallocOwnedResult data headerByte
      (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail))
    (s := s) (E := E) (Φ := Φ)
    (controls := smallAllocatorBinControls ++ smallAllocatorOuterControls)
    (calls := calls)
  simp only [smallAllocatorOuterControls] at Havailable
  rw [List.append_nil]
  iapply Havailable
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Howned]
  · iexact Howned
  iintro Hmap Howned
  have Hallocate := smallAllocator_singleBinAllocation_twp (α := α)
    size frame smallMap chunk previous data oldHeader nextHeader headerByte tail
    hnonzero hheaderByte hdata hheadRoom hchunkLinksRoom hchunkRoom hnextRoom
    (s := s) (E := E) (Φ := Φ) (controls := []) (calls := calls)
  simp only [smallAllocatorOuterControls, List.append_nil] at Hallocate
  iapply Hallocate
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hhead]
  · iexact Hhead
  isplitl [HheaderTail]
  · iexact HheaderTail
  isplitl [Howned]
  · iexact Howned
  isplitl [HnextHeader]
  · iexact HnextHeader
  iintro Hmap Hhead HheaderTail Howned HnextHeader
  let rest : List Value :=
    [.i32 chunk, .i32 (smallAllocatorNextChunk size smallMap chunk),
      .i32 0, .i32 0, .i32 smallMap,
      .i32 (smallAllocatorSelectedBin size smallMap),
      .i32 (smallAllocatorBinSentinel size smallMap), .i32 0, .i64 0]
  have Hepilogue := smallAllocator_epilogue_twp (α := α)
    (chunk + 8) frame rest
    (iprop% pointsTo_u32 1056608
        (smallAllocatorClearedSmallMap size smallMap) ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292)
        (smallAllocatorAllocatedHeader size smallMap) ∗
      dlmallocOwnedResult data
        (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        (nextHeader ||| 1))
    (s := s) (E := E) (Φ := Φ) (controls := []) (calls := calls)
  iapply Hepilogue
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hmap Hhead HheaderTail Howned HnextHeader]
  · iframe
  iintro Hglobal HR
  icases HR with ⟨Hmap, Hhead, HheaderTail, Howned, HnextHeader⟩
  isimp only [rest]
  iapply Hdone $$ Hglobal Hmap Hhead HheaderTail Howned HnextHeader

/- Complete small-alignment singleton path of local `func170`.  The selected
owned block is returned from local162, installed in func170's second
parameter, and zero-filled by the already-proved post-selection rule. -/
theorem dlmalloc_singleton_ownedResult_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align stackTop smallMap chunk previous data oldHeader
      nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (halign : align < 9)
    (hsmall : size < 245)
    (havailable : smallAllocatorShiftedMap size smallMap &&& 3 ≠ 0)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8) (hdataNonzero : data ≠ 0)
    (hsize : size ≠ 0)
    (hlength : size.toNat =
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length)
    (hpayloadRoom : data.toNat +
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length ≤
      UInt32.size)
    (hheadRoom : (smallAllocatorBinHeadAddress size smallMap).toNat + 4 ≤
      UInt32.size)
    (hchunkLinksRoom : chunk.toNat + 12 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hnextRoom : (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤
      UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 ((stackTop - 16) + 16)) -∗
        pointsTo_u32 1056608 (smallAllocatorClearedSmallMap size smallMap) -∗
        pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk -∗
        headerWordTailAt (data + 4294967292)
          (smallAllocatorAllocatedHeader size smallMap) -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (data + 4294967292) (DFrac.own 1)
          (some (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)) -∗
        array64At data
          (List.replicate
            (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length
            0) -∗
        pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
          (nextHeader ||| 1) -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 data], [], [.i32 data]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 align], [], []⟩,
        func170, 1, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hmap, Hhead, HheaderTail, Howned,
    HnextHeader, Hdone⟩
  have Hselect := dlmalloc_to_smallAllocator_twp (α := α)
    size align halign (s := s) (E := E) (Φ := Φ)
    (controls := controls) (calls := calls)
  iapply Hselect
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  have Hentry := smallAllocator_owned_entry_twp (α := α)
    size stackTop data headerByte
    (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail)
    (s := s) (E := E) (Φ := Φ) (controls := [])
    (calls :=
      { locals := ⟨[.i32 size, .i32 align], [], []⟩
        continuation := [.localSet 1]
        resultArity := 1
        callerRemainder := []
        control := dlmallocSelectOuterFrame size align :: controls } :: calls)
  iapply Hentry
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Howned]
  · iexact Howned
  iintro Hglobal Howned
  have Hbody := smallAllocator_singleton_afterFrame_twp (α := α)
    size (stackTop - 16) smallMap chunk previous data oldHeader nextHeader
    headerByte tail hsmall havailable hnonzero hheaderByte hdata hheadRoom
    hchunkLinksRoom hchunkRoom hnextRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := ⟨[.i32 size, .i32 align], [], []⟩
        continuation := [.localSet 1]
        resultArity := 1
        callerRemainder := []
        control := dlmallocSelectOuterFrame size align :: controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hhead]
  · iexact Hhead
  isplitl [HheaderTail]
  · iexact HheaderTail
  isplitl [Howned]
  · iexact Howned
  isplitl [HnextHeader]
  · iexact HnextHeader
  iintro Hglobal Hmap Hhead HheaderTail Howned HnextHeader
  iapply twp_returnFromCallFallthrough
  simp only [List.take, List.singleton_append]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons]
  rw [← hdata]
  iapply twp_exitControl (by rfl)
  simp only [dlmallocSelectOuterFrame, List.take_zero, List.drop_zero,
    List.nil_append]
  have Hafter := dlmalloc_afterSelect_ownedResult_twp (α := α)
    size data (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)
    (packU32 (smallAllocatorBinSentinel size smallMap) previous) tail
    hdataNonzero hsize hlength hpayloadRoom
    (s := s) (E := E) (Φ := Φ) (controls := controls) (calls := calls)
  iapply Hafter
  isplitl [Howned]
  · iexact Howned
  iintro Hheader Harray
  iapply Hdone $$ Hruntime Hglobal Hmap Hhead HheaderTail Hheader Harray
    HnextHeader

def dlmallocSingletonZeroedAt [WasmHeapGS] [WasmGlobalGS]
    (size stackTop smallMap chunk previous data nextHeader : UInt32)
    (tail : List UInt64) : IProp WasmHeapGF :=
  iprop% globalPointsTo 0 (.i32 ((stackTop - 16) + 16)) ∗
    pointsTo_u32 1056608 (smallAllocatorClearedSmallMap size smallMap) ∗
    pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
    headerWordTailAt (data + 4294967292)
      (smallAllocatorAllocatedHeader size smallMap) ∗
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (data + 4294967292) (DFrac.own 1)
      (some (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)) ∗
    array64At data
      (List.replicate
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length
        0) ∗
    pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
      (nextHeader ||| 1)

/- Local `func131` is now a complete owned allocator forwarder on the verified
singleton path: func170 returns by fallthrough and leaves func131 at its
generated explicit `ret` with the zeroed data pointer. -/
theorem allocatorForward_singleton_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align stackTop smallMap chunk previous data oldHeader
      nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (halign : align < 9)
    (hsmall : size < 245)
    (havailable : smallAllocatorShiftedMap size smallMap &&& 3 ≠ 0)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8) (hdataNonzero : data ≠ 0)
    (hsize : size ≠ 0)
    (hlength : size.toNat =
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length)
    (hpayloadRoom : data.toNat +
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length ≤
      UInt32.size)
    (hheadRoom : (smallAllocatorBinHeadAddress size smallMap).toNat + 4 ≤
      UInt32.size)
    (hchunkLinksRoom : chunk.toNat + 12 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hnextRoom : (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤
      UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        dlmallocSingletonZeroedAt size stackTop smallMap chunk previous data
          nextHeader tail -∗
        WP (.running
          ⟨⟨[.i32 size, .i32 align], [], [.i32 data]⟩,
            [.ret], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 size, .i32 align], [], []⟩,
        func131, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hmap, Hhead, HheaderTail, Howned,
    HnextHeader, Hdone⟩
  have Hforward := allocatorForward_body_twp (α := α)
    size align (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hforward
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  have Hdlmalloc := dlmalloc_singleton_ownedResult_twp (α := α)
    size align stackTop smallMap chunk previous data oldHeader nextHeader
    headerByte tail halign hsmall havailable hnonzero hheaderByte hdata
    hdataNonzero hsize hlength hpayloadRoom hheadRoom hchunkLinksRoom
    hchunkRoom hnextRoom
    (s := s) (E := E) (Φ := Φ) (controls := [])
    (calls := allocatorForwardFrame size align :: calls)
  simp only [allocatorForwardFrame] at Hdlmalloc
  iapply Hdlmalloc
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hhead]
  · iexact Hhead
  isplitl [HheaderTail]
  · iexact HheaderTail
  isplitl [Howned]
  · iexact Howned
  isplitl [HnextHeader]
  · iexact HnextHeader
  iintro Hruntime Hglobal Hmap Hhead HheaderTail Hheader Harray HnextHeader
  iapply twp_returnFromCallFallthrough
  simp only [List.take, List.singleton_append]
  ihave Hzeroed : dlmallocSingletonZeroedAt size stackTop smallMap chunk
      previous data nextHeader tail $$
      [Hglobal Hmap Hhead HheaderTail Hheader Harray HnextHeader]
  · isimp only [dlmallocSingletonZeroedAt]
    iframe
  iapply Hdone $$ Hruntime Hzeroed

/- Absolute-index-133 call rule for the complete singleton allocator path. -/
theorem allocatorForward_singleton_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (size align stackTop smallMap chunk previous data oldHeader
      nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (halign : align < 9) (hsmall : size < 245)
    (havailable : smallAllocatorShiftedMap size smallMap &&& 3 ≠ 0)
    (hnonzero : headerByte.toUInt32 &&& 3 ≠ 0)
    (hheaderByte : headerByte = u32Byte oldHeader 0)
    (hdata : data = chunk + 8) (hdataNonzero : data ≠ 0)
    (hsize : size ≠ 0)
    (hlength : size.toNat =
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length)
    (hpayloadRoom : data.toNat +
      8 * (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail).length ≤
      UInt32.size)
    (hheadRoom : (smallAllocatorBinHeadAddress size smallMap).toNat + 4 ≤
      UInt32.size)
    (hchunkLinksRoom : chunk.toNat + 12 ≤ UInt32.size)
    (hchunkRoom : chunk.toNat + 8 ≤ UInt32.size)
    (hnextRoom : (smallAllocatorNextChunk size smallMap chunk).toNat + 8 ≤
      UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        dlmallocSingletonZeroedAt size stackTop smallMap chunk previous data
          nextHeader tail -∗
        WP (.running
          ⟨{ callerLocals with values := .i32 data :: stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 align, .i32 size] ++ stack },
        .call 133 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hmap, Hhead, HheaderTail, Howned,
    HnextHeader, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 133 func131Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func131Def, Function.toLocals, Function.numParams]
  have Hbody := allocatorForward_singleton_twp (α := α)
    size align stackTop smallMap chunk previous data oldHeader nextHeader
    headerByte tail halign hsmall havailable hnonzero hheaderByte hdata
    hdataNonzero hsize hlength hpayloadRoom hheadRoom hchunkLinksRoom
    hchunkRoom hnextRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hhead]
  · iexact Hhead
  isplitl [HheaderTail]
  · iexact HheaderTail
  isplitl [Howned]
  · iexact Howned
  isplitl [HnextHeader]
  · iexact HnextHeader
  iintro Hruntime Hzeroed
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.singleton_append]
  iapply Hdone $$ Hruntime Hzeroed

end Project.Mergesort.AllocatorProof
