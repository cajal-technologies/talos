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

/-! ## Local `func143`: the allocator-result core on the singleton path

Local `func143` (absolute index 145) reserves a 32-byte frame, dispatches on
its nonzero-size and zeroed-request flags, forwards the request to local
`func131` at absolute index 133, and copies the resulting `(data, size)` pair
into its caller-supplied result slot. -/

def allocatorResultTail : Program :=
  [.localGet 4, .load32 8, .localSet 8,
    .localGet 0, .localGet 4, .load32 12, .store32 4,
    .localGet 0, .localGet 8, .store32 0,
    .localGet 4, .const 32, .add, .globalSet 0, .ret]

def allocatorResultCheckBody : Program :=
  [.localGet 4, .load32 16, .br_if 0,
    .localGet 4, .const 0, .store32 28,
    .localGet 4, .const 0, .store32 24,
    .const 0, .load32 1050408, .localSet 5,
    .const 0, .load32 1050412, .localSet 6,
    .localGet 4, .localGet 5, .store32 8,
    .localGet 4, .localGet 6, .store32 12,
    .br 1]

def allocatorResultSuccessStores : Program :=
  [.localGet 4, .localGet 4, .load32 16, .store32 28,
    .localGet 4, .localGet 4, .load32 28, .store32 24,
    .localGet 4, .localGet 4, .load32 24, .store32 20,
    .localGet 4, .load32 20, .localSet 7,
    .localGet 4, .localGet 7, .store32 8,
    .localGet 4, .localGet 2, .store32 12]

def allocatorResultFlagBody : Program :=
  [.localGet 2, .br_if 0, .br 1]

def allocatorResultZeroedFlagBody : Program :=
  [.block 0 0 allocatorResultFlagBody, .localGet 3, .br_if 2, .br 1]

def allocatorResultZeroSizeBody : Program :=
  .block 0 0 allocatorResultZeroedFlagBody ::
    [.localGet 4, .localGet 1, .store32 8,
      .localGet 4, .const 0, .store32 12, .br 3]

def allocatorResultUninitBody : Program :=
  .block 0 0 allocatorResultZeroSizeBody ::
    [.call 134, .localGet 4, .localGet 2, .localGet 1, .call 130,
      .store32 16, .br 1]

def allocatorResultForwardBody : Program :=
  .block 0 0 allocatorResultUninitBody ::
    [.call 134, .localGet 4, .localGet 2, .localGet 1, .call 133,
      .store32 16]

def allocatorResultOuterBody : Program :=
  .block 0 0 allocatorResultForwardBody ::
    .block 0 0 allocatorResultCheckBody ::
    allocatorResultSuccessStores

private theorem func143_shape :
    func143 =
      [.globalGet 0, .const 32, .sub, .localSet 4,
        .localGet 4, .globalSet 0,
        .block 0 0 allocatorResultOuterBody] ++ allocatorResultTail := by
  rfl

def allocatorResultOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := allocatorResultOuterBody
    continuation := allocatorResultTail
    belowStack := [] }

def allocatorResultForwardFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := allocatorResultForwardBody
    continuation :=
      .block 0 0 allocatorResultCheckBody :: allocatorResultSuccessStores
    belowStack := [] }

/- Pure prefix of local `func143`: reserve the 32-byte frame, take the
generated nonzero-size/zeroed-request branch, cross the no-op guard at
absolute index 134, and stop exactly at the absolute-index-133 forwarding
call. -/
theorem allocatorResult_to_forward_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (resultPtr align size flag stackTop : UInt32)
    (hsize : size ≠ 0) (hflag : flag ≠ 0)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 stackTop) ∗ R ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗ R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 align, .i32 size, .i32 flag],
              [.i32 (stackTop - 32), .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 align, .i32 size, .i32 (stackTop - 32)]⟩,
            .call 133 :: [.store32 16], 0, [],
            [allocatorResultForwardFrame, allocatorResultOuterFrame],
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 align, .i32 size, .i32 flag],
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func143, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, HR, Hdone⟩
  rw [func143_shape]
  simp only [List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_block
  simp only [allocatorResultOuterBody]
  iapply twp_block
  simp only [allocatorResultForwardBody]
  iapply twp_block
  simp only [allocatorResultUninitBody]
  iapply twp_block
  simp only [allocatorResultZeroSizeBody]
  iapply twp_block
  simp only [allocatorResultZeroedFlagBody]
  iapply twp_block
  simp only [allocatorResultFlagBody]
  iapply twp_localGet rfl
  iapply twp_brIf hsize (by rfl)
  iapply twp_localGet rfl
  iapply twp_brIf hflag (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_call (α := α) «module» 134 func132Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func132Def, func132, Function.toLocals, Function.numParams]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  isimp only [allocatorResultForwardFrame, allocatorResultOuterFrame,
    allocatorResultForwardBody, allocatorResultOuterBody,
    allocatorResultUninitBody, allocatorResultZeroSizeBody,
    allocatorResultZeroedFlagBody, allocatorResultFlagBody] at Hdone
  iapply Hdone $$ Hruntime Hglobal HR

/- Exact successful suffix of local `func143` after the forwarding call has
left a nonzero data pointer on the operand stack: record it throughout the
frame's bookkeeping words and store the final `(data, size)` pair into the
caller-supplied result slot. -/
set_option maxHeartbeats 4000000 in
theorem allocatorResult_success_suffix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr align size flag frame data : UInt32)
    (old8 old12 old16 old20 old24 old28 : UInt32)
    (oldResultData oldResultSize : UInt32)
    (hframeRoom : frame.toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    (hdata : data ≠ 0)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 (frame + 8) old8 ∗
      pointsTo_u32 (frame + 12) old12 ∗
      pointsTo_u32 (frame + 16) old16 ∗
      pointsTo_u32 (frame + 20) old20 ∗
      pointsTo_u32 (frame + 24) old24 ∗
      pointsTo_u32 (frame + 28) old28 ∗
      allocationPairAt resultPtr oldResultData oldResultSize ∗
      (globalPointsTo 0 (.i32 (frame + 32)) -∗
        pointsTo_u32 (frame + 8) data -∗
        pointsTo_u32 (frame + 12) size -∗
        pointsTo_u32 (frame + 16) data -∗
        pointsTo_u32 (frame + 20) data -∗
        pointsTo_u32 (frame + 24) data -∗
        pointsTo_u32 (frame + 28) data -∗
        allocationPairAt resultPtr data size -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 align, .i32 size, .i32 flag],
              [.i32 frame, .i32 0, .i32 0, .i32 data, .i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 align, .i32 size, .i32 flag],
          [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0],
          [.i32 data, .i32 frame]⟩,
        [.store32 16], 0, [],
        [allocatorResultForwardFrame, allocatorResultOuterFrame],
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 32 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 32 hframeRoom (by decide)
  obtain ⟨hf160, hf161, hf162, hf163⟩ :=
    descriptorSlot32Facts frame 16 32 hframeRoom (by decide)
  obtain ⟨hf200, hf201, hf202, hf203⟩ :=
    descriptorSlot32Facts frame 20 32 hframeRoom (by decide)
  obtain ⟨hf240, hf241, hf242, hf243⟩ :=
    descriptorSlot32Facts frame 24 32 hframeRoom (by decide)
  obtain ⟨hf280, hf281, hf282, hf283⟩ :=
    descriptorSlot32Facts frame 28 32 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    descriptorSlot32Facts resultPtr 0 8 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 8 hresultRoom (by decide)
  iintro ⟨Hglobal, H8, H12, H16, H20, H24, H28, Hresult, Hdone⟩
  isimp only [allocationPairAt] at Hresult
  icases Hresult with ⟨Hr0, Hr4⟩
  iapply twp_store32 old16 hf160 hf161 hf162 hf163 $$ H16
  iintro H16
  iapply twp_exitControl (by rfl)
  simp only [allocatorResultForwardFrame, List.take_zero, List.nil_append]
  iapply twp_block
  simp only [allocatorResultCheckBody]
  iapply twp_localGet rfl
  iapply twp_load32 data hf160 hf161 hf162 hf163 $$ H16
  iintro H16
  iapply twp_brIf hdata (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  simp only [allocatorResultSuccessStores]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 data hf160 hf161 hf162 hf163 $$ H16
  iintro H16
  iapply twp_store32 old28 hf280 hf281 hf282 hf283 $$ H28
  iintro H28
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 data hf280 hf281 hf282 hf283 $$ H28
  iintro H28
  iapply twp_store32 old24 hf240 hf241 hf242 hf243 $$ H24
  iintro H24
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 data hf240 hf241 hf242 hf243 $$ H24
  iintro H24
  iapply twp_store32 old20 hf200 hf201 hf202 hf203 $$ H20
  iintro H20
  iapply twp_localGet rfl
  iapply twp_load32 data hf200 hf201 hf202 hf203 $$ H20
  iintro H20
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old8 hf80 hf81 hf82 hf83 $$ H8
  iintro H8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old12 hf120 hf121 hf122 hf123 $$ H12
  iintro H12
  iapply twp_exitControl (by rfl)
  simp only [allocatorResultOuterFrame, List.take_zero, List.nil_append]
  simp only [allocatorResultTail]
  iapply twp_localGet rfl
  iapply twp_load32 data hf80 hf81 hf82 hf83 $$ H8
  iintro H8
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 size hf120 hf121 hf122 hf123 $$ H12
  iintro H12
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
  rw [UInt32.add_comm (32 : UInt32) frame]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave Hr0 : pointsTo_u32 resultPtr data $$ [Hr0At]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact Hr0At
  ihave Hresult : allocationPairAt resultPtr data size $$ [Hr0 Hr4]
  · isimp only [allocationPairAt]
    iframe
  iapply Hdone $$ Hglobal H8 H12 H16 H20 H24 H28 Hresult

/- Allocator-internal state left over by the verified singleton path, with
the stack global and the zero-filled payload split off so that callers can
consume them directly. -/
def allocatorCoreResidueAt [WasmHeapGS]
    (size smallMap chunk data nextHeader : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 1056608 (smallAllocatorClearedSmallMap size smallMap) ∗
    pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
    headerWordTailAt (data + 4294967292)
      (smallAllocatorAllocatedHeader size smallMap) ∗
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (data + 4294967292) (DFrac.own 1)
      (some (u32Byte (smallAllocatorAllocatedHeader size smallMap) 0)) ∗
    pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
      (nextHeader ||| 1)

/- Complete singleton-path body rule for local `func143`.  The allocator
package is threaded to the absolute-index-133 call and comes back as the
zeroed payload, the fresh result pair, and the opaque allocator residue. -/
set_option maxHeartbeats 4000000 in
theorem allocatorResult_singleton_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr flag stackTop : UInt32)
    (size align smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (old8 old12 old16 old20 old24 old28 : UInt32)
    (oldResultData oldResultSize : UInt32)
    (hflag : flag ≠ 0)
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
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 32) + 12) old12 ∗
      pointsTo_u32 ((stackTop - 32) + 16) old16 ∗
      pointsTo_u32 ((stackTop - 32) + 20) old20 ∗
      pointsTo_u32 ((stackTop - 32) + 24) old24 ∗
      pointsTo_u32 ((stackTop - 32) + 28) old28 ∗
      allocationPairAt resultPtr oldResultData oldResultSize ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 32) + 8) data -∗
        pointsTo_u32 ((stackTop - 32) + 12) size -∗
        pointsTo_u32 ((stackTop - 32) + 16) data -∗
        pointsTo_u32 ((stackTop - 32) + 20) data -∗
        pointsTo_u32 ((stackTop - 32) + 24) data -∗
        pointsTo_u32 ((stackTop - 32) + 28) data -∗
        allocationPairAt resultPtr data size -∗
        allocatorCoreResidueAt size smallMap chunk data nextHeader -∗
        array64At data
          (List.replicate
            (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
              tail).length 0) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 align, .i32 size, .i32 flag],
              [.i32 (stackTop - 32), .i32 0, .i32 0, .i32 data, .i32 data],
              []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 align, .i32 size, .i32 flag],
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func143, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, H8, H12, H16, H20, H24, H28, Hresult,
    Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  have Hprefix := allocatorResult_to_forward_twp (α := α)
    (iprop% pointsTo_u32 ((stackTop - 32) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 32) + 12) old12 ∗
      pointsTo_u32 ((stackTop - 32) + 16) old16 ∗
      pointsTo_u32 ((stackTop - 32) + 20) old20 ∗
      pointsTo_u32 ((stackTop - 32) + 24) old24 ∗
      pointsTo_u32 ((stackTop - 32) + 28) old28 ∗
      allocationPairAt resultPtr oldResultData oldResultSize)
    resultPtr align size flag stackTop hsize hflag
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hprefix
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H8 H12 H16 H20 H24 H28 Hresult]
  · iframe
  iintro Hruntime Hglobal HR
  icases HR with ⟨H8, H12, H16, H20, H24, H28, Hresult⟩
  have Hforward := allocatorForward_singleton_call_twp (α := α)
    size align (stackTop - 32) smallMap chunk previous data oldHeader
    nextHeader headerByte tail halign hsmall havailable hnonzero
    hheaderByte hdata hdataNonzero hsize hlength hpayloadRoom hheadRoom
    hchunkLinksRoom hchunkRoom hnextRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 resultPtr, .i32 align, .i32 size, .i32 flag],
        [.i32 (stackTop - 32), .i32 0, .i32 0, .i32 0, .i32 0], []⟩)
    (stack := [.i32 (stackTop - 32)])
    (code := [.store32 16]) (arity := 0) (remainder := [])
    (controls := [allocatorResultForwardFrame, allocatorResultOuterFrame])
    (calls := calls)
  simp only [List.cons_append, List.nil_append] at Hforward
  iapply Hforward
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
  isimp only [dlmallocSingletonZeroedAt] at Hzeroed
  icases Hzeroed with ⟨HglobalA, Hmap, Hhead, HheaderTail, Hheader,
    Harray, HnextHeader⟩
  ihave Hglobal : globalPointsTo 0 (.i32 (stackTop - 32)) $$ [HglobalA]
  · rw [show (stackTop - 32) - 16 + 16 = stackTop - 32 by bv_decide]
    iexact HglobalA
  have Hsuffix := allocatorResult_success_suffix_twp (α := α)
    resultPtr align size flag (stackTop - 32) data
    old8 old12 old16 old20 old24 old28 oldResultData oldResultSize
    hframeRoom hresultRoom hdataNonzero
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hsuffix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H8]
  · iexact H8
  isplitl [H12]
  · iexact H12
  isplitl [H16]
  · iexact H16
  isplitl [H20]
  · iexact H20
  isplitl [H24]
  · iexact H24
  isplitl [H28]
  · iexact H28
  isplitl [Hresult]
  · iexact Hresult
  iintro Hglobal H8 H12 H16 H20 H24 H28 Hresult
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (stackTop - 32) + 32 = stackTop by bv_decide]
    iexact Hglobal
  ihave Hresidue : allocatorCoreResidueAt size smallMap chunk data
      nextHeader $$ [Hmap Hhead HheaderTail Hheader HnextHeader]
  · isimp only [allocatorCoreResidueAt]
    iframe
  iapply Hdone $$ Hruntime HglobalTop H8 H12 H16 H20 H24 H28 Hresult
    Hresidue Harray

/- Absolute-index-145 call rule for the allocator-result core, preserving an
arbitrary caller frame. -/
set_option maxHeartbeats 4000000 in
theorem allocatorResult_singleton_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr flag stackTop : UInt32)
    (size align smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (old8 old12 old16 old20 old24 old28 : UInt32)
    (oldResultData oldResultSize : UInt32)
    (hflag : flag ≠ 0)
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
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 32) + 12) old12 ∗
      pointsTo_u32 ((stackTop - 32) + 16) old16 ∗
      pointsTo_u32 ((stackTop - 32) + 20) old20 ∗
      pointsTo_u32 ((stackTop - 32) + 24) old24 ∗
      pointsTo_u32 ((stackTop - 32) + 28) old28 ∗
      allocationPairAt resultPtr oldResultData oldResultSize ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 32) + 8) data -∗
        pointsTo_u32 ((stackTop - 32) + 12) size -∗
        pointsTo_u32 ((stackTop - 32) + 16) data -∗
        pointsTo_u32 ((stackTop - 32) + 20) data -∗
        pointsTo_u32 ((stackTop - 32) + 24) data -∗
        pointsTo_u32 ((stackTop - 32) + 28) data -∗
        allocationPairAt resultPtr data size -∗
        allocatorCoreResidueAt size smallMap chunk data nextHeader -∗
        array64At data
          (List.replicate
            (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
              tail).length 0) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 flag, .i32 size, .i32 align, .i32 resultPtr] ++ stack },
        .call 145 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, H8, H12, H16, H20, H24, H28, Hresult,
    Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 145 func143Def
      (by decide) allocatorResult_index $$ Hruntime
  iintro Hruntime
  simp [func143Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := allocatorResult_singleton_twp (α := α)
    resultPtr flag stackTop size align smallMap chunk previous data
    oldHeader nextHeader headerByte tail old8 old12 old16 old20 old24
    old28 oldResultData oldResultSize hflag halign hsmall havailable
    hnonzero hheaderByte hdata hdataNonzero hsize hlength hpayloadRoom
    hheadRoom hchunkLinksRoom hchunkRoom hnextRoom hframeRoom hresultRoom
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
  isplitl [H8]
  · iexact H8
  isplitl [H12]
  · iexact H12
  isplitl [H16]
  · iexact H16
  isplitl [H20]
  · iexact H20
  isplitl [H24]
  · iexact H24
  isplitl [H28]
  · iexact H28
  isplitl [Hresult]
  · iexact Hresult
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
  iintro Hruntime Hglobal H8 H12 H16 H20 H24 H28 Hresult Hresidue Harray
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal H8 H12 H16 H20 H24 H28 Hresult
    Hresidue Harray

/- Complete singleton-path body rule for local `func145`: the pure wrapper
prefix, the verified local-`func143` core, and the wrapper's result-copy
suffix, composed into one closed contract. -/
set_option maxHeartbeats 4000000 in
theorem zeroedAllocatorWrapper_singleton_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr metaPtr stackTop : UInt32)
    (size align smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (old8 old12 old16 old20 old24 old28 : UInt32)
    (oldPairData oldPairSize oldResultData oldResultSize : UInt32)
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
    (hwrapRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hcoreRoom : (stackTop - 48).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 48) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 48) + 12) old12 ∗
      pointsTo_u32 ((stackTop - 48) + 16) old16 ∗
      pointsTo_u32 ((stackTop - 48) + 20) old20 ∗
      pointsTo_u32 ((stackTop - 48) + 24) old24 ∗
      pointsTo_u32 ((stackTop - 48) + 28) old28 ∗
      allocationPairAt ((stackTop - 16) + 8) oldPairData oldPairSize ∗
      allocationPairAt resultPtr oldResultData oldResultSize ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 48) + 8) data -∗
        pointsTo_u32 ((stackTop - 48) + 12) size -∗
        pointsTo_u32 ((stackTop - 48) + 16) data -∗
        pointsTo_u32 ((stackTop - 48) + 20) data -∗
        pointsTo_u32 ((stackTop - 48) + 24) data -∗
        pointsTo_u32 ((stackTop - 48) + 28) data -∗
        allocationPairAt ((stackTop - 16) + 8) data size -∗
        allocationPairAt resultPtr data size -∗
        allocatorCoreResidueAt size smallMap chunk data nextHeader -∗
        array64At data
          (List.replicate
            (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
              tail).length 0) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 metaPtr, .i32 align, .i32 size],
              [.i32 (stackTop - 16), .i32 1, .i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 metaPtr, .i32 align, .i32 size],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func145, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hw80, hw81, hw82, hw83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hwrapRoom (by decide)
  iintro ⟨Hruntime, Hglobal, H8, H12, H16, H20, H24, H28, Hpair,
    Hresult, Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  have Hprefix := zeroedAllocatorWrapper_to_core_twp (α := α)
    (iprop% runtimeModuleOwn «module» ∗
      pointsTo_u32 ((stackTop - 48) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 48) + 12) old12 ∗
      pointsTo_u32 ((stackTop - 48) + 16) old16 ∗
      pointsTo_u32 ((stackTop - 48) + 20) old20 ∗
      pointsTo_u32 ((stackTop - 48) + 24) old24 ∗
      pointsTo_u32 ((stackTop - 48) + 28) old28 ∗
      allocationPairAt ((stackTop - 16) + 8) oldPairData oldPairSize ∗
      allocationPairAt resultPtr oldResultData oldResultSize ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader)
    resultPtr metaPtr align size stackTop
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hprefix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hruntime H8 H12 H16 H20 H24 H28 Hpair Hresult Hmap Hhead
    HheaderTail Howned HnextHeader]
  · iframe
  iintro Hglobal HR
  icases HR with ⟨Hruntime, H8, H12, H16, H20, H24, H28, Hpair, Hresult,
    Hmap, Hhead, HheaderTail, Howned, HnextHeader⟩
  have Hcore := allocatorResult_singleton_call_twp (α := α)
    ((stackTop - 16) + 8) 1 (stackTop - 16) size align smallMap chunk
    previous data oldHeader nextHeader headerByte tail
    old8 old12 old16 old20 old24 old28 oldPairData oldPairSize
    (by decide) halign hsmall havailable hnonzero hheaderByte hdata
    hdataNonzero hsize hlength hpayloadRoom hheadRoom hchunkLinksRoom
    hchunkRoom hnextRoom
    (by rw [show (stackTop - 16) - 32 = stackTop - 48 by bv_decide]
        exact hcoreRoom)
    (by have h := hw80
        rw [show UInt32.ofNat 8 = (8 : UInt32) from rfl] at h
        rw [h]
        simp only [UInt32.size] at hwrapRoom ⊢
        omega)
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 resultPtr, .i32 metaPtr, .i32 align, .i32 size],
        [.i32 (stackTop - 16), .i32 1, .i32 0], []⟩)
    (stack := [])
    (code := zeroedAllocatorWrapperAfterCall) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
  rw [show (stackTop - 16) - 32 = stackTop - 48 by bv_decide] at Hcore
  simp only [List.cons_append, List.nil_append] at Hcore
  iapply Hcore
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H8]
  · iexact H8
  isplitl [H12]
  · iexact H12
  isplitl [H16]
  · iexact H16
  isplitl [H20]
  · iexact H20
  isplitl [H24]
  · iexact H24
  isplitl [H28]
  · iexact H28
  isplitl [Hpair]
  · isimp only [allocationPairAt]
    isimp only [allocationPairAt] at Hpair
    iexact Hpair
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
  iintro Hruntime Hglobal H8 H12 H16 H20 H24 H28 Hpair Hresidue Harray
  have Hsuffix := zeroedAllocatorWrapper_success_suffix_twp (α := α)
    resultPtr metaPtr align size (stackTop - 16) data
    oldResultData oldResultSize
    (List.replicate
      (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
        tail).length 0)
    hwrapRoom hresultRoom
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hsuffix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hpair]
  · iexact Hpair
  isplitl [Hresult]
  · iexact Hresult
  isplitl [Harray]
  · iexact Harray
  iintro Hglobal Hpair Hresult Harray
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (stackTop - 16) + 16 = stackTop by bv_decide]
    iexact Hglobal
  iapply Hdone $$ Hruntime HglobalTop H8 H12 H16 H20 H24 H28 Hpair
    Hresult Hresidue Harray

/- Absolute-index-147 call rule for the zeroed-allocation wrapper on the
verified singleton path, preserving an arbitrary caller frame. -/
set_option maxHeartbeats 4000000 in
theorem zeroedAllocatorWrapper_singleton_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr metaPtr stackTop : UInt32)
    (size align smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (old8 old12 old16 old20 old24 old28 : UInt32)
    (oldPairData oldPairSize oldResultData oldResultSize : UInt32)
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
    (hwrapRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hcoreRoom : (stackTop - 48).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 48) + 8) old8 ∗
      pointsTo_u32 ((stackTop - 48) + 12) old12 ∗
      pointsTo_u32 ((stackTop - 48) + 16) old16 ∗
      pointsTo_u32 ((stackTop - 48) + 20) old20 ∗
      pointsTo_u32 ((stackTop - 48) + 24) old24 ∗
      pointsTo_u32 ((stackTop - 48) + 28) old28 ∗
      allocationPairAt ((stackTop - 16) + 8) oldPairData oldPairSize ∗
      allocationPairAt resultPtr oldResultData oldResultSize ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 48) + 8) data -∗
        pointsTo_u32 ((stackTop - 48) + 12) size -∗
        pointsTo_u32 ((stackTop - 48) + 16) data -∗
        pointsTo_u32 ((stackTop - 48) + 20) data -∗
        pointsTo_u32 ((stackTop - 48) + 24) data -∗
        pointsTo_u32 ((stackTop - 48) + 28) data -∗
        allocationPairAt ((stackTop - 16) + 8) data size -∗
        allocationPairAt resultPtr data size -∗
        allocatorCoreResidueAt size smallMap chunk data nextHeader -∗
        array64At data
          (List.replicate
            (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
              tail).length 0) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 size, .i32 align, .i32 metaPtr, .i32 resultPtr] ++ stack },
        .call 147 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, H8, H12, H16, H20, H24, H28, Hpair, Hresult,
    Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 147 func145Def
      (by decide) zeroedAllocatorWrapper_index $$ Hruntime
  iintro Hruntime
  simp [func145Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := zeroedAllocatorWrapper_singleton_twp (α := α)
    resultPtr metaPtr stackTop size align smallMap chunk previous data
    oldHeader nextHeader headerByte tail old8 old12 old16 old20 old24
    old28 oldPairData oldPairSize oldResultData oldResultSize
    halign hsmall havailable hnonzero hheaderByte hdata hdataNonzero
    hsize hlength hpayloadRoom hheadRoom hchunkLinksRoom hchunkRoom
    hnextRoom hwrapRoom hcoreRoom hresultRoom
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
  isplitl [H8]
  · iexact H8
  isplitl [H12]
  · iexact H12
  isplitl [H16]
  · iexact H16
  isplitl [H20]
  · iexact H20
  isplitl [H24]
  · iexact H24
  isplitl [H28]
  · iexact H28
  isplitl [Hpair]
  · iexact Hpair
  isplitl [Hresult]
  · iexact Hresult
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
  iintro Hruntime Hglobal H8 H12 H16 H20 H24 H28 Hpair Hresult Hresidue
    Harray
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal H8 H12 H16 H20 H24 H28 Hpair Hresult
    Hresidue Harray

/-! ## Local `func144`: the zeroed-allocation entry point

Local `func144` (absolute index 146) computes the byte size `count * elemSize`
in 64-bit arithmetic, rejects overflow and over-large requests, and forwards
zeroed requests to the wrapper at absolute index 147. -/

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
        .constI64 value :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.constI64)

private theorem twp_extendUI32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues,
          .i64 (UInt64.ofNat value.toNat) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 value :: values⟩,
        .extendUI32 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.extendUI32)

private theorem twp_mulI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs * rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .mulI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.mulI64)

private theorem twp_shrUI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs >>> (rhs % 64)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .shrUI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shrUI64)

private theorem twp_ne_i32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ne :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ne hresult)

def zeroedAllocatorEpilogue : Program :=
  [.localGet 5, .const 48, .add, .globalSet 0, .ret]

def zeroedAllocatorResultSeg : Program :=
  [.localGet 5, .load32 40, .localSet 17,
    .localGet 0, .localGet 1, .store32 4,
    .localGet 0, .localGet 17, .store32 8,
    .localGet 0, .const 0, .store32 0,
    .br 1]

def zeroedAllocatorSelectBody : Program :=
  [.const 0, .localGet 16, .localGet 15, .select,
    .const 1, .and, .eqz, .br_if 0,
    .localGet 0, .localGet 9, .store32 4,
    .localGet 0, .localGet 10, .store32 8,
    .localGet 0, .const 1, .store32 0,
    .br 1]

def zeroedAllocatorSelectSeg : Program :=
  [.localGet 5, .load32 40, .localSet 15,
    .const 1, .localSet 16,
    .block 0 0 zeroedAllocatorSelectBody] ++ zeroedAllocatorResultSeg

def zeroedAllocatorAfterWrapperCall : Program :=
  [.localGet 5, .load32 12, .localSet 13,
    .localGet 5, .localGet 5, .load32 8, .store32 40,
    .localGet 5, .localGet 13, .store32 44,
    .br 1]

def zeroedAllocatorUninitSeg : Program :=
  [.localGet 5, .const 16, .add,
    .localGet 5, .const 27, .add,
    .localGet 9, .localGet 10, .call 148,
    .localGet 5, .load32 20, .localSet 14,
    .localGet 5, .localGet 5, .load32 16, .store32 40,
    .localGet 5, .localGet 14, .store32 44]

def zeroedAllocatorZeroedBody : Program :=
  [.localGet 2, .const 1, .and, .eqz, .br_if 0,
    .localGet 5, .const 8, .add,
    .localGet 5, .const 27, .add,
    .localGet 9, .localGet 10, .call 147] ++
    zeroedAllocatorAfterWrapperCall

def zeroedAllocatorInnerAllocBody : Program :=
  .block 0 0 zeroedAllocatorZeroedBody :: zeroedAllocatorUninitSeg

def zeroedAllocatorAllocSeg : Program :=
  .block 0 0 zeroedAllocatorInnerAllocBody :: zeroedAllocatorSelectSeg

def zeroedAllocatorZeroSizeSeg : Program :=
  [.localGet 0, .const 0, .store32 4,
    .localGet 0, .localGet 3, .store32 8,
    .localGet 0, .const 0, .store32 0,
    .br 2]

def zeroedAllocatorErrorSeg : Program :=
  [.const 0, .load32 1050408, .localSet 11,
    .const 0, .load32 1050412, .localSet 12,
    .localGet 0, .localGet 11, .store32 4,
    .localGet 0, .localGet 12, .store32 8,
    .localGet 0, .const 1, .store32 0,
    .br 2]

def zeroedAllocatorFitsSeg : Program :=
  [.localGet 5, .localGet 3, .store32 32,
    .localGet 5, .localGet 8, .store32 36,
    .localGet 5, .const 0, .store32 28,
    .localGet 5, .load32 32, .localSet 9,
    .localGet 5, .load32 36, .localSet 10,
    .localGet 10, .eqz, .br_if 1, .br 2]

def zeroedAllocatorGuardBody : Program :=
  [.localGet 7, .const 1, .and, .br_if 0,
    .localGet 8, .const 2147483648, .localGet 3, .sub, .leU,
    .const 1, .and, .br_if 2, .br 1]

def zeroedAllocatorGuardOuter1 : Program :=
  [.block 0 0 zeroedAllocatorGuardBody, .br 2]

def zeroedAllocatorGuardOuter2 : Program :=
  [.block 0 0 zeroedAllocatorGuardOuter1, .br 1]

def zeroedAllocatorFitsBody : Program :=
  .block 0 0 zeroedAllocatorGuardOuter2 :: zeroedAllocatorFitsSeg

def zeroedAllocatorErrorBody : Program :=
  .block 0 0 zeroedAllocatorFitsBody :: zeroedAllocatorErrorSeg

def zeroedAllocatorZeroSizeBody : Program :=
  .block 0 0 zeroedAllocatorErrorBody :: zeroedAllocatorZeroSizeSeg

def zeroedAllocatorMainBody : Program :=
  .block 0 0 zeroedAllocatorZeroSizeBody :: zeroedAllocatorAllocSeg

def zeroedAllocatorTopBody : Program :=
  [.block 0 0 zeroedAllocatorMainBody]

private theorem func144_shape :
    func144 =
      [.globalGet 0, .const 48, .sub, .localSet 5,
        .localGet 5, .globalSet 0,
        .localGet 1, .extendUI32, .localGet 4, .extendUI32, .mulI64,
        .localSet 6,
        .localGet 6, .constI64 32, .shrUI64, .wrapI64, .const 0, .ne,
        .localSet 7,
        .localGet 6, .wrapI64, .localSet 8,
        .block 0 0 zeroedAllocatorTopBody] ++ zeroedAllocatorEpilogue := by
  rfl

def zeroedAllocatorFrameLocals
    (frame : UInt32) (prod : UInt64) (size align : UInt32) : List Value :=
  [.i32 frame, .i64 prod, .i32 0, .i32 size, .i32 align, .i32 size,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

def zeroedAllocatorZeroedFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := zeroedAllocatorZeroedBody
    continuation := zeroedAllocatorUninitSeg
    belowStack := [] }

def zeroedAllocatorInnerAllocFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := zeroedAllocatorInnerAllocBody
    continuation := zeroedAllocatorSelectSeg
    belowStack := [] }

def zeroedAllocatorMainFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := zeroedAllocatorMainBody
    continuation := []
    belowStack := [] }

def zeroedAllocatorTopFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := zeroedAllocatorTopBody
    continuation := zeroedAllocatorEpilogue
    belowStack := [] }

/- Pure prefix of local `func144`: reserve the 48-byte frame, perform the
64-bit size computation, pass the generated overflow and size-class guards,
record the accepted request in the frame, and stop exactly at the
absolute-index-147 wrapper call of the zeroed branch. -/
set_option maxHeartbeats 4000000 in
theorem zeroedAllocator_to_wrapper_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (resultPtr count flags align elemSize size stackTop : UInt32)
    (prod : UInt64)
    (old28 old32 old36 : UInt32)
    (hprod : UInt64.ofNat count.toNat * UInt64.ofNat elemSize.toNat = prod)
    (hlow : UInt32.ofNat (prod.toNat % 2 ^ 32) = size)
    (hhigh : UInt32.ofNat
      ((prod >>> ((32 : UInt64) % 64)).toNat % 2 ^ 32) = 0)
    (hfits : size ≤ 2147483648 - align)
    (hsizeNonzero : size ≠ 0)
    (hflags : flags &&& 1 ≠ 0)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 48) + 28) old28 ∗
      pointsTo_u32 ((stackTop - 48) + 32) old32 ∗
      pointsTo_u32 ((stackTop - 48) + 36) old36 ∗ R ∗
      (globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        pointsTo_u32 ((stackTop - 48) + 28) 0 -∗
        pointsTo_u32 ((stackTop - 48) + 32) align -∗
        pointsTo_u32 ((stackTop - 48) + 36) size -∗ R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 count, .i32 flags, .i32 align,
              .i32 elemSize],
              zeroedAllocatorFrameLocals (stackTop - 48) prod size align,
              [.i32 size, .i32 align, .i32 ((stackTop - 48) + 27),
                .i32 ((stackTop - 48) + 8)]⟩,
            .call 147 :: zeroedAllocatorAfterWrapperCall, 0, [],
            [zeroedAllocatorZeroedFrame, zeroedAllocatorInnerAllocFrame,
              zeroedAllocatorMainFrame, zeroedAllocatorTopFrame],
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 count, .i32 flags, .i32 align,
          .i32 elemSize],
          [.i32 0, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
            .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func144, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf280, hf281, hf282, hf283⟩ :=
    descriptorSlot32Facts (stackTop - 48) 28 48 hframeRoom (by decide)
  obtain ⟨hf320, hf321, hf322, hf323⟩ :=
    descriptorSlot32Facts (stackTop - 48) 32 48 hframeRoom (by decide)
  obtain ⟨hf360, hf361, hf362, hf363⟩ :=
    descriptorSlot32Facts (stackTop - 48) 36 48 hframeRoom (by decide)
  iintro ⟨Hglobal, H28, H32, H36, HR, Hdone⟩
  rw [func144_shape]
  simp only [List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_extendUI32
  iapply twp_localGet rfl
  iapply twp_extendUI32
  iapply twp_mulI64
  rw [hprod]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_shrUI64
  iapply twp_wrapI64
  rw [hhigh]
  iapply twp_const
  iapply twp_ne_i32 (result := 0) (by simp)
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_wrapI64
  rw [hlow]
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [zeroedAllocatorTopBody]
  iapply twp_block
  simp only [zeroedAllocatorMainBody]
  iapply twp_block
  simp only [zeroedAllocatorZeroSizeBody]
  iapply twp_block
  simp only [zeroedAllocatorErrorBody]
  iapply twp_block
  simp only [zeroedAllocatorFitsBody]
  iapply twp_block
  simp only [zeroedAllocatorGuardOuter2]
  iapply twp_block
  simp only [zeroedAllocatorGuardOuter1]
  iapply twp_block
  simp only [zeroedAllocatorGuardBody]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_leU (result := 1) (by simp [hfits])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  simp only [zeroedAllocatorFitsSeg]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old32 hf320 hf321 hf322 hf323 $$ H32
  iintro H32
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old36 hf360 hf361 hf362 hf363 $$ H36
  iintro H36
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old28 hf280 hf281 hf282 hf283 $$ H28
  iintro H28
  iapply twp_localGet rfl
  iapply twp_load32 align hf320 hf321 hf322 hf323 $$ H32
  iintro H32
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_load32 size hf360 hf361 hf362 hf363 $$ H36
  iintro H36
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [hsizeNonzero])
  iapply twp_brIfZero
  iapply twp_br (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  simp only [zeroedAllocatorAllocSeg]
  iapply twp_block
  simp only [zeroedAllocatorInnerAllocBody]
  iapply twp_block
  simp only [zeroedAllocatorZeroedBody]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  iapply twp_eqz (result := 0) (by simp [hflags])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (8 : UInt32) (stackTop - 48)]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (27 : UInt32) (stackTop - 48)]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  isimp only [zeroedAllocatorZeroedFrame, zeroedAllocatorInnerAllocFrame,
    zeroedAllocatorMainFrame, zeroedAllocatorTopFrame,
    zeroedAllocatorZeroedBody, zeroedAllocatorInnerAllocBody,
    zeroedAllocatorMainBody, zeroedAllocatorTopBody,
    zeroedAllocatorZeroSizeBody, zeroedAllocatorErrorBody,
    zeroedAllocatorFitsBody, zeroedAllocatorGuardOuter2,
    zeroedAllocatorGuardOuter1, zeroedAllocatorGuardBody,
    zeroedAllocatorFitsSeg, zeroedAllocatorErrorSeg,
    zeroedAllocatorZeroSizeSeg, zeroedAllocatorAllocSeg,
    zeroedAllocatorSelectSeg, zeroedAllocatorSelectBody,
    zeroedAllocatorResultSeg, zeroedAllocatorUninitSeg,
    zeroedAllocatorAfterWrapperCall, zeroedAllocatorEpilogue,
    zeroedAllocatorFrameLocals,
    List.cons_append, List.nil_append] at Hdone
  simp only [zeroedAllocatorErrorSeg, zeroedAllocatorZeroSizeSeg,
    zeroedAllocatorSelectSeg, zeroedAllocatorSelectBody,
    zeroedAllocatorResultSeg, zeroedAllocatorUninitSeg,
    zeroedAllocatorAfterWrapperCall, zeroedAllocatorEpilogue,
    List.cons_append, List.nil_append, List.drop_zero]
  iapply Hdone $$ Hglobal H28 H32 H36 HR

/- Exact successful suffix of local `func144` after the wrapper has returned
the `(data, size)` pair in the frame: publish the pair through the frame's
result words, pass the generated null check, and write the three-word success
descriptor `(0, count, data)` into the caller-supplied result slot. -/
set_option maxHeartbeats 4000000 in
theorem zeroedAllocator_success_suffix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count flags align elemSize size frame data : UInt32)
    (prod : UInt64)
    (old40 old44 oldR0 oldR4 oldR8 : UInt32)
    (hframeRoom : frame.toNat + 48 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    (hdataNonzero : data ≠ 0)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      allocationPairAt (frame + 8) data size ∗
      pointsTo_u32 (frame + 40) old40 ∗
      pointsTo_u32 (frame + 44) old44 ∗
      pointsTo_u32 resultPtr oldR0 ∗
      pointsTo_u32 (resultPtr + 4) oldR4 ∗
      pointsTo_u32 (resultPtr + 8) oldR8 ∗
      (globalPointsTo 0 (.i32 (frame + 48)) -∗
        allocationPairAt (frame + 8) data size -∗
        pointsTo_u32 (frame + 40) data -∗
        pointsTo_u32 (frame + 44) size -∗
        pointsTo_u32 resultPtr 0 -∗
        pointsTo_u32 (resultPtr + 4) count -∗
        pointsTo_u32 (resultPtr + 8) data -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 count, .i32 flags, .i32 align,
              .i32 elemSize],
              [.i32 frame, .i64 prod, .i32 0, .i32 size, .i32 align,
                .i32 size, .i32 0, .i32 0, .i32 size, .i32 0, .i32 data,
                .i32 1, .i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 count, .i32 flags, .i32 align,
          .i32 elemSize],
          zeroedAllocatorFrameLocals frame prod size align, []⟩,
        zeroedAllocatorAfterWrapperCall, 0, [],
        [zeroedAllocatorZeroedFrame, zeroedAllocatorInnerAllocFrame,
          zeroedAllocatorMainFrame, zeroedAllocatorTopFrame],
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 48 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 48 hframeRoom (by decide)
  obtain ⟨hf400, hf401, hf402, hf403⟩ :=
    descriptorSlot32Facts frame 40 48 hframeRoom (by decide)
  obtain ⟨hf440, hf441, hf442, hf443⟩ :=
    descriptorSlot32Facts frame 44 48 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    descriptorSlot32Facts resultPtr 0 12 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 12 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    descriptorSlot32Facts resultPtr 8 12 hresultRoom (by decide)
  iintro ⟨Hglobal, Hpair, H40, H44, Hr0, Hr4, Hr8, Hdone⟩
  isimp only [allocationPairAt] at Hpair
  icases Hpair with ⟨Hp8, Hp12⟩
  simp only [zeroedAllocatorAfterWrapperCall, zeroedAllocatorFrameLocals]
  iapply twp_localGet rfl
  ihave Hp12At : pointsTo_u32 (frame + 12) size $$ [Hp12]
  · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
    iexact Hp12
  iapply twp_load32 size hf120 hf121 hf122 hf123 $$ Hp12At
  iintro Hp12At
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 data hf80 hf81 hf82 hf83 $$ Hp8
  iintro Hp8
  iapply twp_store32 old40 hf400 hf401 hf402 hf403 $$ H40
  iintro H40
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old44 hf440 hf441 hf442 hf443 $$ H44
  iintro H44
  iapply twp_br (by rfl)
  simp only [zeroedAllocatorInnerAllocFrame, zeroedAllocatorSelectSeg,
    List.take_zero, List.nil_append, List.cons_append]
  iapply twp_localGet rfl
  iapply twp_load32 data hf400 hf401 hf402 hf403 $$ H40
  iintro H40
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [zeroedAllocatorSelectBody]
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 0) (by simp [hdataNonzero])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  simp only [zeroedAllocatorResultSeg]
  iapply twp_localGet rfl
  iapply twp_load32 data hf400 hf401 hf402 hf403 $$ H40
  iintro H40
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldR4 hr40 hr41 hr42 hr43 $$ Hr4
  iintro Hr4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldR8 hr80 hr81 hr82 hr83 $$ Hr8
  iintro Hr8
  iapply twp_localGet rfl
  iapply twp_const
  ihave Hr0At : pointsTo_u32 (resultPtr + 0) oldR0 $$ [Hr0]
  · iapply pointsTo_u32_add_zero
    iexact Hr0
  iapply twp_store32 oldR0 hr0 hr1 hr2 hr3 $$ Hr0At
  iintro Hr0At
  iapply twp_br (by rfl)
  simp only [zeroedAllocatorTopFrame, zeroedAllocatorEpilogue,
    List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (48 : UInt32) frame]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave Hr0 : pointsTo_u32 resultPtr 0 $$ [Hr0At]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact Hr0At
  ihave Hpair : allocationPairAt (frame + 8) data size $$ [Hp8 Hp12At]
  · isimp only [allocationPairAt]
    isplitl [Hp8]
    · iexact Hp8
    · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
      iexact Hp12At
  iapply Hdone $$ Hglobal Hpair H40 H44 Hr0 Hr4 Hr8

/- Complete singleton-path body rule for local `func144`: size computation,
guards, the verified wrapper chain at absolute index 147, and the success
descriptor suffix, composed into one closed contract. -/
set_option maxHeartbeats 4000000 in
theorem zeroedAllocator_singleton_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count flags align elemSize stackTop : UInt32)
    (prod : UInt64)
    (size smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (old28 old32 old36 old40 old44 : UInt32)
    (oldPair8 oldPair12 oldWrap8 oldWrap12 : UInt32)
    (oldCore8 oldCore12 oldCore16 oldCore20 oldCore24 oldCore28 : UInt32)
    (oldR0 oldR4 oldR8 : UInt32)
    (hprod : UInt64.ofNat count.toNat * UInt64.ofNat elemSize.toNat = prod)
    (hlow : UInt32.ofNat (prod.toNat % 2 ^ 32) = size)
    (hhigh : UInt32.ofNat
      ((prod >>> ((32 : UInt64) % 64)).toNat % 2 ^ 32) = 0)
    (hfits : size ≤ 2147483648 - align)
    (hflags : flags &&& 1 ≠ 0)
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
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    (hwrapRoom : (stackTop - 64).toNat + 16 ≤ UInt32.size)
    (hcoreRoom : (stackTop - 96).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 48) + 28) old28 ∗
      pointsTo_u32 ((stackTop - 48) + 32) old32 ∗
      pointsTo_u32 ((stackTop - 48) + 36) old36 ∗
      pointsTo_u32 ((stackTop - 48) + 40) old40 ∗
      pointsTo_u32 ((stackTop - 48) + 44) old44 ∗
      allocationPairAt ((stackTop - 48) + 8) oldPair8 oldPair12 ∗
      allocationPairAt ((stackTop - 64) + 8) oldWrap8 oldWrap12 ∗
      pointsTo_u32 ((stackTop - 96) + 8) oldCore8 ∗
      pointsTo_u32 ((stackTop - 96) + 12) oldCore12 ∗
      pointsTo_u32 ((stackTop - 96) + 16) oldCore16 ∗
      pointsTo_u32 ((stackTop - 96) + 20) oldCore20 ∗
      pointsTo_u32 ((stackTop - 96) + 24) oldCore24 ∗
      pointsTo_u32 ((stackTop - 96) + 28) oldCore28 ∗
      pointsTo_u32 resultPtr oldR0 ∗
      pointsTo_u32 (resultPtr + 4) oldR4 ∗
      pointsTo_u32 (resultPtr + 8) oldR8 ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 48) + 28) 0 -∗
        pointsTo_u32 ((stackTop - 48) + 32) align -∗
        pointsTo_u32 ((stackTop - 48) + 36) size -∗
        pointsTo_u32 ((stackTop - 48) + 40) data -∗
        pointsTo_u32 ((stackTop - 48) + 44) size -∗
        allocationPairAt ((stackTop - 48) + 8) data size -∗
        allocationPairAt ((stackTop - 64) + 8) data size -∗
        pointsTo_u32 ((stackTop - 96) + 8) data -∗
        pointsTo_u32 ((stackTop - 96) + 12) size -∗
        pointsTo_u32 ((stackTop - 96) + 16) data -∗
        pointsTo_u32 ((stackTop - 96) + 20) data -∗
        pointsTo_u32 ((stackTop - 96) + 24) data -∗
        pointsTo_u32 ((stackTop - 96) + 28) data -∗
        pointsTo_u32 resultPtr 0 -∗
        pointsTo_u32 (resultPtr + 4) count -∗
        pointsTo_u32 (resultPtr + 8) data -∗
        allocatorCoreResidueAt size smallMap chunk data nextHeader -∗
        array64At data
          (List.replicate
            (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
              tail).length 0) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 count, .i32 flags, .i32 align,
              .i32 elemSize],
              [.i32 (stackTop - 48), .i64 prod, .i32 0, .i32 size,
                .i32 align, .i32 size, .i32 0, .i32 0, .i32 size, .i32 0,
                .i32 data, .i32 1, .i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 count, .i32 flags, .i32 align,
          .i32 elemSize],
          [.i32 0, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
            .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func144, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hp80, hp81, hp82, hp83⟩ :=
    descriptorSlot32Facts (stackTop - 48) 8 48 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, H28, H32, H36, H40, H44, Hpair, Hwrap,
    Hc8, Hc12, Hc16, Hc20, Hc24, Hc28, Hr0, Hr4, Hr8,
    Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  have Hprefix := zeroedAllocator_to_wrapper_twp (α := α)
    (iprop% runtimeModuleOwn «module» ∗
      pointsTo_u32 ((stackTop - 48) + 40) old40 ∗
      pointsTo_u32 ((stackTop - 48) + 44) old44 ∗
      allocationPairAt ((stackTop - 48) + 8) oldPair8 oldPair12 ∗
      allocationPairAt ((stackTop - 64) + 8) oldWrap8 oldWrap12 ∗
      pointsTo_u32 ((stackTop - 96) + 8) oldCore8 ∗
      pointsTo_u32 ((stackTop - 96) + 12) oldCore12 ∗
      pointsTo_u32 ((stackTop - 96) + 16) oldCore16 ∗
      pointsTo_u32 ((stackTop - 96) + 20) oldCore20 ∗
      pointsTo_u32 ((stackTop - 96) + 24) oldCore24 ∗
      pointsTo_u32 ((stackTop - 96) + 28) oldCore28 ∗
      pointsTo_u32 resultPtr oldR0 ∗
      pointsTo_u32 (resultPtr + 4) oldR4 ∗
      pointsTo_u32 (resultPtr + 8) oldR8 ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader)
    resultPtr count flags align elemSize size stackTop prod
    old28 old32 old36 hprod hlow hhigh hfits hsize hflags hframeRoom
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hprefix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H28]
  · iexact H28
  isplitl [H32]
  · iexact H32
  isplitl [H36]
  · iexact H36
  isplitl [Hruntime H40 H44 Hpair Hwrap Hc8 Hc12 Hc16 Hc20 Hc24 Hc28
    Hr0 Hr4 Hr8 Hmap Hhead HheaderTail Howned HnextHeader]
  · iframe
  iintro Hglobal H28 H32 H36 HR
  icases HR with ⟨Hruntime, H40, H44, Hpair, Hwrap, Hc8, Hc12, Hc16,
    Hc20, Hc24, Hc28, Hr0, Hr4, Hr8, Hmap, Hhead, HheaderTail, Howned,
    HnextHeader⟩
  have Hwrapper := zeroedAllocatorWrapper_singleton_call_twp (α := α)
    ((stackTop - 48) + 8) ((stackTop - 48) + 27) (stackTop - 48)
    size align smallMap chunk previous data oldHeader nextHeader
    headerByte tail oldCore8 oldCore12 oldCore16 oldCore20 oldCore24
    oldCore28 oldWrap8 oldWrap12 oldPair8 oldPair12
    halign hsmall havailable hnonzero hheaderByte hdata hdataNonzero
    hsize hlength hpayloadRoom hheadRoom hchunkLinksRoom hchunkRoom
    hnextRoom
    (by rw [show (stackTop - 48) - 16 = stackTop - 64 by bv_decide]
        exact hwrapRoom)
    (by rw [show (stackTop - 48) - 48 = stackTop - 96 by bv_decide]
        exact hcoreRoom)
    (by have h := hp80
        rw [show UInt32.ofNat 8 = (8 : UInt32) from rfl] at h
        rw [h]
        simp only [UInt32.size] at hframeRoom ⊢
        omega)
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 resultPtr, .i32 count, .i32 flags, .i32 align,
          .i32 elemSize],
        zeroedAllocatorFrameLocals (stackTop - 48) prod size align, []⟩)
    (stack := [])
    (code := zeroedAllocatorAfterWrapperCall) (arity := 0)
    (remainder := [])
    (controls :=
      [zeroedAllocatorZeroedFrame, zeroedAllocatorInnerAllocFrame,
        zeroedAllocatorMainFrame, zeroedAllocatorTopFrame])
    (calls := calls)
  rw [show (stackTop - 48) - 16 = stackTop - 64 by bv_decide,
    show (stackTop - 48) - 48 = stackTop - 96 by bv_decide] at Hwrapper
  simp only [List.cons_append, List.nil_append] at Hwrapper
  iapply Hwrapper
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hc8]
  · iexact Hc8
  isplitl [Hc12]
  · iexact Hc12
  isplitl [Hc16]
  · iexact Hc16
  isplitl [Hc20]
  · iexact Hc20
  isplitl [Hc24]
  · iexact Hc24
  isplitl [Hc28]
  · iexact Hc28
  isplitl [Hwrap]
  · iexact Hwrap
  isplitl [Hpair]
  · iexact Hpair
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
  iintro Hruntime Hglobal Hc8 Hc12 Hc16 Hc20 Hc24 Hc28 Hwrap Hpair
    Hresidue Harray
  have Hsuffix := zeroedAllocator_success_suffix_twp (α := α)
    resultPtr count flags align elemSize size (stackTop - 48) data prod
    old40 old44 oldR0 oldR4 oldR8 hframeRoom hresultRoom hdataNonzero
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hsuffix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hpair]
  · iexact Hpair
  isplitl [H40]
  · iexact H40
  isplitl [H44]
  · iexact H44
  isplitl [Hr0]
  · iexact Hr0
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  iintro Hglobal Hpair H40 H44 Hr0 Hr4 Hr8
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (stackTop - 48) + 48 = stackTop by bv_decide]
    iexact Hglobal
  iapply Hdone $$ Hruntime HglobalTop H28 H32 H36 H40 H44 Hpair Hwrap
    Hc8 Hc12 Hc16 Hc20 Hc24 Hc28 Hr0 Hr4 Hr8 Hresidue Harray

/- Absolute-index-146 call rule for the zeroed-allocation entry point on the
verified singleton path, preserving an arbitrary caller frame.  This is the
call boundary consumed by `Vec<u64>::from_elem` and by the iterator
collection chain. -/
set_option maxHeartbeats 4000000 in
theorem zeroedAllocator_singleton_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count flags align elemSize stackTop : UInt32)
    (prod : UInt64)
    (size smallMap chunk previous data oldHeader nextHeader : UInt32)
    (headerByte : UInt8) (tail : List UInt64)
    (old28 old32 old36 old40 old44 : UInt32)
    (oldPair8 oldPair12 oldWrap8 oldWrap12 : UInt32)
    (oldCore8 oldCore12 oldCore16 oldCore20 oldCore24 oldCore28 : UInt32)
    (oldR0 oldR4 oldR8 : UInt32)
    (hprod : UInt64.ofNat count.toNat * UInt64.ofNat elemSize.toNat = prod)
    (hlow : UInt32.ofNat (prod.toNat % 2 ^ 32) = size)
    (hhigh : UInt32.ofNat
      ((prod >>> ((32 : UInt64) % 64)).toNat % 2 ^ 32) = 0)
    (hfits : size ≤ 2147483648 - align)
    (hflags : flags &&& 1 ≠ 0)
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
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    (hwrapRoom : (stackTop - 64).toNat + 16 ≤ UInt32.size)
    (hcoreRoom : (stackTop - 96).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 48) + 28) old28 ∗
      pointsTo_u32 ((stackTop - 48) + 32) old32 ∗
      pointsTo_u32 ((stackTop - 48) + 36) old36 ∗
      pointsTo_u32 ((stackTop - 48) + 40) old40 ∗
      pointsTo_u32 ((stackTop - 48) + 44) old44 ∗
      allocationPairAt ((stackTop - 48) + 8) oldPair8 oldPair12 ∗
      allocationPairAt ((stackTop - 64) + 8) oldWrap8 oldWrap12 ∗
      pointsTo_u32 ((stackTop - 96) + 8) oldCore8 ∗
      pointsTo_u32 ((stackTop - 96) + 12) oldCore12 ∗
      pointsTo_u32 ((stackTop - 96) + 16) oldCore16 ∗
      pointsTo_u32 ((stackTop - 96) + 20) oldCore20 ∗
      pointsTo_u32 ((stackTop - 96) + 24) oldCore24 ∗
      pointsTo_u32 ((stackTop - 96) + 28) oldCore28 ∗
      pointsTo_u32 resultPtr oldR0 ∗
      pointsTo_u32 (resultPtr + 4) oldR4 ∗
      pointsTo_u32 (resultPtr + 8) oldR8 ∗
      pointsTo_u32 1056608 smallMap ∗
      pointsTo_u32 (smallAllocatorBinHeadAddress size smallMap) chunk ∗
      headerWordTailAt (data + 4294967292) oldHeader ∗
      dlmallocOwnedResult data headerByte
        (packU32 (smallAllocatorBinSentinel size smallMap) previous :: tail) ∗
      pointsTo_u32 (smallAllocatorNextChunk size smallMap chunk + 4)
        nextHeader ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 48) + 28) 0 -∗
        pointsTo_u32 ((stackTop - 48) + 32) align -∗
        pointsTo_u32 ((stackTop - 48) + 36) size -∗
        pointsTo_u32 ((stackTop - 48) + 40) data -∗
        pointsTo_u32 ((stackTop - 48) + 44) size -∗
        allocationPairAt ((stackTop - 48) + 8) data size -∗
        allocationPairAt ((stackTop - 64) + 8) data size -∗
        pointsTo_u32 ((stackTop - 96) + 8) data -∗
        pointsTo_u32 ((stackTop - 96) + 12) size -∗
        pointsTo_u32 ((stackTop - 96) + 16) data -∗
        pointsTo_u32 ((stackTop - 96) + 20) data -∗
        pointsTo_u32 ((stackTop - 96) + 24) data -∗
        pointsTo_u32 ((stackTop - 96) + 28) data -∗
        pointsTo_u32 resultPtr 0 -∗
        pointsTo_u32 (resultPtr + 4) count -∗
        pointsTo_u32 (resultPtr + 8) data -∗
        allocatorCoreResidueAt size smallMap chunk data nextHeader -∗
        array64At data
          (List.replicate
            (packU32 (smallAllocatorBinSentinel size smallMap) previous ::
              tail).length 0) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 elemSize, .i32 align, .i32 flags, .i32 count,
            .i32 resultPtr] ++ stack },
        .call 146 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, H28, H32, H36, H40, H44, Hpair, Hwrap,
    Hc8, Hc12, Hc16, Hc20, Hc24, Hc28, Hr0, Hr4, Hr8,
    Hmap, Hhead, HheaderTail, Howned, HnextHeader, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 146 func144Def
      (by decide) zeroedAllocator_index $$ Hruntime
  iintro Hruntime
  simp [func144Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := zeroedAllocator_singleton_twp (α := α)
    resultPtr count flags align elemSize stackTop prod size smallMap
    chunk previous data oldHeader nextHeader headerByte tail
    old28 old32 old36 old40 old44 oldPair8 oldPair12 oldWrap8 oldWrap12
    oldCore8 oldCore12 oldCore16 oldCore20 oldCore24 oldCore28
    oldR0 oldR4 oldR8
    hprod hlow hhigh hfits hflags halign hsmall havailable hnonzero
    hheaderByte hdata hdataNonzero hsize hlength hpayloadRoom hheadRoom
    hchunkLinksRoom hchunkRoom hnextRoom hframeRoom hwrapRoom hcoreRoom
    hresultRoom
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
  isplitl [H28]
  · iexact H28
  isplitl [H32]
  · iexact H32
  isplitl [H36]
  · iexact H36
  isplitl [H40]
  · iexact H40
  isplitl [H44]
  · iexact H44
  isplitl [Hpair]
  · iexact Hpair
  isplitl [Hwrap]
  · iexact Hwrap
  isplitl [Hc8]
  · iexact Hc8
  isplitl [Hc12]
  · iexact Hc12
  isplitl [Hc16]
  · iexact Hc16
  isplitl [Hc20]
  · iexact Hc20
  isplitl [Hc24]
  · iexact Hc24
  isplitl [Hc28]
  · iexact Hc28
  isplitl [Hr0]
  · iexact Hr0
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
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
  iintro Hruntime Hglobal H28 H32 H36 H40 H44 Hpair Hwrap Hc8 Hc12 Hc16
    Hc20 Hc24 Hc28 Hr0 Hr4 Hr8 Hresidue Harray
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal H28 H32 H36 H40 H44 Hpair Hwrap Hc8
    Hc12 Hc16 Hc20 Hc24 Hc28 Hr0 Hr4 Hr8 Hresidue Harray

end Project.Mergesort.AllocatorProof
