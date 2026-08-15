import Project.Mergesort.VectorProof
import Project.Mergesort.SplitAtProof
import Project.Mergesort.RangeProof

/-!
# Generated output-vector iterator construction

Exact total rules for `func123`, the unchanged generated
`Vec<u64>::into_iter` implementation, and its absolute-index call boundary.
-/

namespace Project.Mergesort.OutputIteratorProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.VectorProof
open Project.Mergesort.SplitAtProof

def intoIterDescriptorAt [WasmHeapGS]
    (base allocation current capacity finish : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 base allocation ∗
    pointsTo_u32 (base + 4) current ∗
    pointsTo_u32 (base + 8) capacity ∗
    pointsTo_u32 (base + 12) finish

private theorem slot32Facts (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 4 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega),
    by simpa using hstep 3 (by omega)⟩

private theorem slot64Facts (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 8 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 ∧
    ((base + UInt32.ofNat offset) + 4).toNat =
      (base + UInt32.ofNat offset).toNat + 4 ∧
    ((base + UInt32.ofNat offset) + 5).toNat =
      (base + UInt32.ofNat offset).toNat + 5 ∧
    ((base + UInt32.ofNat offset) + 6).toNat =
      (base + UInt32.ofNat offset).toNat + 6 ∧
    ((base + UInt32.ofNat offset) + 7).toNat =
      (base + UInt32.ofNat offset).toNat + 7 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 7) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega),
    by simpa using hstep 3 (by omega),
    by simpa using hstep 4 (by omega),
    by simpa using hstep 5 (by omega),
    by simpa using hstep 6 (by omega),
    by simpa using hstep 7 (by omega)⟩

private theorem sliceDescriptorAt_intro [WasmHeapGS]
    (base low high : UInt32) :
    pointsTo_u32 base low ∗ pointsTo_u32 (base + 4) high ⊢
      sliceDescriptorAt base low high := by
  rw [sliceDescriptorAt]

private theorem pointsTo_u64_add_zero [WasmHeapGS]
    (base : UInt32) (value : UInt64) :
    pointsTo_u64 base value ⊢ pointsTo_u64 (base + 0) value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u32_add_zero [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 base value ⊢ pointsTo_u32 (base + 0) value := by
  rw [UInt32.add_zero]

/- Exact body rule for generated local `func123`, `Vec<u64>::into_iter`. -/
set_option maxHeartbeats 6000000 in
theorem vecIntoIter_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr vecPtr capacity data length stackTop : UInt32)
    (oldFrame8 oldFrame12 oldFrame16 oldFrame24 oldFrame28
      oldFrame32 oldFrame36 oldFrame40 : UInt32)
    (oldResult0 oldResult4 oldResult8 oldResult12 : UInt32)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    (hvecRoom : vecPtr.toNat + 12 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      vecDescriptorAt vecPtr capacity data length ∗
      sliceDescriptorAt ((stackTop - 48) + 8) oldFrame8 oldFrame12 ∗
      pointsTo_u32 ((stackTop - 48) + 16) oldFrame16 ∗
      pointsTo_u32 ((stackTop - 48) + 24) oldFrame24 ∗
      pointsTo_u32 ((stackTop - 48) + 28) oldFrame28 ∗
      sliceDescriptorAt ((stackTop - 48) + 32) oldFrame32 oldFrame36 ∗
      pointsTo_u32 ((stackTop - 48) + 40) oldFrame40 ∗
      intoIterDescriptorAt resultPtr oldResult0 oldResult4
        oldResult8 oldResult12 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        vecDescriptorAt vecPtr capacity data length -∗
        sliceDescriptorAt ((stackTop - 48) + 8) capacity data -∗
        pointsTo_u32 ((stackTop - 48) + 16) length -∗
        pointsTo_u32 ((stackTop - 48) + 24)
          (data + (length <<< 3)) -∗
        pointsTo_u32 ((stackTop - 48) + 28) capacity -∗
        sliceDescriptorAt ((stackTop - 48) + 32) capacity data -∗
        pointsTo_u32 ((stackTop - 48) + 40) length -∗
        intoIterDescriptorAt resultPtr data data capacity
          (data + (length <<< 3)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 vecPtr],
              [.i32 (stackTop - 48), .i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 vecPtr], [.i32 0, .i32 0], []⟩,
        func123, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 48
  obtain ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩ :=
    slot64Facts vecPtr 0 12 hvecRoom (by decide)
  obtain ⟨hvl0, hvl1, hvl2, hvl3⟩ :=
    slot32Facts vecPtr 8 12 hvecRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83, hf84, hf85, hf86, hf87⟩ :=
    slot64Facts frame 8 48 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    slot32Facts frame 12 48 hframeRoom (by decide)
  obtain ⟨hf160, hf161, hf162, hf163⟩ :=
    slot32Facts frame 16 48 hframeRoom (by decide)
  obtain ⟨hf240, hf241, hf242, hf243⟩ :=
    slot32Facts frame 24 48 hframeRoom (by decide)
  obtain ⟨hf280, hf281, hf282, hf283⟩ :=
    slot32Facts frame 28 48 hframeRoom (by decide)
  obtain ⟨hf320, hf321, hf322, hf323, hf324, hf325, hf326, hf327⟩ :=
    slot64Facts frame 32 48 hframeRoom (by decide)
  obtain ⟨hf400, hf401, hf402, hf403⟩ :=
    slot32Facts frame 40 48 hframeRoom (by decide)
  obtain ⟨hr00, hr01, hr02, hr03⟩ :=
    slot32Facts resultPtr 0 16 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    slot32Facts resultPtr 4 16 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    slot32Facts resultPtr 8 16 hresultRoom (by decide)
  obtain ⟨hr120, hr121, hr122, hr123⟩ :=
    slot32Facts resultPtr 12 16 hresultRoom (by decide)
  iintro ⟨Hglobal, Hvec, Hf8, Hf16, Hf24, Hf28, Hf32, Hf40,
    Hresult, Hdone⟩
  isimp only [vecDescriptorAt] at Hvec
  icases Hvec with ⟨Hcapacity, Hdata, Hlength⟩
  isimp only [intoIterDescriptorAt] at Hresult
  icases Hresult with ⟨Hr0, Hr4, Hr8, Hr12⟩
  ihave HvecWord : pointsTo_u64 vecPtr (packU32 capacity data) $$
      [Hcapacity Hdata]
  · iapply (sliceDescriptorAt_eq_u64 vecPtr capacity data).mp
    iapply sliceDescriptorAt_intro
    iframe
  ihave Hf8Word : pointsTo_u64 (frame + 8)
      (packU32 oldFrame8 oldFrame12) $$ [Hf8]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 8)
      oldFrame8 oldFrame12).mp
    iexact Hf8
  ihave Hf32Word : pointsTo_u64 (frame + 32)
      (packU32 oldFrame32 oldFrame36) $$ [Hf32]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 32)
      oldFrame32 oldFrame36).mp
    iexact Hf32
  simp only [func123]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 length hvl0 hvl1 hvl2 hvl3 $$ Hlength
  iintro Hlength
  iapply twp_store32 oldFrame40 hf400 hf401 hf402 hf403 $$ Hf40
  iintro Hf40
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HvecWordAt : pointsTo_u64 (vecPtr + 0)
      (packU32 capacity data) $$ [HvecWord]
  · iapply pointsTo_u64_add_zero
    iexact HvecWord
  iapply twp_load64 (packU32 capacity data)
    hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 $$ HvecWordAt
  iintro HvecWordAt
  iapply twp_store64 (packU32 oldFrame32 oldFrame36)
    hf320 hf321 hf322 hf323 hf324 hf325 hf326 hf327 $$ Hf32Word
  iintro Hf32Word
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 length hf400 hf401 hf402 hf403 $$ Hf40
  iintro Hf40
  iapply twp_store32 oldFrame16 hf160 hf161 hf162 hf163 $$ Hf16
  iintro Hf16
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 capacity data)
    hf320 hf321 hf322 hf323 hf324 hf325 hf326 hf327 $$ Hf32Word
  iintro Hf32Word
  iapply twp_store64 (packU32 oldFrame8 oldFrame12)
    hf80 hf81 hf82 hf83 hf84 hf85 hf86 hf87 $$ Hf8Word
  iintro Hf8Word
  ihave Hf8Desc :=
    (sliceDescriptorAt_eq_u64 (frame + 8) capacity data).mpr $$ Hf8Word
  isimp only [sliceDescriptorAt] at Hf8Desc
  icases Hf8Desc with ⟨Hf8, Hf12⟩
  ihave Hf12At : pointsTo_u32 (frame + 12) data $$ [Hf12]
  · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
    iexact Hf12
  iapply twp_localGet rfl
  iapply twp_load32 data hf120 hf121 hf122 hf123 $$ Hf12At
  iintro Hf12At
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 length hf160 hf161 hf162 hf163 $$ Hf16
  iintro Hf16
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  rw [UInt32.add_comm (length <<< (3 % 32)),
    show (3 % 32 : UInt32) = 3 by decide]
  iapply twp_store32 oldFrame24 hf240 hf241 hf242 hf243 $$ Hf24
  iintro Hf24
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 capacity hf80 hf81 hf82 hf83 $$ Hf8
  iintro Hf8
  iapply twp_store32 oldFrame28 hf280 hf281 hf282 hf283 $$ Hf28
  iintro Hf28
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hr0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hr0]
  · iapply pointsTo_u32_add_zero
    iexact Hr0
  iapply twp_store32 oldResult0 hr00 hr01 hr02 hr03 $$ Hr0At
  iintro Hr0At
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 capacity hf280 hf281 hf282 hf283 $$ Hf28
  iintro Hf28
  iapply twp_store32 oldResult8 hr80 hr81 hr82 hr83 $$ Hr8
  iintro Hr8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResult4 hr40 hr41 hr42 hr43 $$ Hr4
  iintro Hr4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (data + (length <<< 3))
    hf240 hf241 hf242 hf243 $$ Hf24
  iintro Hf24
  iapply twp_store32 oldResult12 hr120 hr121 hr122 hr123 $$ Hr12
  iintro Hr12
  ihave HvecWord : pointsTo_u64 vecPtr (packU32 capacity data) $$
      [HvecWordAt]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact HvecWordAt
  ihave HvecDesc : vecDescriptorAt vecPtr capacity data length $$
      [HvecWord Hlength]
  · ihave HvecPair :=
      (sliceDescriptorAt_eq_u64 vecPtr capacity data).mpr $$ HvecWord
    isimp only [sliceDescriptorAt] at HvecPair
    isimp only [vecDescriptorAt]
    iframe
  ihave Hf8Desc : sliceDescriptorAt (frame + 8) capacity data $$ [Hf8 Hf12At]
  · iapply sliceDescriptorAt_intro
    isplitl [Hf8]
    · iexact Hf8
    · rw [show (frame + 8) + 4 = frame + 12 by bv_decide]
      iexact Hf12At
  ihave Hf32Desc : sliceDescriptorAt (frame + 32) capacity data $$ [Hf32Word]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 32) capacity data).mpr
    iexact Hf32Word
  ihave Hr0 : pointsTo_u32 resultPtr data $$ [Hr0At]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact Hr0At
  ihave HresultDesc : intoIterDescriptorAt resultPtr data data capacity
      (data + (length <<< 3)) $$ [Hr0 Hr4 Hr8 Hr12]
  · isimp only [intoIterDescriptorAt]
    iframe
  simp only [frame, List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply Hdone $$ Hglobal HvecDesc Hf8Desc Hf16 Hf24 Hf28 Hf32Desc Hf40
    HresultDesc

/- Composable total rule for `func123` at absolute Wasm index `125`. -/
set_option maxHeartbeats 6000000 in
theorem vecIntoIter_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr vecPtr capacity data length stackTop : UInt32)
    (oldFrame8 oldFrame12 oldFrame16 oldFrame24 oldFrame28
      oldFrame32 oldFrame36 oldFrame40 : UInt32)
    (oldResult0 oldResult4 oldResult8 oldResult12 : UInt32)
    (hframeRoom : (stackTop - 48).toNat + 48 ≤ UInt32.size)
    (hvecRoom : vecPtr.toNat + 12 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      vecDescriptorAt vecPtr capacity data length ∗
      sliceDescriptorAt ((stackTop - 48) + 8) oldFrame8 oldFrame12 ∗
      pointsTo_u32 ((stackTop - 48) + 16) oldFrame16 ∗
      pointsTo_u32 ((stackTop - 48) + 24) oldFrame24 ∗
      pointsTo_u32 ((stackTop - 48) + 28) oldFrame28 ∗
      sliceDescriptorAt ((stackTop - 48) + 32) oldFrame32 oldFrame36 ∗
      pointsTo_u32 ((stackTop - 48) + 40) oldFrame40 ∗
      intoIterDescriptorAt resultPtr oldResult0 oldResult4
        oldResult8 oldResult12 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        vecDescriptorAt vecPtr capacity data length -∗
        sliceDescriptorAt ((stackTop - 48) + 8) capacity data -∗
        pointsTo_u32 ((stackTop - 48) + 16) length -∗
        pointsTo_u32 ((stackTop - 48) + 24)
          (data + (length <<< 3)) -∗
        pointsTo_u32 ((stackTop - 48) + 28) capacity -∗
        sliceDescriptorAt ((stackTop - 48) + 32) capacity data -∗
        pointsTo_u32 ((stackTop - 48) + 40) length -∗
        intoIterDescriptorAt resultPtr data data capacity
          (data + (length <<< 3)) -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 vecPtr, .i32 resultPtr] ++ stack },
        .call 125 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hvec, Hf8, Hf16, Hf24, Hf28, Hf32, Hf40,
    Hresult, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 125 func123Def
      (by decide) vecIntoIter_index $$ Hruntime
  iintro Hruntime
  simp [func123Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := vecIntoIter_body_twp (α := α)
    resultPtr vecPtr capacity data length stackTop
    oldFrame8 oldFrame12 oldFrame16 oldFrame24 oldFrame28
    oldFrame32 oldFrame36 oldFrame40
    oldResult0 oldResult4 oldResult8 oldResult12
    hframeRoom hvecRoom hresultRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hvec]
  · iexact Hvec
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hf16]
  · iexact Hf16
  isplitl [Hf24]
  · iexact Hf24
  isplitl [Hf28]
  · iexact Hf28
  isplitl [Hf32]
  · iexact Hf32
  isplitl [Hf40]
  · iexact Hf40
  isplitl [Hresult]
  · iexact Hresult
  iintro Hglobal Hvec Hf8 Hf16 Hf24 Hf28 Hf32 Hf40 Hresult
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hvec Hf8 Hf16 Hf24 Hf28 Hf32 Hf40
    Hresult

/-! ## Generated `IntoIter<u64>::next`

The result is Rust's two-word `Option<u64>` return area: a 64-bit discriminant
followed by the payload word. -/

def optionU64At [WasmHeapGS]
    (base : UInt32) (tag payload : UInt64) : IProp WasmHeapGF :=
  iprop% pointsTo_u64 base tag ∗ pointsTo_u64 (base + 8) payload

private theorem twp_eq
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
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.eq hresult)

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
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.constI64)

/- Exact empty-path body rule for generated local `func5`. -/
set_option maxHeartbeats 3000000 in
theorem intoIterNext_empty_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iterPtr allocation current capacity stackTop : UInt32)
    (oldFrame12 : UInt32) (oldTag oldPayload : UInt64)
    (hiterRoom : iterPtr.toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      intoIterDescriptorAt iterPtr allocation current capacity current ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      optionU64At resultPtr oldTag oldPayload ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        intoIterDescriptorAt iterPtr allocation current capacity current -∗
        pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 -∗
        optionU64At resultPtr 0 oldPayload -∗
        ∀ controls : List ControlFrame,
          WP (.running
            ⟨⟨[.i32 resultPtr, .i32 iterPtr],
                [.i32 (stackTop - 16)], []⟩,
              [.ret], 0, [], controls, calls⟩ : Expr α)
            @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 iterPtr], [.i32 0], []⟩,
        func5, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  obtain ⟨hi40, hi41, hi42, hi43⟩ :=
    slot32Facts iterPtr 4 16 hiterRoom (by decide)
  obtain ⟨hi120, hi121, hi122, hi123⟩ :=
    slot32Facts iterPtr 12 16 hiterRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
    slot64Facts resultPtr 0 16 hresultRoom (by decide)
  iintro ⟨Hglobal, Hiter, Hframe12, Hresult, Hdone⟩
  isimp only [intoIterDescriptorAt] at Hiter
  icases Hiter with ⟨Hallocation, Hcurrent, Hcapacity, Hfinish⟩
  isimp only [optionU64At] at Hresult
  icases Hresult with ⟨Htag, Hpayload⟩
  simp only [func5]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 current hi120 hi121 hi122 hi123 $$ Hfinish
  iintro Hfinish
  iapply twp_localGet rfl
  iapply twp_load32 current hi40 hi41 hi42 hi43 $$ Hcurrent
  iintro Hcurrent
  iapply twp_eq (result := 1) (by simp)
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_constI64
  ihave HtagAt : pointsTo_u64 (resultPtr + 0) oldTag $$ [Htag]
  · iapply pointsTo_u64_add_zero
    iexact Htag
  iapply twp_store64 oldTag hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 $$ HtagAt
  iintro HtagAt
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_exitControl (by rfl)
  ihave Htag : pointsTo_u64 resultPtr 0 $$ [HtagAt]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact HtagAt
  ihave Hiter : intoIterDescriptorAt iterPtr allocation current capacity
      current $$ [Hallocation Hcurrent Hcapacity Hfinish]
  · isimp only [intoIterDescriptorAt]
    iframe
  ihave Hresult : optionU64At resultPtr 0 oldPayload $$ [Htag Hpayload]
  · isimp only [optionU64At]
    iframe
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.take_zero, List.nil_append]
  iapply Hdone $$ Hglobal Hiter Hframe12 Hresult

/- Exact nonempty-path body rule for generated local `func5`. -/
set_option maxHeartbeats 3000000 in
theorem intoIterNext_nonempty_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iterPtr allocation current capacity finish stackTop : UInt32)
    (value oldTag oldPayload : UInt64) (oldFrame12 : UInt32)
    (hne : finish ≠ current)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hiterRoom : iterPtr.toNat + 16 ≤ UInt32.size)
    (hcurrentRoom : current.toNat + 8 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      intoIterDescriptorAt iterPtr allocation current capacity finish ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u64 current value ∗
      optionU64At resultPtr oldTag oldPayload ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        intoIterDescriptorAt iterPtr allocation (current + 8) capacity finish -∗
        pointsTo_u32 ((stackTop - 16) + 12) current -∗
        pointsTo_u64 current value -∗
        optionU64At resultPtr 1 value -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 iterPtr],
              [.i32 (stackTop - 16)], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 iterPtr], [.i32 0], []⟩,
        func5, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  obtain ⟨hi40, hi41, hi42, hi43⟩ :=
    slot32Facts iterPtr 4 16 hiterRoom (by decide)
  obtain ⟨hi120, hi121, hi122, hi123⟩ :=
    slot32Facts iterPtr 12 16 hiterRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    slot32Facts frame 12 16 hframeRoom (by decide)
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    slot64Facts current 0 8 hcurrentRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
    slot64Facts resultPtr 0 16 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83, hr84, hr85, hr86, hr87⟩ :=
    slot64Facts resultPtr 8 16 hresultRoom (by decide)
  iintro ⟨Hglobal, Hiter, Hframe12, Hvalue, Hresult, Hdone⟩
  isimp only [intoIterDescriptorAt] at Hiter
  icases Hiter with ⟨Hallocation, Hcurrent, Hcapacity, Hfinish⟩
  isimp only [optionU64At] at Hresult
  icases Hresult with ⟨Htag, Hpayload⟩
  simp only [func5]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 finish hi120 hi121 hi122 hi123 $$ Hfinish
  iintro Hfinish
  iapply twp_localGet rfl
  iapply twp_load32 current hi40 hi41 hi42 hi43 $$ Hcurrent
  iintro Hcurrent
  iapply twp_eq (result := 0) (by simp [hne])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 current hi40 hi41 hi42 hi43 $$ Hcurrent
  iintro Hcurrent
  iapply twp_store32 oldFrame12 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 current hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm (8 : UInt32) current]
  iapply twp_store32 current hi40 hi41 hi42 hi43 $$ Hcurrent
  iintro Hcurrent
  iapply twp_br (by rfl)
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 current hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  ihave HvalueAt : pointsTo_u64 (current + 0) value $$ [Hvalue]
  · iapply pointsTo_u64_add_zero
    iexact Hvalue
  iapply twp_load64 value hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 $$ HvalueAt
  iintro HvalueAt
  iapply twp_store64 oldPayload hr80 hr81 hr82 hr83 hr84 hr85 hr86 hr87
    $$ Hpayload
  iintro Hpayload
  iapply twp_localGet rfl
  iapply twp_constI64
  ihave HtagAt : pointsTo_u64 (resultPtr + 0) oldTag $$ [Htag]
  · iapply pointsTo_u64_add_zero
    iexact Htag
  iapply twp_store64 oldTag hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 $$ HtagAt
  iintro HtagAt
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  ihave Hvalue : pointsTo_u64 current value $$ [HvalueAt]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact HvalueAt
  ihave Htag : pointsTo_u64 resultPtr 1 $$ [HtagAt]
  · rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]
    iexact HtagAt
  ihave Hiter : intoIterDescriptorAt iterPtr allocation (current + 8)
      capacity finish $$ [Hallocation Hcurrent Hcapacity Hfinish]
  · isimp only [intoIterDescriptorAt]
    iframe
  ihave Hresult : optionU64At resultPtr 1 value $$ [Htag Hpayload]
  · isimp only [optionU64At]
    iframe
  iapply Hdone $$ Hglobal Hiter Hframe12 Hvalue Hresult

/- Total empty-path call rule for `func5` at absolute Wasm index `7`. -/
set_option maxHeartbeats 3000000 in
theorem intoIterNext_empty_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iterPtr allocation current capacity stackTop : UInt32)
    (oldFrame12 : UInt32) (oldTag oldPayload : UInt64)
    (hiterRoom : iterPtr.toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      intoIterDescriptorAt iterPtr allocation current capacity current ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      optionU64At resultPtr oldTag oldPayload ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        intoIterDescriptorAt iterPtr allocation current capacity current -∗
        pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 -∗
        optionU64At resultPtr 0 oldPayload -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 iterPtr, .i32 resultPtr] ++ stack },
        .call 7 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hiter, Hframe12, Hresult, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 7 func5Def
      (by decide) intoIterNext_index $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := intoIterNext_empty_body_twp (α := α)
    resultPtr iterPtr allocation current capacity stackTop
    oldFrame12 oldTag oldPayload hiterRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hiter]
  · iexact Hiter
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [Hresult]
  · iexact Hresult
  iintro Hglobal Hiter Hframe12 Hresult
  iintro %blockControls
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hiter Hframe12 Hresult

/- Total nonempty-path call rule for `func5` at absolute Wasm index `7`. -/
set_option maxHeartbeats 3000000 in
theorem intoIterNext_nonempty_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iterPtr allocation current capacity finish stackTop : UInt32)
    (value oldTag oldPayload : UInt64) (oldFrame12 : UInt32)
    (hne : finish ≠ current)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hiterRoom : iterPtr.toNat + 16 ≤ UInt32.size)
    (hcurrentRoom : current.toNat + 8 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      intoIterDescriptorAt iterPtr allocation current capacity finish ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u64 current value ∗
      optionU64At resultPtr oldTag oldPayload ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        intoIterDescriptorAt iterPtr allocation (current + 8) capacity finish -∗
        pointsTo_u32 ((stackTop - 16) + 12) current -∗
        pointsTo_u64 current value -∗
        optionU64At resultPtr 1 value -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 iterPtr, .i32 resultPtr] ++ stack },
        .call 7 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hiter, Hframe12, Hvalue, Hresult, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 7 func5Def
      (by decide) intoIterNext_index $$ Hruntime
  iintro Hruntime
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := intoIterNext_nonempty_body_twp (α := α)
    resultPtr iterPtr allocation current capacity finish stackTop
    value oldTag oldPayload oldFrame12 hne hframeRoom hiterRoom
    hcurrentRoom hresultRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hiter]
  · iexact Hiter
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [Hvalue]
  · iexact Hvalue
  isplitl [Hresult]
  · iexact Hresult
  iintro Hglobal Hiter Hframe12 Hvalue Hresult
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hiter Hframe12 Hvalue Hresult

end Project.Mergesort.OutputIteratorProof
