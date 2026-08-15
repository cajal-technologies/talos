import Project.Mergesort.Machine

/-!
# Generated vector descriptor helpers

The unchanged Rust driver represents `Vec<u64>` by its generated three-word
descriptor `(capacity, data, length)`.  This file starts the vector layer with
the exact generated `func103` length accessor and its absolute-index call rule.
-/

namespace Project.Mergesort.VectorProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine

def vecDescriptorAt [WasmHeapGS]
    (base capacity data length : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 base capacity ∗
    pointsTo_u32 (base + 4) data ∗
    pointsTo_u32 (base + 8) length

private theorem pointsTo_u32_add_zero
    [WasmHeapGS] (address value : UInt32) :
    pointsTo_u32 (address + 0) value ⊢ pointsTo_u32 address value := by
  rw [UInt32.add_zero]

private theorem descriptorSlot32Facts (base : UInt32) (offset total : Nat)
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
  exact ⟨by simpa using h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega)⟩

/-- Exact total body rule for generated local `func103`, `Vec<u64>::len`.
The descriptor is preserved and the generated return stack contains its length.
-/
theorem vecLen_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr length : UInt32)
    (hroom : vecPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 (vecPtr + 8) length ∗
      (pointsTo_u32 (vecPtr + 8) length -∗
        WP (.running
          ⟨⟨[.i32 vecPtr], [], [.i32 length]⟩,
            [.ret], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 vecPtr], [], []⟩,
        func103, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    descriptorSlot32Facts vecPtr 8 12 hroom (by decide)
  iintro ⟨Hlength, Hdone⟩
  simp only [func103]
  iapply twp_localGet rfl
  iapply twp_load32 length h0 h1 h2 h3 $$ Hlength
  iintro Hlength
  iapply Hdone $$ Hlength

/-- Composable total call rule for `func103` at absolute Wasm index `105`. -/
theorem vecLen_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (vecPtr length : UInt32)
    (hroom : vecPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (vecPtr + 8) length ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 (vecPtr + 8) length -∗
        WP (.running
          ⟨{ callerLocals with values := .i32 length :: stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 vecPtr :: stack },
        .call 105 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hvec, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 105 func103Def
      (by decide) vecLen_index $$ Hruntime
  iintro Hruntime
  simp [func103Def, Function.toLocals, Function.numParams]
  have Hbody := vecLen_body_twp (α := α)
    vecPtr length hroom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hvec]
  · iexact Hvec
  iintro Hvec
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.singleton_append]
  iapply Hdone $$ Hruntime Hvec

theorem vecDerefMut_body_eq_stringDeref_body : func122 = func119 := rfl

/-- Shared exact body rule for the identical generated `String::deref` and
`Vec<u64>::deref_mut` descriptor-copy programs (`func119` and `func122`). -/
theorem derefSlice_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr data length oldResultData oldResultLength : UInt32)
    (hsourceRoom : sourcePtr.toNat + 12 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 (sourcePtr + 4) data ∗
      pointsTo_u32 (sourcePtr + 8) length ∗
      pointsTo_u32 (resultPtr + 0) oldResultData ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (pointsTo_u32 (sourcePtr + 4) data -∗
        pointsTo_u32 (sourcePtr + 8) length -∗
        pointsTo_u32 (resultPtr + 0) data -∗
        pointsTo_u32 (resultPtr + 4) length -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 sourcePtr], [.i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 sourcePtr], [.i32 0], []⟩,
        func119, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hs40, hs41, hs42, hs43⟩ :=
    descriptorSlot32Facts sourcePtr 4 12 hsourceRoom (by decide)
  obtain ⟨hs80, hs81, hs82, hs83⟩ :=
    descriptorSlot32Facts sourcePtr 8 12 hsourceRoom (by decide)
  obtain ⟨hr00, hr01, hr02, hr03⟩ :=
    descriptorSlot32Facts resultPtr 0 8 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 8 hresultRoom (by decide)
  iintro ⟨HsourceData, HsourceLength, HresultData, HresultLength, Hdone⟩
  simp only [func119]
  iapply twp_localGet rfl
  iapply twp_load32 data hs40 hs41 hs42 hs43 $$ HsourceData
  iintro HsourceData
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 length hs80 hs81 hs82 hs83 $$ HsourceLength
  iintro HsourceLength
  iapply twp_store32 oldResultLength hr40 hr41 hr42 hr43 $$ HresultLength
  iintro HresultLength
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResultData hr00 hr01 hr02 hr03 $$ HresultData
  iintro HresultData
  simp
  iapply Hdone $$ HsourceData HsourceLength HresultData HresultLength

/-- The shared descriptor-copy rule specialized to generated `func122`. -/
theorem vecDerefMut_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr data length oldResultData oldResultLength : UInt32)
    (hsourceRoom : sourcePtr.toNat + 12 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 (sourcePtr + 4) data ∗
      pointsTo_u32 (sourcePtr + 8) length ∗
      pointsTo_u32 (resultPtr + 0) oldResultData ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (pointsTo_u32 (sourcePtr + 4) data -∗
        pointsTo_u32 (sourcePtr + 8) length -∗
        pointsTo_u32 (resultPtr + 0) data -∗
        pointsTo_u32 (resultPtr + 4) length -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 sourcePtr], [.i32 data], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 sourcePtr], [.i32 0], []⟩,
        func122, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [vecDerefMut_body_eq_stringDeref_body]
  exact derefSlice_body_twp resultPtr sourcePtr data length
    oldResultData oldResultLength hsourceRoom hresultRoom

/-- Composable call rule for generated `String::deref` at absolute index 121. -/
theorem stringDeref_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr data length oldResultData oldResultLength : UInt32)
    (hsourceRoom : sourcePtr.toNat + 12 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (sourcePtr + 4) data ∗
      pointsTo_u32 (sourcePtr + 8) length ∗
      pointsTo_u32 (resultPtr + 0) oldResultData ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 (sourcePtr + 4) data -∗
        pointsTo_u32 (sourcePtr + 8) length -∗
        pointsTo_u32 (resultPtr + 0) data -∗
        pointsTo_u32 (resultPtr + 4) length -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 sourcePtr, .i32 resultPtr] ++ stack },
        .call 121 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, HsourceData, HsourceLength, HresultData,
    HresultLength, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 121 func119Def
      (by decide) stringDeref_index $$ Hruntime
  iintro Hruntime
  simp [func119Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := derefSlice_body_twp (α := α)
    resultPtr sourcePtr data length oldResultData oldResultLength
    hsourceRoom hresultRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  ihave HresultDataAt : pointsTo_u32 (resultPtr + 0) oldResultData $$
      [HresultData]
  · rw [UInt32.add_zero]
    iexact HresultData
  iapply Hbody
  isplitl [HsourceData]
  · iexact HsourceData
  isplitl [HsourceLength]
  · iexact HsourceLength
  isplitl [HresultDataAt]
  · iexact HresultDataAt
  isplitl [HresultLength]
  · iexact HresultLength
  iintro HsourceData HsourceLength HresultData HresultLength
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave HresultDataPlain : pointsTo_u32 resultPtr data $$ [HresultData]
  · iapply pointsTo_u32_add_zero
    iexact HresultData
  iapply Hdone $$ Hruntime HsourceData HsourceLength HresultDataPlain HresultLength

/-- Composable call rule for generated `Vec<u64>::deref_mut` at absolute
index 124.  It reuses the shared descriptor-copy body proof above. -/
theorem vecDerefMut_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr data length oldResultData oldResultLength : UInt32)
    (hsourceRoom : sourcePtr.toNat + 12 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (sourcePtr + 4) data ∗
      pointsTo_u32 (sourcePtr + 8) length ∗
      pointsTo_u32 (resultPtr + 0) oldResultData ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 (sourcePtr + 4) data -∗
        pointsTo_u32 (sourcePtr + 8) length -∗
        pointsTo_u32 (resultPtr + 0) data -∗
        pointsTo_u32 (resultPtr + 4) length -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 sourcePtr, .i32 resultPtr] ++ stack },
        .call 124 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, HsourceData, HsourceLength, HresultData,
    HresultLength, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 124 func122Def
      (by decide) vecDerefMut_index $$ Hruntime
  iintro Hruntime
  simp [func122Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := vecDerefMut_body_twp (α := α)
    resultPtr sourcePtr data length oldResultData oldResultLength
    hsourceRoom hresultRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  ihave HresultDataAt : pointsTo_u32 (resultPtr + 0) oldResultData $$
      [HresultData]
  · rw [UInt32.add_zero]
    iexact HresultData
  iapply Hbody
  isplitl [HsourceData]
  · iexact HsourceData
  isplitl [HsourceLength]
  · iexact HsourceLength
  isplitl [HresultDataAt]
  · iexact HresultDataAt
  isplitl [HresultLength]
  · iexact HresultLength
  iintro HsourceData HsourceLength HresultData HresultLength
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave HresultDataPlain : pointsTo_u32 resultPtr data $$ [HresultData]
  · iapply pointsTo_u32_add_zero
    iexact HresultData
  iapply Hdone $$ Hruntime HsourceData HsourceLength HresultDataPlain HresultLength

end Project.Mergesort.VectorProof
