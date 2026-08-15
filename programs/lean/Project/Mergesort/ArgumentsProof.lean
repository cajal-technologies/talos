import Project.Mergesort.FormatProof

/-!
# Generated formatting-arguments constructors

The exported driver uses two small generated constructors for the descriptor
passed to the formatting machinery.  `func49` stores two raw words, while
`func50` stores a string pointer and its generated tagged length.
-/

namespace Project.Mergesort.ArgumentsProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.FormatProof

def argumentsAt [WasmHeapGS]
    (base first second : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 base first ∗ pointsTo_u32 (base + 4) second

private theorem pointsTo_u32_at_eq
    [WasmSmallStepGS hlc] {address address' value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 address value ⊢ pointsTo_u32 address' value := by
  rw [haddress]

/-- Exact total body rule for generated local `func49`. -/
theorem argumentsNew_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr first second oldFirst oldSecond : UInt32)
    (hroom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 (resultPtr + 0) oldFirst ∗
      pointsTo_u32 (resultPtr + 4) oldSecond ∗
      (argumentsAt resultPtr first second -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 first, .i32 second], [], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 first, .i32 second], [], []⟩,
        func49, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h00, h01, h02, h03⟩ :=
    descriptorSlot32Facts resultPtr 0 8 hroom (by decide)
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts resultPtr 4 8 hroom (by decide)
  iintro ⟨Hfirst, Hsecond, Hdone⟩
  simp only [func49]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldSecond h40 h41 h42 h43 $$ Hsecond
  iintro Hsecond
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFirst h00 h01 h02 h03 $$ Hfirst
  iintro Hfirst
  ihave Hfirst0 : pointsTo_u32 resultPtr first $$ [Hfirst]
  · iapply pointsTo_u32_at_eq (show resultPtr + 0 = resultPtr by
      bv_decide)
    iexact Hfirst
  ihave Hargs : argumentsAt resultPtr first second $$ [Hfirst0 Hsecond]
  · simp only [argumentsAt]
    iframe
  iapply Hdone $$ Hargs

/-- Composable total call rule for `func49` at absolute Wasm index `51`. -/
theorem argumentsNew_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr first second oldFirst oldSecond : UInt32)
    (hroom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (resultPtr + 0) oldFirst ∗
      pointsTo_u32 (resultPtr + 4) oldSecond ∗
      (runtimeModuleOwn «module» -∗
        argumentsAt resultPtr first second -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 second, .i32 first, .i32 resultPtr] ++ stack },
        .call 51 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hfirst, Hsecond, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 51 func49Def
      (by decide) argumentsNew_index $$ Hruntime
  iintro Hruntime
  simp [func49Def, Function.toLocals, Function.numParams]
  have Hbody := argumentsNew_body_twp (α := α)
    resultPtr first second oldFirst oldSecond hroom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  ihave HfirstAt0 : pointsTo_u32 (resultPtr + 0) oldFirst $$ [Hfirst]
  · iapply pointsTo_u32_at_eq (show resultPtr = resultPtr + 0 by
      bv_decide)
    iexact Hfirst
  iapply Hbody
  isplitl [HfirstAt0]
  · iexact HfirstAt0
  isplitl [Hsecond]
  · iexact Hsecond
  iintro Hargs
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hargs

/-- Exact total body rule for generated local `func50`. -/
theorem argumentsFromStr_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr stringPtr stringLength oldFirst oldSecond : UInt32)
    (hroom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 (resultPtr + 0) oldFirst ∗
      pointsTo_u32 (resultPtr + 4) oldSecond ∗
      (argumentsAt resultPtr stringPtr
          ((1 : UInt32) ||| (stringLength <<< (1 : UInt32))) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 stringPtr, .i32 stringLength],
              [.i32 1,
                .i32 ((1 : UInt32) ||| (stringLength <<< (1 : UInt32)))],
              []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 stringPtr, .i32 stringLength],
          [.i32 0, .i32 0], []⟩,
        func50, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h00, h01, h02, h03⟩ :=
    descriptorSlot32Facts resultPtr 0 8 hroom (by decide)
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts resultPtr 4 8 hroom (by decide)
  iintro ⟨Hfirst, Hsecond, Hdone⟩
  simp only [func50]
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_shl
  iapply twp_or
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFirst h00 h01 h02 h03 $$ Hfirst
  iintro Hfirst
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldSecond h40 h41 h42 h43 $$ Hsecond
  iintro Hsecond
  ihave Hfirst0 : pointsTo_u32 resultPtr stringPtr $$ [Hfirst]
  · iapply pointsTo_u32_at_eq (show resultPtr + 0 = resultPtr by
      bv_decide)
    iexact Hfirst
  isimp at Hsecond
  isimp
  ihave Hargs : argumentsAt resultPtr stringPtr
      ((1 : UInt32) ||| (stringLength <<< (1 : UInt32))) $$
      [Hfirst0 Hsecond]
  · simp only [argumentsAt]
    iframe
  iapply Hdone $$ Hargs

/-- Composable total call rule for `func50` at absolute Wasm index `52`. -/
theorem argumentsFromStr_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr stringPtr stringLength oldFirst oldSecond : UInt32)
    (hroom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (resultPtr + 0) oldFirst ∗
      pointsTo_u32 (resultPtr + 4) oldSecond ∗
      (runtimeModuleOwn «module» -∗
        argumentsAt resultPtr stringPtr
          ((1 : UInt32) ||| (stringLength <<< (1 : UInt32))) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 stringLength, .i32 stringPtr, .i32 resultPtr] ++ stack },
        .call 52 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hfirst, Hsecond, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 52 func50Def
      (by decide) argumentsFromStr_index $$ Hruntime
  iintro Hruntime
  simp [func50Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := argumentsFromStr_body_twp (α := α)
    resultPtr stringPtr stringLength oldFirst oldSecond hroom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  ihave HfirstAt0 : pointsTo_u32 (resultPtr + 0) oldFirst $$ [Hfirst]
  · iapply pointsTo_u32_at_eq (show resultPtr = resultPtr + 0 by
      bv_decide)
    iexact Hfirst
  iapply Hbody
  isplitl [HfirstAt0]
  · iexact HfirstAt0
  isplitl [Hsecond]
  · iexact Hsecond
  iintro Hargs
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hargs

end Project.Mergesort.ArgumentsProof
