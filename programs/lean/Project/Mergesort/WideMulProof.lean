import Project.Mergesort.FormatProof

/-! Arithmetic facts for the generated `func254` wide multiply on the
decimal parser's `(acc, 10)` operands. -/

namespace Project.Mergesort.WideMulProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.FormatProof

private theorem twp_constI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {v : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 v :: stack⟩, code, arity,
      remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, stack⟩, .constI64 v :: code, arity,
      remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.constI64)

private theorem twp_andI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {lhs rhs : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 (lhs &&& rhs) :: stack⟩, code,
      arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, .i64 rhs :: .i64 lhs :: stack⟩,
      .andI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.andI64)

private theorem twp_addI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {lhs rhs : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 (lhs + rhs) :: stack⟩, code,
      arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, .i64 rhs :: .i64 lhs :: stack⟩,
      .addI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.addI64)

private theorem twp_mulI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {lhs rhs : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 (lhs * rhs) :: stack⟩, code,
      arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, .i64 rhs :: .i64 lhs :: stack⟩,
      .mulI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.mulI64)

private theorem twp_shrUI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {lhs rhs : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 (lhs >>> (rhs % 64)) :: stack⟩,
      code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, .i64 rhs :: .i64 lhs :: stack⟩,
      .shrUI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shrUI64)

private theorem twp_shlI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {lhs rhs : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 (lhs <<< (rhs % 64)) :: stack⟩,
      code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, .i64 rhs :: .i64 lhs :: stack⟩,
      .shlI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shlI64)

private theorem twp_orI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {lhs rhs : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 (lhs ||| rhs) :: stack⟩, code,
      arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, .i64 rhs :: .i64 lhs :: stack⟩,
      .orI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.orI64)

private theorem twp_extendUI32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {params locals stack : List Value} {v : UInt32} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, locals, .i64 (UInt64.ofNat v.toNat) :: stack⟩,
      code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, locals, .i32 v :: stack⟩,
      .extendUI32 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.extendUI32)

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

def parserWideLow (x : UInt64) : UInt64 :=
  ((10 : UInt64) &&& (4294967295 : UInt64)) *
      (x &&& (4294967295 : UInt64)) +
    ((((10 : UInt64) >>> (32 % 64)) *
        (x &&& (4294967295 : UInt64)) +
      ((10 : UInt64) &&& (4294967295 : UInt64)) *
        (x >>> (32 % 64))) <<< (32 % 64))

def parserWideCross1 (x : UInt64) : UInt64 :=
  ((10 : UInt64) >>> (32 % 64)) *
    (x &&& (4294967295 : UInt64))

def parserWideCross (x : UInt64) : UInt64 :=
  parserWideCross1 x +
    ((10 : UInt64) &&& (4294967295 : UInt64)) *
      (x >>> (32 % 64))

def parserWideP0 (x : UInt64) : UInt64 :=
  ((10 : UInt64) &&& (4294967295 : UInt64)) *
    (x &&& (4294967295 : UInt64))

def parserWideHigh (x : UInt64) : UInt64 :=
  ((((10 : UInt64) >>> (32 % 64)) * (x >>> (32 % 64)) +
      ((UInt64.ofNat
          (if parserWideCross x < parserWideCross1 x then
            (1 : UInt32)
          else 0).toNat <<< (32 % 64)) |||
        (parserWideCross x >>> (32 % 64)))) +
    UInt64.ofNat
      (if parserWideLow x < parserWideP0 x then (1 : UInt32) else 0).toNat) +
    (0 * x + (10 : UInt64) * 0)

theorem parserWideLow_eq (x : UInt64) : parserWideLow x = x * 10 := by
  unfold parserWideLow
  bv_decide

theorem parserWideHigh_eq_zero (x : UInt64)
    (hbound : x ≤ 1844674407370955161) : parserWideHigh x = 0 := by
  unfold parserWideHigh parserWideLow parserWideP0 parserWideCross
    parserWideCross1
  split <;> split <;> simp_all <;> bv_decide

def wideMulParams (resultPtr : UInt32) (x : UInt64) : List Value :=
  [.i32 resultPtr, .i64 x, .i64 0, .i64 10, .i64 0]

def wideMulZeroLocals : List Value := List.replicate 6 (.i64 0)

def wideMulLowLocals (x : UInt64) : List Value :=
  [.i64 (parserWideCross x), .i64 (parserWideCross1 x),
   .i64 (parserWideP0 x), .i64 ((10 : UInt64) >>> (32 % 64)),
   .i64 (x >>> (32 % 64)), .i64 (parserWideLow x)]

def wideMulAtStoreLow : Program := func254.drop 37
def wideMulAtStoreHigh : Program := func254.drop 67

theorem func254_prefix_eq :
    func254 = func254.take 37 ++ wideMulAtStoreLow := by
  simp [wideMulAtStoreLow]

theorem wideMulAtStoreHigh_eq :
    wideMulAtStoreHigh = [.store64 8] := by
  rfl

/- Segment A: the pure generated prefix, ending with the named low word in
local 10 and the result pointer still on the operand stack. -/
theorem wideMul_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    (resultPtr : UInt32) (x : UInt64) {calls : List CallFrame} :
    (WP (.running
      ⟨⟨wideMulParams resultPtr x, wideMulLowLocals x, [.i32 resultPtr]⟩,
        wideMulAtStoreLow, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨wideMulParams resultPtr x, wideMulZeroLocals, []⟩,
        func254, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hdone
  simp only [func254]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_andI64
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_andI64
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_mulI64
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_shrUI64
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_mulI64
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_shrUI64
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_mulI64
  iapply twp_addI64
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_shlI64
  iapply twp_addI64
  iapply twp_localSet rfl
  isimp [wideMulParams, wideMulZeroLocals, wideMulLowLocals,
    parserWideLow, parserWideCross, parserWideCross1, parserWideP0,
    wideMulAtStoreLow, func254] at Hdone
  isimp [wideMulParams, wideMulZeroLocals, wideMulLowLocals,
    parserWideLow, parserWideCross, parserWideCross1, parserWideP0,
    wideMulAtStoreLow]
  iexact Hdone

/- Segment B: write the low word, compute the named high word, and stop with
the final store as the only remaining instruction. -/
theorem wideMul_storeLow_high_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    (resultPtr : UInt32) (x : UInt64) (oldLow : UInt64)
    (hroom : resultPtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u64 (resultPtr + 0) oldLow ∗
      (pointsTo_u64 (resultPtr + 0) (parserWideLow x) -∗
        WP (.running
          ⟨⟨wideMulParams resultPtr x, wideMulLowLocals x,
              [.i64 (parserWideHigh x), .i32 resultPtr]⟩,
            wideMulAtStoreHigh, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨wideMulParams resultPtr x, wideMulLowLocals x, [.i32 resultPtr]⟩,
        wideMulAtStoreLow, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    descriptorSlot64Facts resultPtr 0 16 hroom (by decide)
  iintro ⟨Hlow, Hdone⟩
  simp only [wideMulAtStoreLow, func254, List.drop]
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_store64 oldLow h0 h1 h2 h3 h4 h5 h6 h7 $$ Hlow
  iintro Hlow
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_mulI64
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_ltUI64 rfl
  iapply twp_extendUI32
  iapply twp_constI64
  iapply twp_shlI64
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_shrUI64
  iapply twp_orI64
  iapply twp_addI64
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_ltUI64 rfl
  iapply twp_extendUI32
  iapply twp_addI64
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_mulI64
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_mulI64
  iapply twp_addI64
  iapply twp_addI64
  isimp [wideMulParams, wideMulLowLocals, parserWideHigh,
    parserWideLow, parserWideCross, parserWideCross1, parserWideP0,
    wideMulAtStoreHigh, func254] at Hdone
  isimp [wideMulParams, wideMulLowLocals, parserWideHigh,
    parserWideLow, parserWideCross, parserWideCross1, parserWideP0,
    wideMulAtStoreHigh, func254]
  isimp [UInt32.add_zero, parserWideLow] at Hlow
  iapply Hdone $$ Hlow

/- Segment C: the final high-word store. -/
theorem wideMul_storeHigh_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    (resultPtr : UInt32) (x oldHigh : UInt64)
    (hroom : resultPtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u64 (resultPtr + 8) oldHigh ∗
      (pointsTo_u64 (resultPtr + 8) (parserWideHigh x) -∗
        WP (.running
          ⟨⟨wideMulParams resultPtr x, wideMulLowLocals x, []⟩,
            [], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨wideMulParams resultPtr x, wideMulLowLocals x,
          [.i64 (parserWideHigh x), .i32 resultPtr]⟩,
        wideMulAtStoreHigh, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    descriptorSlot64Facts resultPtr 8 16 hroom (by decide)
  iintro ⟨Hhigh, Hdone⟩
  rw [wideMulAtStoreHigh_eq]
  iapply Wasm.SmallStep.twp_store64 oldHigh h0 h1 h2 h3 h4 h5 h6 h7 $$
    Hhigh
  iintro Hhigh
  iapply Hdone $$ Hhigh

/- Exact bounded body contract used by the decimal parser. -/
theorem wideMul_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    (resultPtr : UInt32) (x oldLow oldHigh : UInt64)
    (hbound : x ≤ 1844674407370955161)
    (hroom : resultPtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u64 (resultPtr + 0) oldLow ∗
      pointsTo_u64 (resultPtr + 8) oldHigh ∗
      (pointsTo_u64 (resultPtr + 0) (x * 10) -∗
        pointsTo_u64 (resultPtr + 8) 0 -∗
        WP (.running
          ⟨⟨wideMulParams resultPtr x, wideMulLowLocals x, []⟩,
            [], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨wideMulParams resultPtr x, wideMulZeroLocals, []⟩,
        func254, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hlow, Hhigh, Hdone⟩
  iapply wideMul_prefix_twp resultPtr x
  iapply wideMul_storeLow_high_twp resultPtr x oldLow hroom
  isplitl [Hlow]
  · iexact Hlow
  iintro Hlow
  iapply wideMul_storeHigh_twp resultPtr x oldHigh hroom
  isplitl [Hhigh]
  · iexact Hhigh
  iintro Hhigh
  have hlow := parserWideLow_eq x
  have hhigh := parserWideHigh_eq_zero x hbound
  isimp [hlow] at Hlow
  isimp [hhigh] at Hhigh
  isimp [UInt32.add_zero] at Hdone
  iapply Hdone $$ Hlow Hhigh

/- Absolute Wasm call rule.  The two imported stdio functions shift local
`func254` to immediate 256. -/
theorem wideMul_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    (resultPtr : UInt32) (x oldLow oldHigh : UInt64)
    (hbound : x ≤ 1844674407370955161)
    (hroom : resultPtr.toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u64 (resultPtr + 0) oldLow ∗
      pointsTo_u64 (resultPtr + 8) oldHigh ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u64 (resultPtr + 0) (x * 10) -∗
        pointsTo_u64 (resultPtr + 8) 0 -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code, arity,
            remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i64 0, .i64 10, .i64 0, .i64 x, .i32 resultPtr] ++ stack },
        .call 256 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hlow, Hhigh, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 256 wideMul128Function
      (by decide) wideMul128_index $$ Hruntime
  iintro Hruntime
  simp [wideMul128Function, func254Def, Function.toLocals,
    Function.numParams, ValueType.zero]
  have Hbody := wideMul_body_twp (α := α) resultPtr x oldLow oldHigh
    hbound hroom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp [wideMulParams, wideMulZeroLocals] at Hbody
  iapply Hbody
  isplitl [Hlow]
  · iexact Hlow
  isplitl [Hhigh]
  · iexact Hhigh
  iintro Hlow Hhigh
  iapply twp_returnFromCallFallthrough (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hlow Hhigh

end Project.Mergesort.WideMulProof
