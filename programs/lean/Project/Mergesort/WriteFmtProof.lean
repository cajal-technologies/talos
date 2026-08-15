import Project.Mergesort.FormatProof
import Project.Mergesort.MemoryFillProof

/-!
# Generated buffered-format writer

The output loop reaches generated local `func33` at absolute index 35.  This
file verifies that large formatter bottom-up.  The first contract covers the
exact 32-byte shadow-frame prologue and stops at its first nested call
(absolute index 36), keeping that formatter dependency explicit.
-/

namespace Project.Mergesort.WriteFmtProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.RangeProof
open Project.Mergesort.FormatProof
open Project.Mergesort.Machine
open Project.Mergesort.MemoryFillProof

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

private theorem pointsTo_u32_at_eq
    [WasmHeapGS] {left right value : UInt32} (h : left = right) :
    pointsTo_u32 left value ⊢ pointsTo_u32 right value := by
  rw [h]

private theorem formatPrepare_index :
    «module».funcs[34]? = some func34Def := by
  rfl

def writeFmtAtPrepare : Program := func33.drop 18
def writeFmtAfterPrepare : Program := func33.drop 19

def writeFmtParams
    (resultPtr writerPtr formatPtr argumentsPtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 writerPtr, .i32 formatPtr, .i32 argumentsPtr]

def writeFmtLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0]

def formatPrepareOuterBody : Program :=
  match func34.drop 7 with
  | .block _ _ body :: _ => body
  | _ => []

def formatPrepareAfterOuter : Program := func34.drop 8

def formatPrepareLocals (frame second : UInt32) : List Value :=
  [.i32 frame, .i32 second, .i32 0, .i32 0, .i32 0,
   .i32 0, .i32 0, .i32 0, .i32 0]

def formatPrepareOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := formatPrepareOuterBody
    continuation := formatPrepareAfterOuter
    belowStack := [] }

def formatPrepareMiddleBody : Program :=
  match formatPrepareOuterBody with
  | .block _ _ body :: _ => body
  | _ => []

def formatPrepareAfterMiddle : Program := formatPrepareOuterBody.drop 1

def formatPrepareInnerBody : Program :=
  match formatPrepareMiddleBody with
  | .block _ _ body :: _ => body
  | _ => []

def formatPrepareStaticPath : Program := formatPrepareMiddleBody.drop 1

def formatPrepareMiddleFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := formatPrepareMiddleBody
    continuation := formatPrepareAfterMiddle
    belowStack := [] }

def formatPrepareStaticLocals
    (frame second staticFirst staticSecond : UInt32) : List Value :=
  [.i32 frame, .i32 second, .i32 0, .i32 0,
   .i32 staticFirst, .i32 staticSecond, .i32 0, .i32 0, .i32 0]

def formatPrepareFinalLocals
    (frame second staticFirst staticSecond : UInt32) : List Value :=
  [.i32 frame, .i32 second, .i32 0, .i32 0,
   .i32 staticFirst, .i32 staticSecond, .i32 staticFirst,
   .i32 staticSecond, .i32 staticFirst]

theorem writeFmtAtPrepare_eq :
    writeFmtAtPrepare = .call 36 :: writeFmtAfterPrepare := by
  rfl

theorem formatPrepare_at_outer_eq :
    func34.drop 7 =
      .block 0 0 formatPrepareOuterBody :: formatPrepareAfterOuter := by
  rfl

theorem formatPrepare_outer_shape :
    formatPrepareOuterBody =
      .block 0 0 formatPrepareMiddleBody :: formatPrepareAfterMiddle := by
  rfl

theorem formatPrepare_middle_shape :
    formatPrepareMiddleBody =
      .block 0 0 formatPrepareInnerBody :: formatPrepareStaticPath := by
  rfl

theorem formatPrepare_inner_shape :
    formatPrepareInnerBody =
      [.localGet 3, .const 1, .and, .const 1, .eq, .const 1, .and,
       .eqz, .br_if 0, .localGet 1, .load32 0, .localSet 4,
       .localGet 3, .const 1, .shrU, .localSet 5, .br 1] := by
  rfl

/-! Exact prefix of local `func34` (absolute 36).  It computes the 16-byte
scratch address, reads the second input word, and enters the generated outer
control block without interpreting either representation branch yet. -/
theorem formatPrepare_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr stackTop second : UInt32)
    (hinputRoom : inputPtr.toNat + 8 ≤ UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (inputPtr + 4) second ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (inputPtr + 4) second -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 inputPtr],
              formatPrepareLocals (stackTop - 16) second, []⟩,
            formatPrepareOuterBody, 0, [],
            formatPrepareOuterFrame :: controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 inputPtr],
          List.replicate 9 (.i32 0), []⟩,
        func34, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts inputPtr 4 8 hinputRoom (by decide)
  iintro ⟨Hglobal, Hsecond, Hdone⟩
  simp only [func34]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.replicate_succ, List.replicate_zero, List.set,
    List.length, Nat.sub_self]
  iapply twp_localGet rfl
  iapply twp_load32 second h40 h41 h42 h43 $$ Hsecond
  iintro Hsecond
  iapply twp_localSet rfl
  simp only [List.length, List.set]
  iapply twp_block
  simp only [List.drop_zero]
  isimp only [formatPrepareLocals, formatPrepareOuterBody,
    formatPrepareOuterFrame, formatPrepareAfterOuter, func34, List.drop] at Hdone
  iapply Hdone $$ Hglobal Hsecond

/-! The driver passes an aligned argument pointer as the second word.  This
exact pure-control rule follows the generated low-bit test through its two
nested blocks and lands at the static fallback loads. -/
theorem formatPrepare_aligned_dispatch_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr frame second : UInt32)
    (heven : second &&& 1 = 0)
    {R : IProp WasmHeapGF}
    {controls : List ControlFrame} {calls : List CallFrame} :
    R ∗
      (R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 inputPtr],
              formatPrepareLocals frame second, []⟩,
            formatPrepareStaticPath, 0, [],
            formatPrepareMiddleFrame :: formatPrepareOuterFrame :: controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 inputPtr],
          formatPrepareLocals frame second, []⟩,
        formatPrepareOuterBody, 0, [],
        formatPrepareOuterFrame :: controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [formatPrepareLocals, formatPrepareMiddleFrame,
    formatPrepareOuterFrame, formatPrepareMiddleBody,
    formatPrepareStaticPath, formatPrepareAfterMiddle,
    formatPrepareAfterOuter, formatPrepareOuterBody, func34, List.drop]
  iintro ⟨HR, Hdone⟩
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [heven]
  iapply twp_const
  iapply twp_eq (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (value := 0) (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ HR

/-! The aligned representation selects the two-word static formatting table.
This rule executes both static loads, copies them into the generated scratch
frame, and takes the depth-one branch to the outer continuation. -/
theorem formatPrepare_static_path_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr frame second staticFirst staticSecond : UInt32)
    (oldFrame4 oldFrame8 : UInt32)
    (hframeRoom : frame.toNat + 12 ≤ UInt32.size)
    {R : IProp WasmHeapGF}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 1049096 staticFirst ∗
      pointsTo_u32 1049100 staticSecond ∗
      pointsTo_u32 (frame + 4) oldFrame4 ∗
      pointsTo_u32 (frame + 8) oldFrame8 ∗ R ∗
      (pointsTo_u32 1049096 staticFirst ∗
        pointsTo_u32 1049100 staticSecond ∗
        pointsTo_u32 (frame + 4) staticFirst ∗
        pointsTo_u32 (frame + 8) staticSecond ∗ R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 inputPtr],
              formatPrepareStaticLocals frame second staticFirst staticSecond,
              []⟩,
            formatPrepareAfterOuter, 0, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 inputPtr],
          formatPrepareLocals frame second, []⟩,
        formatPrepareStaticPath, 0, [],
        formatPrepareMiddleFrame :: formatPrepareOuterFrame :: controls,
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts frame 4 12 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 12 hframeRoom (by decide)
  iintro ⟨HstaticFirst, HstaticSecond, Hframe4, Hframe8, HR, Hdone⟩
  simp only [formatPrepareStaticPath, formatPrepareMiddleBody,
    formatPrepareOuterBody, func34, List.drop]
  iapply twp_const
  ihave HstaticFirstAt :
      pointsTo_u32 ((0 : UInt32) + 1049096) staticFirst $$ [HstaticFirst]
  · rw [show (0 : UInt32) + 1049096 = 1049096 by decide]
    iexact HstaticFirst
  iapply twp_load32 staticFirst (by decide) (by decide) (by decide) (by decide) $$
    HstaticFirstAt
  iintro HstaticFirstAt
  iapply twp_localSet rfl
  simp only [formatPrepareLocals, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  ihave HstaticSecondAt :
      pointsTo_u32 ((0 : UInt32) + 1049100) staticSecond $$ [HstaticSecond]
  · rw [show (0 : UInt32) + 1049100 = 1049100 by decide]
    iexact HstaticSecond
  iapply twp_load32 staticSecond (by decide) (by decide) (by decide) (by decide) $$
    HstaticSecondAt
  iintro HstaticSecondAt
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFrame4 hf40 hf41 hf42 hf43 $$ Hframe4
  iintro Hframe4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFrame8 hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_br (by rfl)
  simp only [formatPrepareOuterFrame, formatPrepareAfterOuter,
    func34, List.drop, List.take_zero, List.nil_append]
  isimp only [formatPrepareStaticLocals, formatPrepareAfterOuter,
    formatPrepareMiddleFrame, formatPrepareOuterFrame,
    formatPrepareAfterMiddle, formatPrepareMiddleBody,
    formatPrepareOuterBody, func34, List.drop] at Hdone
  ihave HstaticFirst : pointsTo_u32 1049096 staticFirst $$ [HstaticFirstAt]
  · iapply pointsTo_u32_at_eq
      (show (0 : UInt32) + 1049096 = 1049096 by decide)
    iexact HstaticFirstAt
  ihave HstaticSecond : pointsTo_u32 1049100 staticSecond $$ [HstaticSecondAt]
  · iapply pointsTo_u32_at_eq
      (show (0 : UInt32) + 1049100 = 1049100 by decide)
    iexact HstaticSecondAt
  iapply Hdone
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  iexact HR

/-! The post-dispatch suffix repeats the generated representation check,
copies the static pair to the result area, and reaches the function return. -/
theorem formatPrepare_static_suffix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr frame second staticFirst staticSecond : UInt32)
    (oldFlag : UInt8) (oldResult0 oldResult4 : UInt32)
    (hframeRoom : frame.toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {R : IProp WasmHeapGF}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 1049096 staticFirst ∗
      pointsTo_u32 1049100 staticSecond ∗
      pointsTo_u32 (frame + 4) staticFirst ∗
      pointsTo_u32 (frame + 8) staticSecond ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (frame + 15) (DFrac.own 1) (some oldFlag) ∗
      pointsTo_u32 resultPtr oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗ R ∗
      (pointsTo_u32 1049096 staticFirst ∗
        pointsTo_u32 1049100 staticSecond ∗
        pointsTo_u32 (frame + 4) staticFirst ∗
        pointsTo_u32 (frame + 8) staticSecond ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (frame + 15) (DFrac.own 1) (some (0 : UInt8)) ∗
        pointsTo_u32 resultPtr staticFirst ∗
        pointsTo_u32 (resultPtr + 4) staticSecond ∗ R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 inputPtr],
              formatPrepareFinalLocals frame second staticFirst staticSecond,
              []⟩,
            [.ret], 0, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 inputPtr],
          formatPrepareStaticLocals frame second staticFirst staticSecond,
          []⟩,
        formatPrepareAfterOuter, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hf15 : (frame + 15).toNat = frame.toNat + 15 := by
    apply UInt32.add_ofNat_toNat_noWrap
    · decide
    · simp only [UInt32.size] at hframeRoom ⊢
      omega
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts frame 4 16 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 16 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    descriptorSlot32Facts resultPtr 0 8 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 8 hresultRoom (by decide)
  iintro ⟨HstaticFirst, HstaticSecond, Hframe4, Hframe8, Hflag,
    Hresult0, Hresult4, HR, Hdone⟩
  simp only [formatPrepareAfterOuter, func34, List.drop]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_owned oldFlag hf15 $$ Hflag
  iintro Hflag
  rw [show (0 : UInt32).toUInt8 = (0 : UInt8) by decide]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_load8U_owned 0 hf15 $$ Hflag
  iintro Hflag
  rw [show (0 : UInt8).toUInt32 = (0 : UInt32) by decide]
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_const
  ihave HstaticFirstAt :
      pointsTo_u32 ((0 : UInt32) + 1049096) staticFirst $$ [HstaticFirst]
  · iapply pointsTo_u32_at_eq
      (show 1049096 = (0 : UInt32) + 1049096 by decide)
    iexact HstaticFirst
  iapply twp_load32 staticFirst (by decide) (by decide) (by decide) (by decide) $$
    HstaticFirstAt
  iintro HstaticFirstAt
  iapply twp_localSet rfl
  simp only [formatPrepareStaticLocals, List.set, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  ihave HstaticSecondAt :
      pointsTo_u32 ((0 : UInt32) + 1049100) staticSecond $$ [HstaticSecond]
  · iapply pointsTo_u32_at_eq
      (show 1049100 = (0 : UInt32) + 1049100 by decide)
    iexact HstaticSecond
  iapply twp_load32 staticSecond (by decide) (by decide) (by decide) (by decide) $$
    HstaticSecondAt
  iintro HstaticSecondAt
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 staticFirst hf40 hf41 hf42 hf43 $$ Hframe4
  iintro Hframe4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 staticSecond hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 staticFirst hf40 hf41 hf42 hf43 $$ Hframe4
  iintro Hframe4
  iapply twp_localSet rfl
  simp only [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 staticSecond hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_store32 oldResult4 hr40 hr41 hr42 hr43 $$ Hresult4
  iintro Hresult4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hresult0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hresult0]
  · iapply pointsTo_u32_at_eq
      (show resultPtr = resultPtr + 0 by bv_decide)
    iexact Hresult0
  iapply twp_store32 oldResult0 hr0 hr1 hr2 hr3 $$ Hresult0At
  iintro Hresult0At
  ihave Hresult0 : pointsTo_u32 resultPtr staticFirst $$ [Hresult0At]
  · iapply pointsTo_u32_at_eq
      (show resultPtr + 0 = resultPtr by bv_decide)
    iexact Hresult0At
  isimp only [formatPrepareFinalLocals] at Hdone
  ihave HstaticFirst : pointsTo_u32 1049096 staticFirst $$ [HstaticFirstAt]
  · iapply pointsTo_u32_at_eq
      (show (0 : UInt32) + 1049096 = 1049096 by decide)
    iexact HstaticFirstAt
  ihave HstaticSecond : pointsTo_u32 1049100 staticSecond $$ [HstaticSecondAt]
  · iapply pointsTo_u32_at_eq
      (show (0 : UInt32) + 1049100 = 1049100 by decide)
    iexact HstaticSecondAt
  iapply Hdone
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hflag]
  · iexact Hflag
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  iexact HR

/-! Full aligned successful body contract for generated local `func34`. -/
theorem formatPrepare_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr stackTop second staticFirst staticSecond : UInt32)
    (oldFrame4 oldFrame8 oldResult0 oldResult4 : UInt32)
    (oldFlag : UInt8)
    (heven : second &&& 1 = 0)
    (hinputRoom : inputPtr.toNat + 8 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {R : IProp WasmHeapGF}
    {controls : List ControlFrame} {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (inputPtr + 4) second ∗
      pointsTo_u32 1049096 staticFirst ∗
      pointsTo_u32 1049100 staticSecond ∗
      pointsTo_u32 ((stackTop - 16) + 4) oldFrame4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((stackTop - 16) + 15) (DFrac.own 1) (some oldFlag) ∗
      pointsTo_u32 resultPtr oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗ R ∗
      (globalPointsTo 0 (.i32 stackTop) ∗
        pointsTo_u32 (inputPtr + 4) second ∗
        pointsTo_u32 1049096 staticFirst ∗
        pointsTo_u32 1049100 staticSecond ∗
        pointsTo_u32 ((stackTop - 16) + 4) staticFirst ∗
        pointsTo_u32 ((stackTop - 16) + 8) staticSecond ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          ((stackTop - 16) + 15) (DFrac.own 1) (some (0 : UInt8)) ∗
        pointsTo_u32 resultPtr staticFirst ∗
        pointsTo_u32 (resultPtr + 4) staticSecond ∗ R -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 inputPtr],
              formatPrepareFinalLocals (stackTop - 16) second
                staticFirst staticSecond, []⟩,
            [.ret], 0, [], controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 inputPtr],
          List.replicate 9 (.i32 0), []⟩,
        func34, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hframeRoom12 : (stackTop - 16).toNat + 12 ≤ UInt32.size := by
    omega
  iintro ⟨Hglobal, Hsecond, HstaticFirst, HstaticSecond, Hframe4,
    Hframe8, Hflag, Hresult0, Hresult4, HR, Hdone⟩
  iapply formatPrepare_prefix_twp resultPtr inputPtr stackTop second hinputRoom
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hsecond]
  · iexact Hsecond
  iintro Hglobal Hsecond
  iapply formatPrepare_aligned_dispatch_twp
    resultPtr inputPtr (stackTop - 16) second heven (R := R)
  isplitl [HR]
  · iexact HR
  iintro HR
  iapply formatPrepare_static_path_twp resultPtr inputPtr (stackTop - 16)
    second staticFirst staticSecond oldFrame4 oldFrame8 hframeRoom12
    (R := R)
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [HR]
  · iexact HR
  iintro ⟨HstaticFirst, HstaticSecond, Hframe4, Hframe8, HR⟩
  iapply formatPrepare_static_suffix_twp resultPtr inputPtr (stackTop - 16)
    second staticFirst staticSecond oldFlag oldResult0 oldResult4
    hframeRoom hresultRoom (R := R)
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hflag]
  · iexact Hflag
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  isplitl [HR]
  · iexact HR
  iintro ⟨HstaticFirst, HstaticSecond, Hframe4, Hframe8, Hflag,
    Hresult0, Hresult4, HR⟩
  iapply Hdone
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hsecond]
  · iexact Hsecond
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hflag]
  · iexact Hflag
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  iexact HR

/-! Composable absolute-index-36 wrapper for the aligned `func34` path. -/
theorem formatPrepare_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr inputPtr stackTop second staticFirst staticSecond : UInt32)
    (oldFrame4 oldFrame8 oldResult0 oldResult4 : UInt32)
    (oldFlag : UInt8)
    (heven : second &&& 1 = 0)
    (hinputRoom : inputPtr.toNat + 8 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {R : IProp WasmHeapGF}
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (inputPtr + 4) second ∗
      pointsTo_u32 1049096 staticFirst ∗
      pointsTo_u32 1049100 staticSecond ∗
      pointsTo_u32 ((stackTop - 16) + 4) oldFrame4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((stackTop - 16) + 15) (DFrac.own 1) (some oldFlag) ∗
      pointsTo_u32 resultPtr oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗ R ∗
      (runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 stackTop) ∗
        pointsTo_u32 (inputPtr + 4) second ∗
        pointsTo_u32 1049096 staticFirst ∗
        pointsTo_u32 1049100 staticSecond ∗
        pointsTo_u32 ((stackTop - 16) + 4) staticFirst ∗
        pointsTo_u32 ((stackTop - 16) + 8) staticSecond ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          ((stackTop - 16) + 15) (DFrac.own 1) (some (0 : UInt8)) ∗
        pointsTo_u32 resultPtr staticFirst ∗
        pointsTo_u32 (resultPtr + 4) staticSecond ∗ R -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 inputPtr, .i32 resultPtr] ++ stack },
        .call 36 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hsecond, HstaticFirst, HstaticSecond,
    Hframe4, Hframe8, Hflag, Hresult0, Hresult4, HR, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 36 func34Def
      (by decide) formatPrepare_index $$ Hruntime
  iintro Hruntime
  simp [func34Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := formatPrepare_body_twp (α := α)
    resultPtr inputPtr stackTop second staticFirst staticSecond
    oldFrame4 oldFrame8 oldResult0 oldResult4 oldFlag heven
    hinputRoom hframeRoom hresultRoom
    (s := s) (E := E) (Φ := Φ) (R := R)
    (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [List.replicate_succ, List.replicate_zero] at Hbody
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hsecond]
  · iexact Hsecond
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hflag]
  · iexact Hflag
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  isplitl [HR]
  · iexact HR
  iintro ⟨Hglobal, Hsecond, HstaticFirst, HstaticSecond, Hframe4,
    Hframe8, Hflag, Hresult0, Hresult4, HR⟩
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hsecond]
  · iexact Hsecond
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hframe4]
  · iexact Hframe4
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hflag]
  · iexact Hflag
  isplitl [Hresult0]
  · iexact Hresult0
  isplitl [Hresult4]
  · iexact Hresult4
  iexact HR

def writeFmtFallbackOuterBody : Program :=
  match func33.drop 34 with
  | .block _ _ body :: _ => body
  | _ => []

def writeFmtFallbackAfterOuter : Program := func33.drop 35

def writeFmtFallbackFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := writeFmtFallbackOuterBody
    continuation := writeFmtFallbackAfterOuter
    belowStack := [] }

def writeFmtAtFallbackCall : Program := [.call 30]

def writeFmtFallbackLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0]

/-! Compose the generated format preparation call and the zero-static-table
dispatch.  The result is the exact fallback call to local `func28` at absolute
index 30. -/
theorem writeFmt_prepare_to_fallback_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writerPtr formatPtr argumentsPtr frame : UInt32)
    (oldHelper4 oldHelper8 oldResult8 oldResult12 oldFrame24 oldFrame28 : UInt32)
    (oldHelperFlag : UInt8)
    (hargumentsEven : argumentsPtr &&& 1 = 0)
    (hinputRoom : (frame + 16).toNat + 8 ≤ UInt32.size)
    (hhelperRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : (frame + 8).toNat + 8 ≤ UInt32.size)
    (hframeRoom : frame.toNat + 32 ≤ UInt32.size)
    {R : IProp WasmHeapGF}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 1049096 0 ∗ pointsTo_u32 1049100 0 ∗
      pointsTo_u32 ((frame - 16) + 4) oldHelper4 ∗
      pointsTo_u32 ((frame - 16) + 8) oldHelper8 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((frame - 16) + 15) (DFrac.own 1) (some oldHelperFlag) ∗
      pointsTo_u32 (frame + 8) oldResult8 ∗
      pointsTo_u32 (frame + 12) oldResult12 ∗
      pointsTo_u32 (frame + 16) formatPtr ∗
      pointsTo_u32 (frame + 20) argumentsPtr ∗
      pointsTo_u32 (frame + 24) oldFrame24 ∗
      pointsTo_u32 (frame + 28) oldFrame28 ∗ R ∗
      (runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 frame) ∗
        pointsTo_u32 1049096 0 ∗ pointsTo_u32 1049100 0 ∗
        pointsTo_u32 ((frame - 16) + 4) 0 ∗
        pointsTo_u32 ((frame - 16) + 8) 0 ∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          ((frame - 16) + 15) (DFrac.own 1) (some (0 : UInt8)) ∗
        pointsTo_u32 (frame + 8) 0 ∗
        pointsTo_u32 (frame + 12) 0 ∗
        pointsTo_u32 (frame + 16) formatPtr ∗
        pointsTo_u32 (frame + 20) argumentsPtr ∗
        pointsTo_u32 (frame + 24) 0 ∗ pointsTo_u32 (frame + 28) 0 ∗ R -∗
        WP (.running
          ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
              writeFmtFallbackLocals frame,
              [.i32 argumentsPtr, .i32 formatPtr,
               .i32 writerPtr, .i32 resultPtr]⟩,
            writeFmtAtFallbackCall, 0, [],
            writeFmtFallbackFrame :: controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
          writeFmtLocals frame,
          [.i32 (frame + 16), .i32 (frame + 8)]⟩,
        writeFmtAtPrepare, 0, [], controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simp only [writeFmtParams, writeFmtLocals]
  obtain ⟨h80, h81, h82, h83⟩ :=
    descriptorSlot32Facts frame 8 32 hframeRoom (by decide)
  obtain ⟨h120, h121, h122, h123⟩ :=
    descriptorSlot32Facts frame 12 32 hframeRoom (by decide)
  obtain ⟨h160, h161, h162, h163⟩ :=
    descriptorSlot32Facts frame 16 32 hframeRoom (by decide)
  obtain ⟨h200, h201, h202, h203⟩ :=
    descriptorSlot32Facts frame 20 32 hframeRoom (by decide)
  obtain ⟨h240, h241, h242, h243⟩ :=
    descriptorSlot32Facts frame 24 32 hframeRoom (by decide)
  obtain ⟨h280, h281, h282, h283⟩ :=
    descriptorSlot32Facts frame 28 32 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, HstaticFirst, HstaticSecond, Hhelper4,
    Hhelper8, HhelperFlag, Hresult8, Hresult12, Hformat, Harguments,
    Hframe24, Hframe28, HR, Hdone⟩
  ihave HargumentsAt : pointsTo_u32 ((frame + 16) + 4) argumentsPtr $$
      [Harguments]
  · iapply pointsTo_u32_at_eq
      (show frame + 20 = (frame + 16) + 4 by bv_decide)
    iexact Harguments
  ihave Hresult12At : pointsTo_u32 ((frame + 8) + 4) oldResult12 $$
      [Hresult12]
  · iapply pointsTo_u32_at_eq
      (show frame + 12 = (frame + 8) + 4 by bv_decide)
    iexact Hresult12
  rw [writeFmtAtPrepare_eq]
  have Hprepare := formatPrepare_call_twp (α := α)
    (frame + 8) (frame + 16) frame argumentsPtr
    0 0 oldHelper4 oldHelper8 oldResult8 oldResult12 oldHelperFlag
    hargumentsEven hinputRoom hhelperRoom hresultRoom (R := R)
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
        writeFmtLocals frame, []⟩)
    (stack := []) (code := writeFmtAfterPrepare) (arity := 0)
    (remainder := []) (controls := controls) (calls := calls)
  simp only [List.append_nil, writeFmtParams, writeFmtLocals] at Hprepare
  iapply Hprepare
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [HargumentsAt]
  · iexact HargumentsAt
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hhelper4]
  · iexact Hhelper4
  isplitl [Hhelper8]
  · iexact Hhelper8
  isplitl [HhelperFlag]
  · iexact HhelperFlag
  isplitl [Hresult8]
  · iexact Hresult8
  isplitl [Hresult12At]
  · iexact Hresult12At
  isplitl [HR]
  · iexact HR
  iintro ⟨Hruntime, Hglobal, Harguments, HstaticFirst, HstaticSecond,
    Hhelper4, Hhelper8, HhelperFlag, Hresult8, Hresult12, HR⟩
  ihave Harguments' : pointsTo_u32 (frame + 20) argumentsPtr $$ [Harguments]
  · iapply pointsTo_u32_at_eq
      (show (frame + 16) + 4 = frame + 20 by bv_decide)
    iexact Harguments
  ihave Hresult12' : pointsTo_u32 (frame + 12) 0 $$ [Hresult12]
  · iapply pointsTo_u32_at_eq
      (show (frame + 8) + 4 = frame + 12 by bv_decide)
    iexact Hresult12
  simp only [writeFmtAfterPrepare, func33, List.drop]
  iapply twp_localGet rfl
  iapply twp_load32 0 h120 h121 h122 h123 $$ Hresult12'
  iintro Hresult12
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 0 h80 h81 h82 h83 $$ Hresult8
  iintro Hresult8
  iapply twp_store32 oldFrame24 h240 h241 h242 h243 $$ Hframe24
  iintro Hframe24
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFrame28 h280 h281 h282 h283 $$ Hframe28
  iintro Hframe28
  iapply twp_localGet rfl
  iapply twp_load32 0 h240 h241 h242 h243 $$ Hframe24
  iintro Hframe24
  iapply twp_localSet rfl
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (value := 0) (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 formatPtr h160 h161 h162 h163 $$ Hformat
  iintro Hformat
  iapply twp_localGet rfl
  iapply twp_load32 argumentsPtr h200 h201 h202 h203 $$ Harguments'
  iintro Harguments
  simp only [List.length, List.set]
  isimp only [writeFmtParams, writeFmtLocals, writeFmtFallbackLocals,
    writeFmtAtFallbackCall,
    writeFmtFallbackFrame, writeFmtFallbackOuterBody,
    writeFmtFallbackAfterOuter, func33, List.drop, List.set,
    List.length] at Hdone
  iapply Hdone
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [HstaticFirst]
  · iexact HstaticFirst
  isplitl [HstaticSecond]
  · iexact HstaticSecond
  isplitl [Hhelper4]
  · iexact Hhelper4
  isplitl [Hhelper8]
  · iexact Hhelper8
  isplitl [HhelperFlag]
  · iexact HhelperFlag
  isplitl [Hresult8]
  · iexact Hresult8
  isplitl [Hresult12]
  · iexact Hresult12
  isplitl [Hformat]
  · iexact Hformat
  isplitl [Harguments]
  · iexact Harguments
  isplitl [Hframe24]
  · iexact Hframe24
  isplitl [Hframe28]
  · iexact Hframe28
  iexact HR

/-! Exact generated prologue of local `func33`, through both saved argument
stores and both operands for absolute call 36. -/
theorem writeFmt_to_prepare_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writerPtr formatPtr argumentsPtr stackTop : UInt32)
    (oldFormat oldArguments : UInt32)
    (hframeRoom : (stackTop - 32).toNat + 24 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 16) oldFormat ∗
      pointsTo_u32 ((stackTop - 32) + 20) oldArguments ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        pointsTo_u32 ((stackTop - 32) + 16) formatPtr -∗
        pointsTo_u32 ((stackTop - 32) + 20) argumentsPtr -∗
        WP (.running
          ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
              writeFmtLocals (stackTop - 32),
              [.i32 ((stackTop - 32) + 16),
               .i32 ((stackTop - 32) + 8)]⟩,
            writeFmtAtPrepare, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
          [.i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func33, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let frame := stackTop - 32
  obtain ⟨h160, h161, h162, h163⟩ :=
    descriptorSlot32Facts frame 16 24 hframeRoom (by decide)
  obtain ⟨h200, h201, h202, h203⟩ :=
    descriptorSlot32Facts frame 20 24 hframeRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hformat, Harguments, Hdone⟩
  simp only [func33]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [writeFmtParams, List.length, Nat.sub_self, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFormat h160 h161 h162 h163 $$ Hformat
  iintro Hformat
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldArguments h200 h201 h202 h203 $$ Harguments
  iintro Harguments
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 8 frame]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 16 frame]
  isimp only [writeFmtParams, writeFmtLocals, writeFmtAtPrepare, func33,
    List.drop] at Hdone
  iapply Hdone $$ Hruntime Hglobal Hformat Harguments

/-! Absolute-index-35 entry rule, composable from the generated driver.  It
enters `func33`, runs the proved prologue, and exposes the exact callee state
at absolute call 36. -/
theorem writeFmt_call_to_prepare_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writerPtr formatPtr argumentsPtr stackTop : UInt32)
    (oldFormat oldArguments : UInt32)
    (hframeRoom : (stackTop - 32).toNat + 24 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 16) oldFormat ∗
      pointsTo_u32 ((stackTop - 32) + 20) oldArguments ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        pointsTo_u32 ((stackTop - 32) + 16) formatPtr -∗
        pointsTo_u32 ((stackTop - 32) + 20) argumentsPtr -∗
        WP (.running
          ⟨⟨writeFmtParams resultPtr writerPtr formatPtr argumentsPtr,
              writeFmtLocals (stackTop - 32),
              [.i32 ((stackTop - 32) + 16),
               .i32 ((stackTop - 32) + 8)]⟩,
            writeFmtAtPrepare, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 argumentsPtr, .i32 formatPtr, .i32 writerPtr,
           .i32 resultPtr] ++ stack },
        .call 35 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hformat, Harguments, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 35 func33Def
      (by decide) writeFmt_index $$ Hruntime
  iintro Hruntime
  simp [func33Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := writeFmt_to_prepare_call_twp (α := α)
    resultPtr writerPtr formatPtr argumentsPtr stackTop
    oldFormat oldArguments hframeRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [writeFmtParams] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hformat]
  · iexact Hformat
  isplitl [Harguments]
  · iexact Harguments
  iintro Hruntime Hglobal Hformat Harguments
  isimp only [writeFmtParams] at Hdone
  iapply Hdone $$ Hruntime Hglobal Hformat Harguments

/-! ## The fallback formatter `func28` (absolute call 30)

`func28` adapts the writer into the two-word output state consumed by
`core::fmt::write` (local `func211`, absolute call 213) and dispatches to it
with the static vtable 1048856.  The rules below cover its exact prologue up
to that call and its successful return path; the formatter call itself stays
an explicit boundary. -/

theorem fallbackFormatter_index : «module».funcs[28]? = some func28Def := by
  rfl

theorem checkFormatResult_index : «module».funcs[29]? = some func29Def := by
  rfl

/-- Overwrite the low byte of a 64-bit word, as `i32.store8` does to an
owned `Result` slot. -/
def withLowByte (value : UInt64) (byte : UInt8) : UInt64 :=
  (value &&& 0xFFFFFFFFFFFFFF00) ||| byte.toUInt64

private theorem u64Byte_withLowByte_zero (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 0 = byte := by
  unfold u64Byte withLowByte
  bv_decide

private theorem u64Byte_withLowByte_one (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 1 = u64Byte value 1 := by
  unfold u64Byte withLowByte
  bv_decide

private theorem u64Byte_withLowByte_two (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 2 = u64Byte value 2 := by
  unfold u64Byte withLowByte
  bv_decide

private theorem u64Byte_withLowByte_three (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 3 = u64Byte value 3 := by
  unfold u64Byte withLowByte
  bv_decide

private theorem u64Byte_withLowByte_four (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 4 = u64Byte value 4 := by
  unfold u64Byte withLowByte
  bv_decide

private theorem u64Byte_withLowByte_five (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 5 = u64Byte value 5 := by
  unfold u64Byte withLowByte
  bv_decide

private theorem u64Byte_withLowByte_six (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 6 = u64Byte value 6 := by
  unfold u64Byte withLowByte
  bv_decide

private theorem u64Byte_withLowByte_seven (value : UInt64) (byte : UInt8) :
    u64Byte (withLowByte value byte) 7 = u64Byte value 7 := by
  unfold u64Byte withLowByte
  bv_decide

private theorem pointsTo_byte_at_eq
    [WasmSmallStepGS hlc] {address address' : UInt32} {byte : UInt8}
    (haddress : address = address') :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some byte) ⊢
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address' (DFrac.own 1) (some byte) := by
  rw [haddress]

private theorem pointsTo_u64_at_eq
    [WasmSmallStepGS hlc] {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 address value ⊢ pointsTo_u64 address' value := by
  rw [haddress]

/-- Exact total body rule for generated local `func29` when the observed
`Result` byte is 4 (`Ok`): the function reads the byte and returns without
further effects. -/
theorem checkFormatResult_ok_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (statePtr : UInt32)
    {calls : List CallFrame} :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        statePtr (DFrac.own 1) (some (4 : UInt8)) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          statePtr (DFrac.own 1) (some (4 : UInt8)) -∗
        WP (.running
          ⟨⟨[.i32 statePtr], [.i32 4, .i32 4, .i32 1], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 statePtr], List.replicate 3 (.i32 0), []⟩,
        func29, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have hnowrap : (statePtr + (0 : UInt32)).toNat =
      statePtr.toNat + (0 : UInt32).toNat := by
    rw [show statePtr + (0 : UInt32) = statePtr by bv_decide]
    simp
  iintro ⟨Hstate, Hdone⟩
  simp only [func29, List.replicate_succ, List.replicate_zero]
  iapply twp_localGet rfl
  ihave HstateAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (statePtr + 0) (DFrac.own 1) (some (4 : UInt8)) $$ [Hstate]
  · iapply pointsTo_byte_at_eq (show statePtr = statePtr + 0 by bv_decide)
    iexact Hstate
  iapply twp_load8U_owned 4 hnowrap $$ HstateAt
  iintro HstateAt
  rw [show (4 : UInt8).toUInt32 = (4 : UInt32) by decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (4 : UInt32) &&& 255 = 4 by decide]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (4 : UInt32) &&& 255 = 4 by decide]
  iapply twp_eq (result := 1) (by decide)
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_const
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_selectI32 (selected := 0) (by decide)
  iapply twp_eqz (value := 0) (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  ihave Hstate : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      statePtr (DFrac.own 1) (some (4 : UInt8)) $$ [HstateAt]
  · iapply pointsTo_byte_at_eq (show statePtr + 0 = statePtr by bv_decide)
    iexact HstateAt
  iapply Hdone $$ Hstate

/-- Composable total call rule for `func29` at absolute Wasm index `31`,
along the `Ok` path. -/
theorem checkFormatResult_ok_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (statePtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        statePtr (DFrac.own 1) (some (4 : UInt8)) ∗
      (runtimeModuleOwn «module» -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          statePtr (DFrac.own 1) (some (4 : UInt8)) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 statePtr] ++ stack },
        .call 31 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hstate, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 31 func29Def
      (by decide) checkFormatResult_index $$ Hruntime
  iintro Hruntime
  simp [func29Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := checkFormatResult_ok_body_twp (α := α) statePtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [List.replicate_succ, List.replicate_zero] at Hbody
  iapply Hbody
  isplitl [Hstate]
  · iexact Hstate
  iintro Hstate
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hstate

/-! ### Exact block skeleton of `func28` -/

def fallbackParams
    (resultPtr writerPtr formatPtr argumentsPtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 writerPtr, .i32 formatPtr, .i32 argumentsPtr]

def fallbackLocals (frame : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 0, .i32 0]

def fallbackOuterBody : Program :=
  match func28.drop 16 with
  | .block _ _ body :: _ => body
  | _ => []

def fallbackAfterOuter : Program := func28.drop 17

def fallbackPanicBody : Program :=
  match fallbackOuterBody with
  | .block _ _ body :: _ => body
  | _ => []

def fallbackAfterPanic : Program := fallbackOuterBody.drop 1

def fallbackCheckBody : Program :=
  match fallbackPanicBody with
  | .block _ _ body :: _ => body
  | _ => []

def fallbackAfterCheck : Program := fallbackPanicBody.drop 1

def fallbackWriteBody : Program :=
  match fallbackCheckBody with
  | .block _ _ body :: _ => body
  | _ => []

def fallbackAfterWrite : Program := fallbackCheckBody.drop 1

/-- The exact code of `func28` from its `core::fmt::write` dispatch. -/
def fallbackAtWrite : Program := fallbackWriteBody.drop 4

def fallbackOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fallbackOuterBody
    continuation := fallbackAfterOuter
    belowStack := [] }

def fallbackPanicFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fallbackPanicBody
    continuation := fallbackAfterPanic
    belowStack := [] }

def fallbackCheckFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fallbackCheckBody
    continuation := fallbackAfterCheck
    belowStack := [] }

def fallbackWriteFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fallbackWriteBody
    continuation := fallbackAfterWrite
    belowStack := [] }

theorem fallbackAtWrite_eq :
    fallbackAtWrite =
      .call 213 :: fallbackWriteBody.drop 5 := by
  rfl

theorem fallbackAfterWrite_eq :
    fallbackAfterWrite = [.localGet 4, .call 31, .br 2] := by
  rfl

/-- Exact prologue of generated local `func28` up to the `core::fmt::write`
dispatch (absolute call 213): it primes the `Result` slot with the `Ok`
byte 4, builds the two-word output state `{ copied result word, writer }`
in its shadow frame, and stops with the four operands for the formatter
call on the stack.  The formatter call remains an explicit boundary. -/
theorem fallback_to_write_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writerPtr formatPtr argumentsPtr stackTop : UInt32)
    (oldResult oldScratch : UInt64) (oldFrame8 : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u64 resultPtr oldResult ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u64 (stackTop - 16) oldScratch ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        pointsTo_u64 resultPtr (withLowByte oldResult 4) -∗
        pointsTo_u32 ((stackTop - 16) + 8) writerPtr -∗
        pointsTo_u64 (stackTop - 16) (withLowByte oldResult 4) -∗
        WP (.running
          ⟨⟨fallbackParams resultPtr writerPtr formatPtr argumentsPtr,
              fallbackLocals (stackTop - 16),
              [.i32 argumentsPtr, .i32 formatPtr, .i32 1048856,
               .i32 (stackTop - 16)]⟩,
            fallbackAtWrite, 0, [],
            [fallbackWriteFrame, fallbackCheckFrame, fallbackPanicFrame,
             fallbackOuterFrame], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fallbackParams resultPtr writerPtr formatPtr argumentsPtr,
          List.replicate 4 (.i32 0), []⟩,
        func28, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have hstore8 : (resultPtr + (0 : UInt32)).toNat =
      resultPtr.toNat + (0 : UInt32).toNat := by
    rw [show resultPtr + (0 : UInt32) = resultPtr by bv_decide]
    simp
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
    descriptorSlot64Facts resultPtr 0 8 hresultRoom (by decide)
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ :=
    descriptorSlot64Facts (stackTop - 16) 0 16 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hframeRoom (by decide)
  iintro ⟨Hglobal, Hresult, Hframe8, Hscratch, Hdone⟩
  simp only [func28, fallbackParams, List.replicate_succ,
    List.replicate_zero]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_const
  isimp only [pointsTo_u64] at Hresult
  icases Hresult with ⟨Hr0, Hr1, Hr2, Hr3, Hr4, Hr5, Hr6, Hr7⟩
  ihave Hr0At : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (resultPtr + 0) (DFrac.own 1) (some (u64Byte oldResult 0)) $$ [Hr0]
  · iapply pointsTo_byte_at_eq (show resultPtr = resultPtr + 0 by bv_decide)
    iexact Hr0
  iapply twp_store8_owned (u64Byte oldResult 0) hstore8 $$ Hr0At
  iintro Hr0At
  rw [show (4 : UInt32).toUInt8 = (4 : UInt8) by decide]
  ihave Hr0 : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      resultPtr (DFrac.own 1) (some (4 : UInt8)) $$ [Hr0At]
  · iapply pointsTo_byte_at_eq (show resultPtr + 0 = resultPtr by bv_decide)
    iexact Hr0At
  ihave Hresult : pointsTo_u64 resultPtr (withLowByte oldResult 4) $$
      [Hr0 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7]
  · isimp only [pointsTo_u64]
    rw [u64Byte_withLowByte_zero, u64Byte_withLowByte_one,
      u64Byte_withLowByte_two, u64Byte_withLowByte_three,
      u64Byte_withLowByte_four, u64Byte_withLowByte_five,
      u64Byte_withLowByte_six, u64Byte_withLowByte_seven]
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFrame8 hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HresultAt : pointsTo_u64 (resultPtr + 0)
      (withLowByte oldResult 4) $$ [Hresult]
  · iapply pointsTo_u64_at_eq (show resultPtr = resultPtr + 0 by bv_decide)
    iexact Hresult
  iapply twp_load64 (withLowByte oldResult 4)
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 $$ HresultAt
  iintro HresultAt
  ihave HscratchAt : pointsTo_u64 ((stackTop - 16) + 0) oldScratch $$
      [Hscratch]
  · iapply pointsTo_u64_at_eq
      (show stackTop - 16 = (stackTop - 16) + 0 by bv_decide)
    iexact Hscratch
  iapply twp_store64 oldScratch hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 $$
    HscratchAt
  iintro HscratchAt
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hresult : pointsTo_u64 resultPtr (withLowByte oldResult 4) $$
      [HresultAt]
  · iapply pointsTo_u64_at_eq (show resultPtr + 0 = resultPtr by bv_decide)
    iexact HresultAt
  ihave Hscratch : pointsTo_u64 (stackTop - 16)
      (withLowByte oldResult 4) $$ [HscratchAt]
  · iapply pointsTo_u64_at_eq
      (show (stackTop - 16) + 0 = stackTop - 16 by bv_decide)
    iexact HscratchAt
  isimp only [fallbackParams, fallbackLocals, fallbackAtWrite,
    fallbackWriteFrame, fallbackWriteBody, fallbackAfterWrite,
    fallbackCheckFrame, fallbackCheckBody, fallbackAfterCheck,
    fallbackPanicFrame, fallbackPanicBody, fallbackAfterPanic,
    fallbackOuterFrame, fallbackOuterBody, fallbackAfterOuter,
    func28, List.drop] at Hdone
  iapply Hdone $$ Hglobal Hresult Hframe8 Hscratch

/-- Exact successful return path of generated local `func28`, from the
instant `core::fmt::write` (absolute call 213) has returned 0: the generated
code re-checks the copied `Ok` byte through local `func29`, branches over the
error and panic arms, restores the shadow stack, and returns.  The `Result`
slot keeps the `Ok` byte 4 written by the prologue, and no host call
occurs. -/
theorem fallback_success_return_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writerPtr formatPtr argumentsPtr stackTop : UInt32)
    (scratch : UInt64)
    (hbyte : u64Byte scratch 0 = 4)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 (stackTop - 16)) ∗
      pointsTo_u64 (stackTop - 16) scratch ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u64 (stackTop - 16) scratch -∗
        WP (.running
          ⟨⟨fallbackParams resultPtr writerPtr formatPtr argumentsPtr,
              fallbackLocals (stackTop - 16), []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fallbackParams resultPtr writerPtr formatPtr argumentsPtr,
          fallbackLocals (stackTop - 16), [.i32 0]⟩,
        fallbackWriteBody.drop 5, 0, [],
        [fallbackWriteFrame, fallbackCheckFrame, fallbackPanicFrame,
         fallbackOuterFrame], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hscratch, Hdone⟩
  simp only [fallbackParams, fallbackLocals, fallbackWriteFrame,
    fallbackCheckFrame, fallbackPanicFrame, fallbackOuterFrame,
    fallbackWriteBody, fallbackAfterWrite, fallbackCheckBody,
    fallbackAfterCheck, fallbackPanicBody, fallbackAfterPanic,
    fallbackOuterBody, fallbackAfterOuter, func28, List.drop]
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (value := 0) (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  isimp only [pointsTo_u64] at Hscratch
  icases Hscratch with ⟨Hs0, Hs1, Hs2, Hs3, Hs4, Hs5, Hs6, Hs7⟩
  ihave Hs0' : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (stackTop - 16) (DFrac.own 1) (some (4 : UInt8)) $$ [Hs0]
  · rw [hbyte]
    iexact Hs0
  have Hcall := checkFormatResult_ok_call_twp (α := α)
    (stackTop - 16)
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 resultPtr, .i32 writerPtr, .i32 formatPtr,
        .i32 argumentsPtr],
        [.i32 (stackTop - 16), .i32 0, .i32 0, .i32 0], []⟩)
    (stack := [])
    (code := [.br 2])
    (arity := 0) (remainder := [])
    (controls :=
      [{ kind := .block
         paramArity := 0
         resultArity := 0
         body := fallbackCheckBody
         continuation := fallbackAfterCheck
         belowStack := [] },
       { kind := .block
         paramArity := 0
         resultArity := 0
         body := fallbackPanicBody
         continuation := fallbackAfterPanic
         belowStack := [] },
       { kind := .block
         paramArity := 0
         resultArity := 0
         body := fallbackOuterBody
         continuation := fallbackAfterOuter
         belowStack := [] }])
    (calls := calls)
  simp only [List.append_nil, fallbackCheckBody, fallbackAfterCheck,
    fallbackPanicBody, fallbackAfterPanic, fallbackOuterBody,
    fallbackAfterOuter, func28, List.drop] at Hcall
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hs0']
  · iexact Hs0'
  iintro Hruntime Hs0'
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 16 (stackTop - 16),
    show (stackTop - 16) + 16 = stackTop by bv_decide]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave Hs0 : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (stackTop - 16) (DFrac.own 1) (some (u64Byte scratch 0)) $$ [Hs0']
  · rw [hbyte]
    iexact Hs0'
  ihave Hscratch : pointsTo_u64 (stackTop - 16) scratch $$
      [Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7]
  · isimp only [pointsTo_u64]
    iframe
  iapply Hdone $$ Hruntime Hglobal Hscratch

/-! ## `core::fmt::write` (`func211`, absolute call 213)

The compact-bytecode interpreter for `fmt::Arguments`.  The driver's format
descriptor at 1050388 starts with opcode `0xC0` ("format the next argument
with default options") followed by the terminator 0, so the program path is
one loop iteration whose only callee is the argument's `Display` formatter,
dispatched through `call_indirect` on the argument descriptor's second word.
The rules below expose that dispatch and the loop exit as exact segments. -/

theorem fmtWrite_index : «module».funcs[211]? = some func211Def := by rfl

private theorem twp_ne
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
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.ne hresult)

private theorem twp_gtS
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs.toInt32 > rhs.toInt32 then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .gtS :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.gtS hresult)

/- The interpreter's sign-extension helper is private, so this rule is
specialised to the only byte our format bytecode feeds it. -/
private theorem twp_extend8S_192
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 4294967232 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 192 :: values⟩,
        .extend8S :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.extend8S)

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

/-! ### Exact block skeleton of `func211` -/

def fmtWriteParams
    (out vtablePtr formatPtr argumentsPtr : UInt32) : List Value :=
  [.i32 out, .i32 vtablePtr, .i32 formatPtr, .i32 argumentsPtr]

def fmtWriteOuterBody : Program :=
  match func211.drop 6 with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteEpilogue : Program := func211.drop 7

def fmtWriteDispatchBody : Program :=
  match fmtWriteOuterBody with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteLoopSetup : Program := fmtWriteOuterBody.drop 1

def fmtWriteEmptyBody : Program :=
  match fmtWriteDispatchBody with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteStrPath : Program := fmtWriteDispatchBody.drop 1

def fmtWriteLoopBody : Program :=
  match fmtWriteLoopSetup.drop 5 with
  | .loop _ _ body :: _ => body
  | _ => []

def fmtWriteAfterLoop : Program := fmtWriteLoopSetup.drop 6

def fmtWriteX1Body : Program :=
  match fmtWriteLoopBody.drop 4 with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteLoopCheck : Program := fmtWriteLoopBody.drop 5

def fmtWriteX2Body : Program :=
  match fmtWriteX1Body with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteFlagsPath : Program := fmtWriteX1Body.drop 1

def fmtWriteX3Body : Program :=
  match fmtWriteX2Body with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteIncrement : Program := fmtWriteX2Body.drop 1

def fmtWriteX4Body : Program :=
  match fmtWriteX3Body with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteAfterX4 : Program := fmtWriteX3Body.drop 1

def fmtWriteX5Body : Program :=
  match fmtWriteX4Body with
  | .block _ _ body :: _ => body
  | _ => []

def fmtWriteAfterX5 : Program := fmtWriteX4Body.drop 1

/-- The exact code of `func211` from the argument-formatter dispatch. -/
def fmtWriteAtDisplay : Program := fmtWriteX5Body.drop 37

def fmtWriteOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fmtWriteOuterBody
    continuation := fmtWriteEpilogue
    belowStack := [] }

def fmtWriteLoopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := fmtWriteLoopBody
    continuation := fmtWriteAfterLoop
    belowStack := [] }

def fmtWriteX1Frame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fmtWriteX1Body
    continuation := fmtWriteLoopCheck
    belowStack := [] }

def fmtWriteX2Frame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fmtWriteX2Body
    continuation := fmtWriteFlagsPath
    belowStack := [] }

def fmtWriteX3Frame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fmtWriteX3Body
    continuation := fmtWriteIncrement
    belowStack := [] }

def fmtWriteX4Frame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fmtWriteX4Body
    continuation := fmtWriteAfterX4
    belowStack := [] }

def fmtWriteX5Frame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := fmtWriteX5Body
    continuation := fmtWriteAfterX5
    belowStack := [] }

def fmtWriteControlsAtDisplay : List ControlFrame :=
  [fmtWriteX5Frame, fmtWriteX4Frame, fmtWriteX3Frame, fmtWriteX2Frame,
   fmtWriteX1Frame, fmtWriteLoopFrame, fmtWriteOuterFrame]

def fmtWriteLocalsAtDisplay
    (frame argEntry slot next : UInt32) : List Value :=
  [.i32 frame, .i32 argEntry, .i32 slot, .i32 0, .i32 next, .i32 192,
   .i32 0, .i32 0]

theorem fmtWriteAtDisplay_eq :
    fmtWriteAtDisplay = .callIndirect 2 0 :: fmtWriteX5Body.drop 38 := by
  rfl

/-- Exact segment of `func211` from its entry to the `Display`-formatter
dispatch, for an aligned (`&1 = 0`) argument descriptor and the one-argument
default-options bytecode `0xC0`: the generated interpreter builds the
`Formatter` record in its shadow frame and stops with the three operands of
the type-2 `call_indirect` on the stack.  The formatter dispatch remains an
explicit boundary. -/
theorem fmtWrite_to_display_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (out vtablePtr formatPtr argumentsPtr stackTop : UInt32)
    (writeStrSlot valuePtr displayFn old0 old4 : UInt32) (old8 : UInt64)
    (hargsEven : argumentsPtr &&& 1 = 0)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hvtableRoom : vtablePtr.toNat + 16 ≤ UInt32.size)
    (hargsRoom : argumentsPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        formatPtr (DFrac.own 1) (some (192 : UInt8)) ∗
      pointsTo_u32 (vtablePtr + 12) writeStrSlot ∗
      pointsTo_u32 argumentsPtr valuePtr ∗
      pointsTo_u32 (argumentsPtr + 4) displayFn ∗
      pointsTo_u32 (stackTop - 16) old0 ∗
      pointsTo_u32 ((stackTop - 16) + 4) old4 ∗
      pointsTo_u64 ((stackTop - 16) + 8) old8 ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          formatPtr (DFrac.own 1) (some (192 : UInt8)) -∗
        pointsTo_u32 (vtablePtr + 12) writeStrSlot -∗
        pointsTo_u32 argumentsPtr valuePtr -∗
        pointsTo_u32 (argumentsPtr + 4) displayFn -∗
        pointsTo_u32 (stackTop - 16) out -∗
        pointsTo_u32 ((stackTop - 16) + 4) vtablePtr -∗
        pointsTo_u64 ((stackTop - 16) + 8) 1610612768 -∗
        WP (.running
          ⟨⟨fmtWriteParams out vtablePtr formatPtr argumentsPtr,
              fmtWriteLocalsAtDisplay (stackTop - 16) argumentsPtr
                writeStrSlot (formatPtr + 1),
              [.i32 displayFn, .i32 (stackTop - 16), .i32 valuePtr]⟩,
            fmtWriteAtDisplay, 1, [], fmtWriteControlsAtDisplay, calls⟩ :
            Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fmtWriteParams out vtablePtr formatPtr argumentsPtr,
          List.replicate 8 (.i32 0), []⟩,
        func211, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have hload8 : (formatPtr + (0 : UInt32)).toNat =
      formatPtr.toNat + (0 : UInt32).toNat := by
    rw [show formatPtr + (0 : UInt32) = formatPtr by bv_decide]
    simp
  obtain ⟨hv120, hv121, hv122, hv123⟩ :=
    descriptorSlot32Facts vtablePtr 12 16 hvtableRoom (by decide)
  obtain ⟨ha00, ha01, ha02, ha03⟩ :=
    descriptorSlot32Facts argumentsPtr 0 8 hargsRoom (by decide)
  obtain ⟨ha40, ha41, ha42, ha43⟩ :=
    descriptorSlot32Facts argumentsPtr 4 8 hargsRoom (by decide)
  obtain ⟨hf00, hf01, hf02, hf03⟩ :=
    descriptorSlot32Facts (stackTop - 16) 0 16 hframeRoom (by decide)
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts (stackTop - 16) 4 16 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83, hf84, hf85, hf86, hf87⟩ :=
    descriptorSlot64Facts (stackTop - 16) 8 16 hframeRoom (by decide)
  iintro ⟨Hglobal, Hformat, Hvtable, Hvalue, Hfn, H0, H4, H8, Hdone⟩
  simp only [func211, fmtWriteParams, List.replicate_succ,
    List.replicate_zero]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [hargsEven]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  ihave HformatAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (formatPtr + 0) (DFrac.own 1) (some (192 : UInt8)) $$ [Hformat]
  · iapply pointsTo_byte_at_eq (show formatPtr = formatPtr + 0 by bv_decide)
    iexact Hformat
  iapply twp_load8U_owned 192 hload8 $$ HformatAt
  iintro HformatAt
  rw [show (192 : UInt8).toUInt32 = (192 : UInt32) by decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 writeStrSlot hv120 hv121 hv122 hv123 $$ Hvtable
  iintro Hvtable
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_loop
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 1 formatPtr]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_extend8S_192
  iapply twp_const
  iapply twp_gtS (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (192 : UInt32) &&& 255 = 192 by decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_eq (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ne (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old4 hf40 hf41 hf42 hf43 $$ H4
  iintro H4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave H0At : pointsTo_u32 ((stackTop - 16) + 0) old0 $$ [H0]
  · iapply pointsTo_u32_at_eq
      (show stackTop - 16 = (stackTop - 16) + 0 by bv_decide)
    iexact H0
  iapply twp_store32 old0 hf00 hf01 hf02 hf03 $$ H0At
  iintro H0At
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply twp_store64 old8 hf80 hf81 hf82 hf83 hf84 hf85 hf86 hf87 $$ H8
  iintro H8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  rw [show ((0 : UInt32) <<< ((3 : UInt32) % 32)) + argumentsPtr =
      argumentsPtr by bv_decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  ihave HvalueAt : pointsTo_u32 (argumentsPtr + 0) valuePtr $$ [Hvalue]
  · iapply pointsTo_u32_at_eq
      (show argumentsPtr = argumentsPtr + 0 by bv_decide)
    iexact Hvalue
  iapply twp_load32 valuePtr ha00 ha01 ha02 ha03 $$ HvalueAt
  iintro HvalueAt
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 displayFn ha40 ha41 ha42 ha43 $$ Hfn
  iintro Hfn
  ihave Hformat : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      formatPtr (DFrac.own 1) (some (192 : UInt8)) $$ [HformatAt]
  · iapply pointsTo_byte_at_eq (show formatPtr + 0 = formatPtr by bv_decide)
    iexact HformatAt
  ihave Hvalue : pointsTo_u32 argumentsPtr valuePtr $$ [HvalueAt]
  · iapply pointsTo_u32_at_eq
      (show argumentsPtr + 0 = argumentsPtr by bv_decide)
    iexact HvalueAt
  ihave H0 : pointsTo_u32 (stackTop - 16) out $$ [H0At]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 16) + 0 = stackTop - 16 by bv_decide)
    iexact H0At
  isimp only [fmtWriteParams, fmtWriteLocalsAtDisplay, fmtWriteAtDisplay,
    fmtWriteControlsAtDisplay, fmtWriteX5Frame, fmtWriteX5Body,
    fmtWriteAfterX5, fmtWriteX4Frame, fmtWriteX4Body, fmtWriteAfterX4,
    fmtWriteX3Frame, fmtWriteX3Body, fmtWriteIncrement, fmtWriteX2Frame,
    fmtWriteX2Body, fmtWriteFlagsPath, fmtWriteX1Frame, fmtWriteX1Body,
    fmtWriteLoopCheck, fmtWriteLoopFrame, fmtWriteLoopBody,
    fmtWriteAfterLoop, fmtWriteOuterFrame, fmtWriteOuterBody,
    fmtWriteEpilogue, fmtWriteLoopSetup, func211, List.drop] at Hdone
  iapply Hdone $$ Hglobal Hformat Hvtable Hvalue Hfn H0 H4 H8

def fmtWriteFinalParams
    (out vtablePtr formatPtr argumentsPtr : UInt32) : List Value :=
  [.i32 out, .i32 vtablePtr, .i32 (formatPtr + 1), .i32 argumentsPtr]

def fmtWriteFinalLocals (frame slot next : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 slot, .i32 1, .i32 next, .i32 192,
   .i32 0, .i32 0]

/-- Exact segment of `func211` from the instant the `Display` formatter has
returned 0: the interpreter advances to the terminator byte 0, leaves the
loop, restores the shadow stack, and falls off the end of the body with
result 0. -/
theorem fmtWrite_display_return_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (out vtablePtr formatPtr argumentsPtr stackTop slot : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 (stackTop - 16)) ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (formatPtr + 1) (DFrac.own 1) (some (0 : UInt8)) ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (formatPtr + 1) (DFrac.own 1) (some (0 : UInt8)) -∗
        WP (.running
          ⟨⟨fmtWriteFinalParams out vtablePtr formatPtr argumentsPtr,
              fmtWriteFinalLocals (stackTop - 16) slot (formatPtr + 1),
              [.i32 0]⟩,
            [], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fmtWriteParams out vtablePtr formatPtr argumentsPtr,
          fmtWriteLocalsAtDisplay (stackTop - 16) argumentsPtr slot
            (formatPtr + 1),
          [.i32 0]⟩,
        fmtWriteX5Body.drop 38, 1, [], fmtWriteControlsAtDisplay,
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have hload8 : ((formatPtr + 1) + (0 : UInt32)).toNat =
      (formatPtr + 1).toNat + (0 : UInt32).toNat := by
    rw [show (formatPtr + 1) + (0 : UInt32) = formatPtr + 1 by bv_decide]
    simp
  iintro ⟨Hglobal, Hterminator, Hdone⟩
  simp only [fmtWriteParams, fmtWriteLocalsAtDisplay,
    fmtWriteControlsAtDisplay, fmtWriteX5Frame, fmtWriteX5Body,
    fmtWriteAfterX5, fmtWriteX4Frame, fmtWriteX4Body, fmtWriteAfterX4,
    fmtWriteX3Frame, fmtWriteX3Body, fmtWriteIncrement, fmtWriteX2Frame,
    fmtWriteX2Body, fmtWriteFlagsPath, fmtWriteX1Frame, fmtWriteX1Body,
    fmtWriteLoopCheck, fmtWriteLoopFrame, fmtWriteLoopBody,
    fmtWriteAfterLoop, fmtWriteOuterFrame, fmtWriteOuterBody,
    fmtWriteEpilogue, fmtWriteLoopSetup, func211, List.drop]
  iapply twp_eqz (value := 0) (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (1 : UInt32) + 0 = 1 by decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  ihave HterminatorAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      ((formatPtr + 1) + 0) (DFrac.own 1) (some (0 : UInt8)) $$
      [Hterminator]
  · iapply pointsTo_byte_at_eq
      (show formatPtr + 1 = (formatPtr + 1) + 0 by bv_decide)
    iexact Hterminator
  iapply twp_load8U_owned 0 hload8 $$ HterminatorAt
  iintro HterminatorAt
  ihave Hterminator : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (formatPtr + 1) (DFrac.own 1) (some (0 : UInt8)) $$ [HterminatorAt]
  · iapply pointsTo_byte_at_eq
      (show (formatPtr + 1) + 0 = formatPtr + 1 by bv_decide)
    iexact HterminatorAt
  rw [show (0 : UInt8).toUInt32 = (0 : UInt32) by decide]
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_brIfZero
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 16 (stackTop - 16),
    show (stackTop - 16) + 16 = stackTop by bv_decide]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  isimp only [fmtWriteFinalParams, fmtWriteFinalLocals] at Hdone
  iapply Hdone $$ Hglobal Hterminator

/-- Total owned-byte counterpart of `i32.load16_u`, assembled from two
adjacent exclusively-owned bytes.  The total lifting library has no 16-bit
rules yet; this local rule mirrors `twp_load8U_owned`. -/
theorem twp_load16U_owned
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (b0 b1 : UInt8)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load16U offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 (b0.toUInt32 ||| (b1.toUInt32 <<< 8)) :: values⟩,
        code, arity, remainder, controls, calls⟩
    (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some b0) ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((address + offset) + 1) (DFrac.own 1) (some b1)) -∗
    (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some b0) ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((address + offset) + 1) (DFrac.own 1) (some b1) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro ⟨Hb0, Hb1⟩ Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hstate
  ihave %Hfacts0 : ⌜store.wasm.mem.read8 (address + offset) = b0 ∧
      (address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$
      [Hstate Hb0]
  · imod stateInterp_pointsTo_facts store ns obs nt
      (address + offset) b0 $$ [$Hstate $Hb0] with %Hfacts
    ipureintro
    exact Hfacts
  ihave %Hfacts1 : ⌜store.wasm.mem.read8 ((address + offset) + 1) = b1 ∧
      ((address + offset) + 1).toNat < store.wasm.mem.pages * 65536⌝ $$
      [Hstate Hb1]
  · imod stateInterp_pointsTo_facts store ns obs nt
      ((address + offset) + 1) b1 $$ [$Hstate $Hb1] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 2 ≤
      store.wasm.mem.pages * 65536 := by
    have := Hfacts1.2
    rw [h1, hnowrap] at this
    omega
  have hread : store.wasm.mem.read16 (address + offset) =
      b0.toUInt32 ||| (b1.toUInt32 <<< 8) := by
    have e0 : store.wasm.mem.bytes (address + offset).toNat = b0 := by
      simpa [Mem.read8] using Hfacts0.1
    have e1 : store.wasm.mem.bytes ((address + offset).toNat + 1) = b1 := by
      have := Hfacts1.1
      simp only [Mem.read8, h1] at this
      exact this
    have hread16 : store.wasm.mem.read16 (address + offset) =
        (store.wasm.mem.bytes (address + offset).toNat).toUInt32 |||
          ((store.wasm.mem.bytes
            ((address + offset).toNat + 1)).toUInt32 <<< 8) := rfl
    rw [hread16, e0, e1]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues,
            .i32 (b0.toUInt32 ||| (b1.toUInt32 <<< 8)) :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.load16U offset), rfl,
        by simpa [hread] using
          (Step.load16U (α := α) (address := address) hbound)⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, _kind, _hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load16U offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load16U offset))
      ⟨.running ⟨⟨params, localValues,
          .i32 (b0.toUInt32 ||| (b1.toUInt32 <<< 8)) :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [hread] using
      (Step.load16U (α := α) (address := address) hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hstate]
  · iexact Hstate
  · iapply Htwp
    isplitl [Hb0]
    · iexact Hb0
    · iexact Hb1

/-! ## `Formatter::pad_integral` helpers (`func226`, absolute call 228)

With the driver's default format options the sign/prefix writer receives the
"no character" sentinel 1114112 and an empty prefix, so it returns 0 without
touching the writer. -/

theorem padPrefix_index : «module».funcs[226]? = some func226Def := by rfl

/-- Exact total body rule for generated local `func226` when no sign
character (sentinel 1114112) and no prefix (`prefixFlag = 0`) are
requested: it returns 0 with no effects. -/
theorem padPrefix_none_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (writerPtr vtablePtr prefixPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 writerPtr, .i32 vtablePtr, .i32 1114112, .i32 0,
          .i32 prefixPtr], [], [.i32 0]⟩,
        [.ret], 1, [],
        [{ kind := .block
           paramArity := 0
           resultArity := 0
           body :=
             match func226.drop 1 with
             | .block _ _ body :: _ => body
             | _ => []
           continuation := func226.drop 2
           belowStack := [] }], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 writerPtr, .i32 vtablePtr, .i32 1114112, .i32 0,
          .i32 prefixPtr], [], []⟩,
        func226, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hdone
  simp only [func226, List.drop]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_eq (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_brIfZero
  iapply twp_const
  iexact Hdone

/-- Composable total call rule for `func226` at absolute Wasm index `228`,
along the no-sign/no-prefix path. -/
theorem padPrefix_none_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (writerPtr vtablePtr prefixPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨{ callerLocals with values := [.i32 0] ++ stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 prefixPtr, .i32 0, .i32 1114112, .i32 vtablePtr,
           .i32 writerPtr] ++ stack },
        .call 228 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 228 func226Def
      (by decide) padPrefix_index $$ Hruntime
  iintro Hruntime
  simp [func226Def, Function.toLocals, Function.numParams]
  have Hbody := padPrefix_none_body_twp (α := α)
    writerPtr vtablePtr prefixPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append, List.cons_append]
  iapply Hdone $$ Hruntime

/-! ## `Formatter::pad_integral` (`func224`, absolute call 226)

With the default options word 0x60000020 (no sign, no `#` prefix, no width)
the function reduces to: write nothing via `func226`, then forward the digit
buffer to the vtable's `write_str` slot.  The `write_str` dispatch remains an
explicit boundary shared with `writeStrAdapter_callIndirect_twp`. -/

theorem padIntegral_index : «module».funcs[224]? = some func224Def := by rfl

private theorem twp_geU
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≥ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .geU :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.geU hresult)

def padIntegralPrefixBody : Program :=
  match func224.drop 21 with
  | .block _ _ body :: _ => body
  | _ => []

def padIntegralAfterPrefix : Program := func224.drop 22

def padIntegralPrefixSkip : Program :=
  match padIntegralPrefixBody with
  | .block _ _ body :: _ => body
  | _ => []

def padIntegralPrefixCount : Program := padIntegralPrefixBody.drop 1

def padIntegralOuterBody : Program :=
  match padIntegralAfterPrefix.drop 5 with
  | .block _ _ body :: _ => body
  | _ => []

def padIntegralReturn : Program := padIntegralAfterPrefix.drop 6

def padIntegralWidthBody : Program :=
  match padIntegralOuterBody with
  | .block _ _ body :: _ => body
  | _ => []

def padIntegralShortPath : Program := padIntegralOuterBody.drop 1

/-- The exact code of `func224` from the `write_str` vtable dispatch. -/
def padIntegralAtWriteStr : Program := padIntegralShortPath.drop 20

def padIntegralOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := padIntegralOuterBody
    continuation := padIntegralReturn
    belowStack := [] }

def padIntegralFinalParams
    (f prefix3 buf len : UInt32) : List Value :=
  [.i32 f, .i32 0, .i32 0, .i32 prefix3, .i32 buf, .i32 len]

def padIntegralLocalsAtWriteStr
    (outWriter vtablePtr len : UInt32) : List Value :=
  [.i32 1610612768, .i32 outWriter, .i32 1114112, .i32 len,
   .i32 vtablePtr, .i32 0, .i32 1114112, .i32 1, .i64 0]

theorem padIntegralAtWriteStr_eq :
    padIntegralAtWriteStr = [.callIndirect 3 0, .localSet 13] := by
  rfl

/-- Exact segment of `func224` from its entry to the `write_str` vtable
dispatch, under the driver's default options word 0x60000020 (stored at
`f+8`; its width half at `f+12` is zero) and `is_nonneg = 1`: no sign and no
prefix are written (`func226` returns 0 without effects), and the segment
stops with the digit-buffer `write_str` operands and table selector on the
stack. -/
theorem padIntegral_to_writeStr_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (f prefix2 prefix3 buf len outWriter vtablePtr writeStrSlot : UInt32)
    (hfRoom : f.toNat + 16 ≤ UInt32.size)
    (hvtableRoom : vtablePtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 (f + 8) 1610612768 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (f + 12) (DFrac.own 1) (some (0 : UInt8)) ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (f + 13) (DFrac.own 1) (some (0 : UInt8)) ∗
      pointsTo_u32 f outWriter ∗
      pointsTo_u32 (f + 4) vtablePtr ∗
      pointsTo_u32 (vtablePtr + 12) writeStrSlot ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 (f + 8) 1610612768 -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (f + 12) (DFrac.own 1) (some (0 : UInt8)) -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (f + 13) (DFrac.own 1) (some (0 : UInt8)) -∗
        pointsTo_u32 f outWriter -∗
        pointsTo_u32 (f + 4) vtablePtr -∗
        pointsTo_u32 (vtablePtr + 12) writeStrSlot -∗
        WP (.running
          ⟨⟨padIntegralFinalParams f prefix3 buf len,
              padIntegralLocalsAtWriteStr outWriter vtablePtr len,
              [.i32 writeStrSlot, .i32 len, .i32 buf, .i32 outWriter]⟩,
            padIntegralAtWriteStr, 1, [], [padIntegralOuterFrame],
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 f, .i32 1, .i32 prefix2, .i32 prefix3, .i32 buf, .i32 len],
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
           .i32 0, .i64 0], []⟩,
        func224, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h00, h01, h02, h03⟩ :=
    descriptorSlot32Facts f 0 16 hfRoom (by decide)
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts f 4 16 hfRoom (by decide)
  obtain ⟨h80, h81, h82, h83⟩ :=
    descriptorSlot32Facts f 8 16 hfRoom (by decide)
  obtain ⟨h120, h121, h122, h123⟩ :=
    descriptorSlot32Facts f 12 16 hfRoom (by decide)
  obtain ⟨hv120, hv121, hv122, hv123⟩ :=
    descriptorSlot32Facts vtablePtr 12 16 hvtableRoom (by decide)
  iintro ⟨Hruntime, Hoptions, Hw0, Hw1, Hout, Hvtable, Hslot, Hdone⟩
  simp only [func224]
  iapply twp_const
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_load32 1610612768 h80 h81 h82 h83 $$ Hoptions
  iintro Hoptions
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (1610612768 : UInt32) &&& 2097152 = 0 by decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 1114112) (by decide)
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shrU
  rw [show (0 : UInt32) >>> ((21 : UInt32) % 32) = 0 by decide]
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 0) (by decide)
  iapply twp_localGet rfl
  iapply twp_add
  rw [show len + (0 : UInt32) = len by bv_decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (1610612768 : UInt32) &&& 8388608 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := 1114112) (by decide)
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hw0At : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (f + 12) (DFrac.own 1) (some (0 : UInt8)) $$ [Hw0]
  · iexact Hw0
  ihave Hw1At : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      ((f + 12) + 1) (DFrac.own 1) (some (0 : UInt8)) $$ [Hw1]
  · iapply pointsTo_byte_at_eq (show f + 13 = (f + 12) + 1 by bv_decide)
    iexact Hw1
  iapply twp_load16U_owned 0 0 h120 h121 $$ [Hw0At Hw1At]
  · iframe
  iintro ⟨Hw0, Hw1⟩
  rw [show (0 : UInt8).toUInt32 ||| ((0 : UInt8).toUInt32 <<< 8) =
      (0 : UInt32) by decide]
  iapply twp_localSet rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_geU (result := 1)
    (by rw [if_pos (show len ≥ 0 from UInt32.zero_le)])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  ihave HoutAt : pointsTo_u32 (f + 0) outWriter $$ [Hout]
  · iapply pointsTo_u32_at_eq (show f = f + 0 by bv_decide)
    iexact Hout
  iapply twp_load32 outWriter h00 h01 h02 h03 $$ HoutAt
  iintro HoutAt
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 vtablePtr h40 h41 h42 h43 $$ Hvtable
  iintro Hvtable
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  have Hprefix := padPrefix_none_call_twp (α := α)
    outWriter vtablePtr prefix3
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 f, .i32 0, .i32 0, .i32 prefix3, .i32 buf, .i32 len],
        [.i32 1610612768, .i32 outWriter, .i32 1114112, .i32 len,
         .i32 vtablePtr, .i32 0, .i32 1114112, .i32 1, .i64 0], []⟩)
    (stack := [])
    (code := padIntegralShortPath.drop 14)
    (arity := 1) (remainder := [])
    (controls := [padIntegralOuterFrame])
    (calls := calls)
  simp only [List.append_nil,
    padIntegralShortPath, padIntegralOuterFrame, padIntegralOuterBody,
    padIntegralReturn, padIntegralAfterPrefix,
    func224, List.drop] at Hprefix
  iapply Hprefix
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 writeStrSlot hv120 hv121 hv122 hv123 $$ Hslot
  iintro Hslot
  ihave Hout : pointsTo_u32 f outWriter $$ [HoutAt]
  · iapply pointsTo_u32_at_eq (show f + 0 = f by bv_decide)
    iexact HoutAt
  ihave Hw1' : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (f + 13) (DFrac.own 1) (some (0 : UInt8)) $$ [Hw1]
  · iapply pointsTo_byte_at_eq (show (f + 12) + 1 = f + 13 by bv_decide)
    iexact Hw1
  isimp only [padIntegralFinalParams, padIntegralLocalsAtWriteStr,
    padIntegralAtWriteStr, padIntegralShortPath, padIntegralOuterFrame,
    padIntegralOuterBody, padIntegralReturn, padIntegralWidthBody,
    padIntegralAfterPrefix, func224, List.drop] at Hdone
  iapply Hdone $$ Hruntime Hoptions Hw0 Hw1' Hout Hvtable Hslot

/-- Exact tail of `func224` after `write_str` has returned: the result is
recorded and returned unchanged. -/
theorem padIntegral_writeStr_return_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (f prefix3 buf len outWriter vtablePtr result : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨padIntegralFinalParams f prefix3 buf len,
          (padIntegralLocalsAtWriteStr outWriter vtablePtr len).set 7
            (.i32 result), [.i32 result]⟩,
        [], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨padIntegralFinalParams f prefix3 buf len,
          padIntegralLocalsAtWriteStr outWriter vtablePtr len,
          [.i32 result]⟩,
        [.localSet 13], 1, [], [padIntegralOuterFrame], calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  iintro Hdone
  simp only [padIntegralFinalParams, padIntegralLocalsAtWriteStr,
    padIntegralOuterFrame, padIntegralOuterBody, padIntegralReturn,
    padIntegralAfterPrefix, func224, List.drop, List.set]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iexact Hdone

end Project.Mergesort.WriteFmtProof
