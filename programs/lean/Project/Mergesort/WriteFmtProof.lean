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

end Project.Mergesort.WriteFmtProof
