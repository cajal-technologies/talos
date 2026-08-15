import Project.Mergesort.FormatProof
import Project.Mergesort.MemoryFillProof
import Project.Mergesort.VectorProof

/-!
# Generated input-iterator constructors

An exact entry decomposition for the unchanged `String::split` (`func82`),
plus total body and call rules for `Iterator::map` (`func90`).  The split
decomposition exposes its generated UTF-8 constructor (`func83`) as the next
proof boundary instead of hiding that non-leaf call.
-/

namespace Project.Mergesort.InputIteratorProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.SplitAtProof
open Project.Mergesort.FormatProof
open Project.Mergesort.MemoryFillProof
open Project.Mergesort.VectorProof

/-- The generated split/map iterator is represented by five consecutive
64-bit words.  Keeping the padding-containing words abstract makes this
layout usable across the generated constructor boundary. -/
def inputIteratorAt [WasmHeapGS] (base : UInt32)
    (word0 word1 word2 word3 word4 : UInt64) : IProp WasmHeapGF :=
  iprop% pointsTo_u64 base word0 ∗
    pointsTo_u64 (base + 8) word1 ∗
    pointsTo_u64 (base + 16) word2 ∗
    pointsTo_u64 (base + 24) word3 ∗
    pointsTo_u64 (base + 32) word4

private def mapParams (resultPtr sourcePtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 sourcePtr]

private theorem pointsTo_u64_add_zero [WasmHeapGS]
    (base : UInt32) (value : UInt64) :
    pointsTo_u64 base value ⊢ pointsTo_u64 (base + 0) value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u64_remove_zero [WasmHeapGS]
    (base : UInt32) (value : UInt64) :
    pointsTo_u64 (base + 0) value ⊢ pointsTo_u64 base value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u32_add_zero' [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 base value ⊢ pointsTo_u32 (base + 0) value := by
  rw [UInt32.add_zero]

private theorem pointsTo_u32_remove_zero' [WasmHeapGS]
    (base value : UInt32) :
    pointsTo_u32 (base + 0) value ⊢ pointsTo_u32 base value := by
  rw [UInt32.add_zero]

private theorem pointsToByte_remove_zero [WasmHeapGS]
    (base : UInt32) (byte : UInt8) :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (base + 0) (DFrac.own 1) (some byte) ⊢
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        base (DFrac.own 1) (some byte) := by
  rw [UInt32.add_zero]

private theorem pointsToByte_add_zero [WasmHeapGS]
    (base : UInt32) (byte : UInt8) :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        base (DFrac.own 1) (some byte) ⊢
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (base + 0) (DFrac.own 1) (some byte) := by
  rw [UInt32.add_zero]

private theorem globalPointsTo_i32_congr [WasmSmallStepGS hlc]
    (index : Nat) (lhs rhs : UInt32) (h : lhs = rhs) :
    globalPointsTo index (.i32 lhs) ⊢ globalPointsTo index (.i32 rhs) := by
  rw [h]

private theorem pointsTo_u32_congr [WasmHeapGS]
    (lhs rhs lhsValue rhsValue : UInt32)
    (haddr : lhs = rhs) (hvalue : lhsValue = rhsValue) :
    pointsTo_u32 lhs lhsValue ⊢ pointsTo_u32 rhs rhsValue := by
  rw [haddr, hvalue]

private theorem pointsTo_u64_congr [WasmHeapGS]
    (lhs rhs : UInt32) (lhsValue rhsValue : UInt64)
    (haddr : lhs = rhs) (hvalue : lhsValue = rhsValue) :
    pointsTo_u64 lhs lhsValue ⊢ pointsTo_u64 rhs rhsValue := by
  rw [haddr, hvalue]

private theorem pointsToByte_congr [WasmHeapGS]
    (lhs rhs : UInt32) (lhsByte rhsByte : UInt8)
    (haddr : lhs = rhs) (hbyte : lhsByte = rhsByte) :
    (lhs ↦w lhsByte) ⊢ (rhs ↦w rhsByte) := by
  rw [haddr, hbyte]

private theorem twp_dropValue
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value} {value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    WP (.running ⟨⟨params, localValues, values⟩,
      code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, localValues, value :: values⟩,
      .drop :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.drop)

/-- Exact ASCII-space path through generated local `func88`. -/
theorem utf8EncodeSpace_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (destination stackTop oldFrame12 : UInt32) (oldByte : UInt8)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (_hdestinationRoom : destination.toNat + 1 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (destination + 0) (DFrac.own 1) (some oldByte) ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 12) 1 -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          destination (DFrac.own 1) (some (32 : UInt8)) -∗
        WP (.running
          ⟨⟨[.i32 32, .i32 destination],
              [.i32 (stackTop - 16), .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 32, .i32 destination],
          [.i32 0, .i32 0, .i32 0, .i32 0,
            .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func88, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 16 hframeRoom (by decide)
  have hdest : (destination + 0).toNat = destination.toNat + (0 : UInt32).toNat := by
    simp
  iintro ⟨Hglobal, Hframe12, Hbyte, Hdone⟩
  simp only [func88]
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
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := 1) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) rfl
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame12 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store8_owned oldByte hdest $$ Hbyte
  iintro Hbyte
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_exitControl rfl
  simp only [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set, List.take_zero, List.nil_append]
  ihave HbyteBaseRaw : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      destination (DFrac.own 1) (some ((32 : UInt32).toUInt8)) $$ [Hbyte]
  · iapply pointsToByte_remove_zero
    iexact Hbyte
  ihave HbyteBase : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      destination (DFrac.own 1) (some (32 : UInt8)) $$ [HbyteBaseRaw]
  · rw [show (32 : UInt32).toUInt8 = (32 : UInt8) by decide]
    iexact HbyteBaseRaw
  iapply Hdone $$ Hglobal Hframe12 HbyteBase

/-- Composable absolute-index-90 rule for the space path of `func88`. -/
theorem utf8EncodeSpace_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (destination stackTop oldFrame12 : UInt32) (oldByte : UInt8)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hdestinationRoom : destination.toNat + 1 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (destination + 0) (DFrac.own 1) (some oldByte) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 12) 1 -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          destination (DFrac.own 1) (some (32 : UInt8)) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 destination, .i32 32] ++ stack },
        .call 90 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe12, Hbyte, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 90 func88Def
      (by decide) utf8Encode_index $$ Hruntime
  iintro Hruntime
  simp [func88Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := utf8EncodeSpace_body_twp (α := α)
    destination stackTop oldFrame12 oldByte hframeRoom hdestinationRoom
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
  isplitl [Hframe12]
  · iexact Hframe12
  ihave HbyteAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (destination + 0) (DFrac.own 1) (some oldByte) $$ [Hbyte]
  · iapply pointsToByte_add_zero
    iexact Hbyte
  isplitl [HbyteAt]
  · iexact HbyteAt
  iintro Hglobal Hframe12 Hbyte
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hframe12 Hbyte

private def utf8CapacityParams (resultPtr destination : UInt32) : List Value :=
  [.i32 resultPtr, .i32 32, .i32 destination, .i32 4]

/-- Exact successful space/capacity-four path through local `func45`. -/
theorem utf8CapacitySpace_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr destination stackTop : UInt32)
    (oldFrame12 oldEncodeFrame12 oldResult0 oldResult4 : UInt32)
    (oldByte : UInt8)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hencodeFrameRoom : ((stackTop - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    (hdestinationRoom : destination.toNat + 1 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 (((stackTop - 16) - 16) + 12) oldEncodeFrame12 ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        destination (DFrac.own 1) (some oldByte) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 12) 1 -∗
        pointsTo_u32 (((stackTop - 16) - 16) + 12) 1 -∗
        pointsTo_u32 resultPtr destination -∗
        pointsTo_u32 (resultPtr + 4) 1 -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          destination (DFrac.own 1) (some (32 : UInt8)) -∗
        WP (.running
          ⟨⟨utf8CapacityParams resultPtr destination,
              [.i32 (stackTop - 16)], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨utf8CapacityParams resultPtr destination, [.i32 0], []⟩,
        func45, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  let encodeFrame := frame - 16
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 16 hframeRoom (by decide)
  obtain ⟨hr00, hr01, hr02, hr03⟩ :=
    descriptorSlot32Facts resultPtr 0 8 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 8 hresultRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hframe12, HencodeFrame12,
    Hresult0, Hresult4, Hbyte, Hdone⟩
  simp only [func45]
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
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := 1) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) rfl
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame12 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 1 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_ltU (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  simp only [utf8CapacityParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_call (α := α) «module» 90 func88Def
      (by decide) utf8Encode_index $$ Hruntime
  iintro Hruntime
  simp [func88Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply utf8EncodeSpace_body_twp (α := α)
    destination frame oldEncodeFrame12 oldByte
    hencodeFrameRoom hdestinationRoom
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [HencodeFrame12]
  · iexact HencodeFrame12
  ihave HbyteAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (destination + 0) (DFrac.own 1) (some oldByte) $$ [Hbyte]
  · iapply pointsToByte_add_zero
    iexact Hbyte
  isplitl [HbyteAt]
  · iexact HbyteAt
  iintro Hglobal HencodeFrame12 Hbyte
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 1 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_store32 oldResult4 hr40 hr41 hr42 hr43 $$ Hresult4
  iintro Hresult4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hresult0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hresult0]
  · iapply pointsTo_u32_add_zero'
    iexact Hresult0
  iapply twp_store32 oldResult0 hr00 hr01 hr02 hr03 $$ Hresult0At
  iintro Hresult0At
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [frame]
  ihave Hresult0Base : pointsTo_u32 resultPtr destination $$ [Hresult0At]
  · iapply pointsTo_u32_remove_zero'
    iexact Hresult0At
  ihave HglobalRestored : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · iapply globalPointsTo_i32_congr 0
      (16 + (stackTop - 16)) stackTop (by bv_decide)
    iexact Hglobal
  iapply Hdone $$ Hruntime HglobalRestored Hframe12 HencodeFrame12
    Hresult0Base Hresult4 Hbyte

/-- Composable absolute-index-47 rule for the successful space path of
generated local `func45`. -/
theorem utf8CapacitySpace_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr destination stackTop : UInt32)
    (oldFrame12 oldEncodeFrame12 oldResult0 oldResult4 : UInt32)
    (oldByte : UInt8)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hencodeFrameRoom : ((stackTop - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    (hdestinationRoom : destination.toNat + 1 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 (((stackTop - 16) - 16) + 12) oldEncodeFrame12 ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        destination (DFrac.own 1) (some oldByte) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 12) 1 -∗
        pointsTo_u32 (((stackTop - 16) - 16) + 12) 1 -∗
        pointsTo_u32 resultPtr destination -∗
        pointsTo_u32 (resultPtr + 4) 1 -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          destination (DFrac.own 1) (some (32 : UInt8)) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 4, .i32 destination, .i32 32, .i32 resultPtr] ++ stack },
        .call 47 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe12, HencodeFrame12,
    Hresult0, Hresult4, Hbyte, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 47 func45Def
      (by decide) utf8Capacity_index $$ Hruntime
  iintro Hruntime
  simp [func45Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := utf8CapacitySpace_body_twp (α := α)
    resultPtr destination stackTop oldFrame12 oldEncodeFrame12
    oldResult0 oldResult4 oldByte hframeRoom hencodeFrameRoom
    hresultRoom hdestinationRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [utf8CapacityParams] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [HencodeFrame12]
  · iexact HencodeFrame12
  ihave Hresult0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hresult0]
  · iapply pointsTo_u32_add_zero'
    iexact Hresult0
  isplitl [Hresult0At]
  · iexact Hresult0At
  isplitl [Hresult4]
  · iexact Hresult4
  isplitl [Hbyte]
  · iexact Hbyte
  iintro Hruntime Hglobal Hframe12 HencodeFrame12
    Hresult0 Hresult4 Hbyte
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hframe12 HencodeFrame12
    Hresult0 Hresult4 Hbyte

def splitConstructorAt [WasmHeapGS]
    (base data length : UInt32) (pad25 pad26 pad27 : UInt8) :
    IProp WasmHeapGF :=
  iprop% pointsTo_u32 base 32 ∗
    pointsTo_u32 (base + 4) data ∗
    pointsTo_u32 (base + 8) length ∗
    pointsTo_u32 (base + 12) 0 ∗
    pointsTo_u32 (base + 16) length ∗
    pointsTo_u32 (base + 20) 32 ∗
    ((base + 24) ↦w (1 : UInt8)) ∗
    ((base + 25) ↦w pad25) ∗
    ((base + 26) ↦w pad26) ∗
    ((base + 27) ↦w pad27)

/-- Little-endian word assembled from four independently owned bytes. -/
def packBytes4 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
    (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

private theorem pointsToBytes4_eq_u32 [WasmHeapGS]
    (base : UInt32) (b0 b1 b2 b3 : UInt8) :
    (iprop% (base ↦w b0) ∗ ((base + 1) ↦w b1) ∗
      ((base + 2) ↦w b2) ∗ ((base + 3) ↦w b3)) ⊣⊢
      pointsTo_u32 base (packBytes4 b0 b1 b2 b3) := by
  simp only [pointsTo_u32, packBytes4, u32Byte]
  rw [show
      (b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 |||
        b3.toUInt32 <<< 24).toUInt8 = b0 by bv_decide,
    show
      ((b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 |||
        b3.toUInt32 <<< 24) >>> 8).toUInt8 = b1 by bv_decide,
    show
      ((b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 |||
        b3.toUInt32 <<< 24) >>> 16).toUInt8 = b2 by bv_decide,
    show
      ((b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 |||
        b3.toUInt32 <<< 24) >>> 24).toUInt8 = b3 by bv_decide]
  exact .rfl

/-- Private memory carried by the generated space constructor and its two
UTF-8 helper frames.  The base is the caller's (`func82`) shadow frame. -/
def splitConstructorSpaceScratchAt [WasmHeapGS] (base : UInt32) :
    IProp WasmHeapGF :=
  let frame := base - 32
  iprop% pointsTo_u32 (frame + 8) (frame + 16) ∗
    pointsTo_u32 (frame + 12) 1 ∗
    pointsTo_u32 (frame + 16) 32 ∗
    ((frame + 22) ↦w (0 : UInt8)) ∗
    ((frame + 23) ↦w (1 : UInt8)) ∗
    pointsTo_u32 (frame + 24) 32 ∗
    pointsTo_u32 ((frame - 16) + 12) 1 ∗
    pointsTo_u32 (((frame - 16) - 16) + 12) 1

/- Exact absolute-index-85 rule for the generated split constructor on the
space delimiter used by the exported driver. -/
set_option maxHeartbeats 6000000 in
theorem splitConstructorSpace_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr data length stackTop : UInt32)
    (oldFrame8 oldFrame12 oldFrame16 oldFrame24 : UInt32)
    (oldFrame22 oldFrame23 : UInt8)
    (oldCapacityFrame12 oldEncodeFrame12 : UInt32)
    (oldResult0 oldResult4 oldResult8 oldResult12
      oldResult16 oldResult20 : UInt32)
    (oldResult24 oldResult25 oldResult26 oldResult27 : UInt8)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hcapacityFrameRoom : ((stackTop - 32) - 16).toNat + 16 ≤ UInt32.size)
    (hencodeFrameRoom : (((stackTop - 32) - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 28 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 32) + 12) oldFrame12 ∗
      pointsTo_u32 ((stackTop - 32) + 16) oldFrame16 ∗
      (((stackTop - 32) + 22) ↦w oldFrame22) ∗
      (((stackTop - 32) + 23) ↦w oldFrame23) ∗
      pointsTo_u32 ((stackTop - 32) + 24) oldFrame24 ∗
      pointsTo_u32 (((stackTop - 32) - 16) + 12) oldCapacityFrame12 ∗
      pointsTo_u32 ((((stackTop - 32) - 16) - 16) + 12) oldEncodeFrame12 ∗
      pointsTo_u32 (resultPtr + 0) oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo_u32 (resultPtr + 8) oldResult8 ∗
      pointsTo_u32 (resultPtr + 12) oldResult12 ∗
      pointsTo_u32 (resultPtr + 16) oldResult16 ∗
      pointsTo_u32 (resultPtr + 20) oldResult20 ∗
      ((resultPtr + 24) ↦w oldResult24) ∗
      ((resultPtr + 25) ↦w oldResult25) ∗
      ((resultPtr + 26) ↦w oldResult26) ∗
      ((resultPtr + 27) ↦w oldResult27) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 32) + 8) ((stackTop - 32) + 16) -∗
        pointsTo_u32 ((stackTop - 32) + 12) 1 -∗
        pointsTo_u32 ((stackTop - 32) + 16) 32 -∗
        (((stackTop - 32) + 22) ↦w (0 : UInt8)) -∗
        (((stackTop - 32) + 23) ↦w (1 : UInt8)) -∗
        pointsTo_u32 ((stackTop - 32) + 24) 32 -∗
        pointsTo_u32 (((stackTop - 32) - 16) + 12) 1 -∗
        pointsTo_u32 ((((stackTop - 32) - 16) - 16) + 12) 1 -∗
        splitConstructorAt resultPtr data length
          oldResult25 oldResult26 oldResult27 -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 length, .i32 data, .i32 32, .i32 resultPtr] ++ stack },
        .call 85 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let frame := stackTop - 32
  let capacityFrame := frame - 16
  let encodeFrame := capacityFrame - 16
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts frame 8 32 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts frame 12 32 hframeRoom (by decide)
  obtain ⟨hf160, hf161, hf162, hf163⟩ :=
    descriptorSlot32Facts frame 16 32 hframeRoom (by decide)
  obtain ⟨hf220, hf221, hf222, hf223⟩ :=
    descriptorSlot32Facts frame 22 32 hframeRoom (by decide)
  obtain ⟨hf230, hf231, hf232, hf233⟩ :=
    descriptorSlot32Facts frame 23 32 hframeRoom (by decide)
  obtain ⟨hf240, hf241, hf242, hf243⟩ :=
    descriptorSlot32Facts frame 24 32 hframeRoom (by decide)
  obtain ⟨hr00, hr01, hr02, hr03⟩ :=
    descriptorSlot32Facts resultPtr 0 28 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 28 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    descriptorSlot32Facts resultPtr 8 28 hresultRoom (by decide)
  obtain ⟨hr120, hr121, hr122, hr123⟩ :=
    descriptorSlot32Facts resultPtr 12 28 hresultRoom (by decide)
  obtain ⟨hr160, hr161, hr162, hr163⟩ :=
    descriptorSlot32Facts resultPtr 16 28 hresultRoom (by decide)
  obtain ⟨hr200, hr201, hr202, hr203⟩ :=
    descriptorSlot32Facts resultPtr 20 28 hresultRoom (by decide)
  have hresult20AtRoom : (20 + resultPtr).toNat + 4 ≤ UInt32.size := by
    rw [show 20 + resultPtr = resultPtr + UInt32.ofNat 20 by
          simpa using UInt32.add_comm (20 : UInt32) resultPtr,
      hr200]
    omega
  obtain ⟨hr20z0, hr20z1, hr20z2, hr20z3⟩ :=
    descriptorSlot32Facts (20 + resultPtr) 0 4 hresult20AtRoom (by decide)
  obtain ⟨hr240, hr241, hr242, hr243⟩ :=
    descriptorSlot32Facts resultPtr 24 28 hresultRoom (by decide)
  iintro ⟨Hruntime, Hglobal, Hframe8, Hframe12, Hframe16,
    Hframe22, Hframe23, Hframe24, HcapacityFrame12, HencodeFrame12,
    Hresult0, Hresult4, Hresult8, Hresult12, Hresult16, Hresult20,
    Hresult24, Hresult25, Hresult26, Hresult27, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 85 func83Def
      (by decide) splitConstructor_index $$ Hruntime
  iintro Hruntime
  simp [func83Def, Function.toLocals, Function.numParams, ValueType.zero]
  simp only [func83]
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
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame16 hf160 hf161 hf162 hf163 $$ Hframe16
  iintro Hframe16
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  isimp only [pointsTo_u32] at Hframe16
  icases Hframe16 with ⟨Hdestination, Hdestination1,
    Hdestination2, Hdestination3⟩
  isimp only [u32Byte] at Hdestination Hdestination1
    Hdestination2 Hdestination3
  rw [show (16 : UInt32) + frame = frame + 16 by bv_decide,
    show (8 : UInt32) + frame = frame + 8 by bv_decide]
  have Hcapacity := utf8CapacitySpace_call_twp (α := α)
    (frame + 8) (frame + 16) frame
    oldCapacityFrame12 oldEncodeFrame12 oldFrame8 oldFrame12
    0 hcapacityFrameRoom hencodeFrameRoom
    (by
      change (frame + UInt32.ofNat 8).toNat + 8 ≤ UInt32.size
      rw [hf80]
      dsimp [frame]
      omega)
    (by
      change (frame + UInt32.ofNat 16).toNat + 1 ≤ UInt32.size
      rw [hf160]
      dsimp [frame]
      omega)
    (callerLocals :=
      ⟨[.i32 resultPtr, .i32 32, .i32 data, .i32 length],
        [.i32 (stackTop - 32), .i32 4, .i32 0,
          .i32 0, .i32 0, .i32 0], []⟩)
    (stack := []) (code := func83.drop 20) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [func83, List.drop, List.append_nil] at Hcapacity
  ihave HcapacityFrame12At : pointsTo_u32 (frame - 16 + 12)
      oldCapacityFrame12 $$ [HcapacityFrame12]
  · iapply pointsTo_u32_congr
      ((stackTop - 32) - 16 + 12) (frame - 16 + 12)
      oldCapacityFrame12 oldCapacityFrame12 (by rfl) rfl
    iexact HcapacityFrame12
  ihave HencodeFrame12At : pointsTo_u32 (frame - 16 - 16 + 12)
      oldEncodeFrame12 $$ [HencodeFrame12]
  · iapply pointsTo_u32_congr
      (((stackTop - 32) - 16) - 16 + 12) (frame - 16 - 16 + 12)
      oldEncodeFrame12 oldEncodeFrame12 (by rfl) rfl
    iexact HencodeFrame12
  ihave Hframe8At : pointsTo_u32 (frame + 8 + 0) oldFrame8 $$ [Hframe8]
  · iapply pointsTo_u32_add_zero'
    iexact Hframe8
  ihave Hframe12At : pointsTo_u32 (frame + 8 + 4) oldFrame12 $$ [Hframe12]
  · iapply pointsTo_u32_congr (frame + 12) (frame + 8 + 4)
      oldFrame12 oldFrame12 (by bv_decide) rfl
    iexact Hframe12
  ihave HdestinationAt : ((frame + 16) ↦w (0 : UInt8)) $$ [Hdestination]
  · iapply pointsToByte_congr (frame + UInt32.ofNat 16) (frame + 16)
      ((0 : UInt32).toUInt8) 0 (by rfl) (by decide)
    iexact Hdestination
  iapply Hcapacity
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [HcapacityFrame12At]
  · iexact HcapacityFrame12At
  isplitl [HencodeFrame12At]
  · iexact HencodeFrame12At
  isplitl [Hframe8At]
  · iexact Hframe8At
  isplitl [Hframe12At]
  · iexact Hframe12At
  isplitl [HdestinationAt]
  · iexact HdestinationAt
  iintro Hruntime Hglobal HcapacityFrame12 HencodeFrame12
    Hframe8 Hframe12 Hdestination
  ihave Hdestination1Z : ((frame + 16 + 1) ↦w (0 : UInt8)) $$
      [Hdestination1]
  · iapply pointsToByte_congr (frame + UInt32.ofNat 16 + 1)
      (frame + 16 + 1) ((0 : UInt32) >>> 8).toUInt8 0
      (by rfl) (by decide)
    iexact Hdestination1
  ihave Hdestination2Z : ((frame + 16 + 2) ↦w (0 : UInt8)) $$
      [Hdestination2]
  · iapply pointsToByte_congr (frame + UInt32.ofNat 16 + 2)
      (frame + 16 + 2) ((0 : UInt32) >>> 16).toUInt8 0
      (by rfl) (by decide)
    iexact Hdestination2
  ihave Hdestination3Z : ((frame + 16 + 3) ↦w (0 : UInt8)) $$
      [Hdestination3]
  · iapply pointsToByte_congr (frame + UInt32.ofNat 16 + 3)
      (frame + 16 + 3) ((0 : UInt32) >>> 24).toUInt8 0
      (by rfl) (by decide)
    iexact Hdestination3
  ihave Hdestination1Out : ((frame + 16 + 1) ↦w
      ((32 : UInt32) >>> 8).toUInt8) $$ [Hdestination1Z]
  · iapply pointsToByte_congr (frame + 16 + 1) (frame + 16 + 1)
      0 ((32 : UInt32) >>> 8).toUInt8 rfl (by decide)
    iexact Hdestination1Z
  ihave Hdestination2Out : ((frame + 16 + 2) ↦w
      ((32 : UInt32) >>> 16).toUInt8) $$ [Hdestination2Z]
  · iapply pointsToByte_congr (frame + 16 + 2) (frame + 16 + 2)
      0 ((32 : UInt32) >>> 16).toUInt8 rfl (by decide)
    iexact Hdestination2Z
  ihave Hdestination3Out : ((frame + 16 + 3) ↦w
      ((32 : UInt32) >>> 24).toUInt8) $$ [Hdestination3Z]
  · iapply pointsToByte_congr (frame + 16 + 3) (frame + 16 + 3)
      0 ((32 : UInt32) >>> 24).toUInt8 rfl (by decide)
    iexact Hdestination3Z
  ihave HdestinationOut : ((frame + 16) ↦w
      (32 : UInt32).toUInt8) $$ [Hdestination]
  · iapply pointsToByte_congr (frame + 16) (frame + 16)
      32 (32 : UInt32).toUInt8 rfl (by decide)
    iexact Hdestination
  ihave Hframe16 : pointsTo_u32 (frame + 16) 32 $$
      [HdestinationOut Hdestination1Out Hdestination2Out Hdestination3Out]
  · isimp only [pointsTo_u32, u32Byte]
    iframe
  ihave Hframe12Base : pointsTo_u32 (frame + 12) 1 $$ [Hframe12]
  · iapply pointsTo_u32_congr (frame + 8 + 4) (frame + 12)
      1 1 (by bv_decide) rfl
    iexact Hframe12
  iapply twp_localGet rfl
  iapply twp_load32 1 hf120 hf121 hf122 hf123 $$ Hframe12Base
  iintro Hframe12
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (frame + 16) hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_dropValue
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_gtU (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store8_owned oldFrame23 hf230 $$ Hframe23
  iintro Hframe23
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_owned oldFrame22 hf220 $$ Hframe22
  iintro Hframe22
  iapply twp_localGet rfl
  ihave Hframe23ForLoad : ((frame + UInt32.ofNat 23) ↦w (1 : UInt8)) $$
      [Hframe23]
  · iapply pointsToByte_congr (frame + UInt32.ofNat 23)
      (frame + UInt32.ofNat 23) (1 : UInt32).toUInt8 1 rfl (by decide)
    iexact Hframe23
  iapply twp_load8U_owned (1 : UInt8) hf230 $$ Hframe23ForLoad
  iintro Hframe23
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 32 hf160 hf161 hf162 hf163 $$ Hframe16
  iintro Hframe16
  iapply twp_store32 oldFrame24 hf240 hf241 hf242 hf243 $$ Hframe24
  iintro Hframe24
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResult4 hr40 hr41 hr42 hr43 $$ Hresult4
  iintro Hresult4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResult8 hr80 hr81 hr82 hr83 $$ Hresult8
  iintro Hresult8
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldResult12 hr120 hr121 hr122 hr123 $$ Hresult12
  iintro Hresult12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResult16 hr160 hr161 hr162 hr163 $$ Hresult16
  iintro Hresult16
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hresult0At : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hresult0]
  · iapply pointsTo_u32_add_zero'
    iexact Hresult0
  iapply twp_store32 oldResult0 hr00 hr01 hr02 hr03 $$ Hresult0At
  iintro Hresult0At
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store8_owned oldResult24 hr240 $$ Hresult24
  iintro Hresult24
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_load32 32 hf240 hf241 hf242 hf243 $$ Hframe24
  iintro Hframe24
  ihave Hresult20At : pointsTo_u32 ((20 + resultPtr) + 0) oldResult20 $$
      [Hresult20]
  · iapply pointsTo_u32_congr (resultPtr + 20) ((20 + resultPtr) + 0)
      oldResult20 oldResult20 (by bv_decide) rfl
    iexact Hresult20
  iapply twp_store32 (address := 20 + resultPtr) (offset := 0) oldResult20
    hr20z0 hr20z1 hr20z2 hr20z3 $$
    Hresult20At
  iintro Hresult20At
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · iapply globalPointsTo_i32_congr 0 (32 + (stackTop - 32)) stackTop
      (by bv_decide)
    iexact Hglobal
  ihave Hresult0Base : pointsTo_u32 resultPtr 32 $$ [Hresult0At]
  · iapply pointsTo_u32_remove_zero'
    iexact Hresult0At
  ihave Hframe22Base : ((frame + 22) ↦w (0 : UInt8)) $$ [Hframe22]
  · rw [show (0 : UInt32).toUInt8 = (0 : UInt8) by decide]
    iexact Hframe22
  ihave Hframe23Base : ((frame + 23) ↦w (1 : UInt8)) $$ [Hframe23]
  · iexact Hframe23
  ihave Hresult24Base : ((resultPtr + 24) ↦w (1 : UInt8)) $$ [Hresult24]
  · iapply pointsToByte_congr (resultPtr + UInt32.ofNat 24)
      (resultPtr + 24) ((1 : UInt8).toUInt32).toUInt8 1
      (by simp) (by decide)
    iexact Hresult24
  ihave Hresult20Base : pointsTo_u32 (resultPtr + 20) 32 $$ [Hresult20At]
  · iapply pointsTo_u32_congr ((20 + resultPtr) + 0) (resultPtr + 20)
      32 32 (by bv_decide) rfl
    iexact Hresult20At
  ihave Hresult : splitConstructorAt resultPtr data length
      oldResult25 oldResult26 oldResult27 $$
      [Hresult0Base Hresult4 Hresult8 Hresult12 Hresult16 Hresult20Base
        Hresult24Base Hresult25 Hresult26 Hresult27]
  · isimp only [splitConstructorAt]
    iframe
  iapply Hdone $$ Hruntime HglobalTop Hframe8 Hframe12 Hframe16
    Hframe22Base Hframe23Base Hframe24 HcapacityFrame12
    HencodeFrame12 Hresult

private def splitParams (resultPtr data length delimiter : UInt32) :
    List Value :=
  [.i32 resultPtr, .i32 data, .i32 length, .i32 delimiter]

set_option maxHeartbeats 6000000 in
/-- The exact generated descriptor-copy tail of local `func82`, after the
space constructor has returned.  `R` carries the constructor's private frame
ownership through this leaf tail unchanged. -/
theorem stringSplitSpace_after_constructor_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr data length stackTop : UInt32)
    (pad25 pad26 pad27 : UInt8)
    (oldFrame8 oldFrame16 oldFrame24 : UInt64)
    (oldFrame32 oldFrame36 oldFrame40 : UInt32)
    (oldFrame44 oldFrame45 oldFrame46 oldFrame47 : UInt8)
    (oldResult0 oldResult8 oldResult16 oldResult24 oldResult32 : UInt64)
    (R : IProp WasmHeapGF)
    (hframeRoom : (stackTop - 80).toNat + 80 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 40 ≤ UInt32.size)
    {calls : List CallFrame} :
    let frame := stackTop - 80
    let tagWord := packBytes4 1 pad25 pad26 pad27
    let tailWord := packBytes4 1 0 oldFrame46 oldFrame47
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗ R ∗
      pointsTo_u64 (frame + 8) oldFrame8 ∗
      pointsTo_u64 (frame + 16) oldFrame16 ∗
      pointsTo_u64 (frame + 24) oldFrame24 ∗
      pointsTo_u32 (frame + 32) oldFrame32 ∗
      pointsTo_u32 (frame + 36) oldFrame36 ∗
      pointsTo_u32 (frame + 40) oldFrame40 ∗
      ((frame + 44) ↦w oldFrame44) ∗
      ((frame + 45) ↦w oldFrame45) ∗
      ((frame + 46) ↦w oldFrame46) ∗
      ((frame + 47) ↦w oldFrame47) ∗
      splitConstructorAt (frame + 52) data length pad25 pad26 pad27 ∗
      inputIteratorAt resultPtr oldResult0 oldResult8 oldResult16
        oldResult24 oldResult32 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗ R -∗
        pointsTo_u64 (frame + 8) (packU32 32 data) -∗
        pointsTo_u64 (frame + 16) (packU32 length 0) -∗
        pointsTo_u64 (frame + 24) (packU32 length 32) -∗
        pointsTo_u32 (frame + 32) tagWord -∗
        pointsTo_u32 (frame + 36) 0 -∗
        pointsTo_u32 (frame + 40) length -∗
        ((frame + 44) ↦w (1 : UInt8)) -∗
        ((frame + 45) ↦w (0 : UInt8)) -∗
        ((frame + 46) ↦w oldFrame46) -∗
        ((frame + 47) ↦w oldFrame47) -∗
        splitConstructorAt (frame + 52) data length pad25 pad26 pad27 -∗
        inputIteratorAt resultPtr
          (packU32 32 data) (packU32 length 0) (packU32 length 32)
          (packU32 tagWord 0) (packU32 length tailWord) -∗
        WP (.running
          ⟨⟨splitParams resultPtr data length 32, [.i32 frame], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨splitParams resultPtr data length 32, [.i32 frame], []⟩,
        func82.drop 13, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  let frame := stackTop - 80
  let tagWord := packBytes4 1 pad25 pad26 pad27
  let tailWord := packBytes4 1 0 oldFrame46 oldFrame47
  obtain ⟨hf320, hf321, hf322, hf323⟩ :=
    descriptorSlot32Facts frame 32 80 hframeRoom (by decide)
  obtain ⟨hf360, hf361, hf362, hf363⟩ :=
    descriptorSlot32Facts frame 36 80 hframeRoom (by decide)
  obtain ⟨hf400, hf401, hf402, hf403⟩ :=
    descriptorSlot32Facts frame 40 80 hframeRoom (by decide)
  obtain ⟨hf440, _, _, _⟩ :=
    descriptorSlot32Facts frame 44 80 hframeRoom (by decide)
  obtain ⟨hf450, _, _, _⟩ :=
    descriptorSlot32Facts frame 45 80 hframeRoom (by decide)
  obtain ⟨hf520, hf521, hf522, hf523, hf524, hf525, hf526, hf527⟩ :=
    descriptorSlot64Facts frame 52 80 hframeRoom (by decide)
  obtain ⟨hf600, hf601, hf602, hf603, hf604, hf605, hf606, hf607⟩ :=
    descriptorSlot64Facts frame 60 80 hframeRoom (by decide)
  obtain ⟨hf680, hf681, hf682, hf683, hf684, hf685, hf686, hf687⟩ :=
    descriptorSlot64Facts frame 68 80 hframeRoom (by decide)
  obtain ⟨hf760, hf761, hf762, hf763⟩ :=
    descriptorSlot32Facts frame 76 80 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83, hf84, hf85, hf86, hf87⟩ :=
    descriptorSlot64Facts frame 8 80 hframeRoom (by decide)
  obtain ⟨hf160, hf161, hf162, hf163, hf164, hf165, hf166, hf167⟩ :=
    descriptorSlot64Facts frame 16 80 hframeRoom (by decide)
  obtain ⟨hf240, hf241, hf242, hf243, hf244, hf245, hf246, hf247⟩ :=
    descriptorSlot64Facts frame 24 80 hframeRoom (by decide)
  obtain ⟨hf32w0, hf32w1, hf32w2, hf32w3, hf32w4, hf32w5, hf32w6,
      hf32w7⟩ := descriptorSlot64Facts frame 32 80 hframeRoom (by decide)
  obtain ⟨hf40w0, hf40w1, hf40w2, hf40w3, hf40w4, hf40w5, hf40w6,
      hf40w7⟩ := descriptorSlot64Facts frame 40 80 hframeRoom (by decide)
  obtain ⟨hr00, hr01, hr02, hr03, hr04, hr05, hr06, hr07⟩ :=
    descriptorSlot64Facts resultPtr 0 40 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83, hr84, hr85, hr86, hr87⟩ :=
    descriptorSlot64Facts resultPtr 8 40 hresultRoom (by decide)
  obtain ⟨hr160, hr161, hr162, hr163, hr164, hr165, hr166, hr167⟩ :=
    descriptorSlot64Facts resultPtr 16 40 hresultRoom (by decide)
  obtain ⟨hr240, hr241, hr242, hr243, hr244, hr245, hr246, hr247⟩ :=
    descriptorSlot64Facts resultPtr 24 40 hresultRoom (by decide)
  obtain ⟨hr320, hr321, hr322, hr323, hr324, hr325, hr326, hr327⟩ :=
    descriptorSlot64Facts resultPtr 32 40 hresultRoom (by decide)
  iintro ⟨Hruntime, Hglobal, HR, Hf8, Hf16, Hf24, Hf32, Hf36, Hf40,
    Hf44, Hf45, Hf46, Hf47, Hconstructor, Hresult, Hdone⟩
  isimp only [splitConstructorAt] at Hconstructor
  icases Hconstructor with ⟨Hc0, Hc4, Hc8, Hc12, Hc16, Hc20,
    Hc24, Hc25, Hc26, Hc27⟩
  isimp only [inputIteratorAt] at Hresult
  icases Hresult with ⟨Hr0, Hr8, Hr16, Hr24, Hr32⟩
  ihave Hc0At : pointsTo_u32 (frame + 52) 32 $$ [Hc0]
  · iapply pointsTo_u32_congr ((stackTop - 80) + 52) (frame + 52)
      32 32 rfl rfl
    iexact Hc0
  ihave Hc4At : pointsTo_u32 ((frame + 52) + 4) data $$ [Hc4]
  · iapply pointsTo_u32_congr ((stackTop - 80) + 52 + 4)
      ((frame + 52) + 4) data data rfl rfl
    iexact Hc4
  ihave Hc0Word : pointsTo_u64 (frame + 52) (packU32 32 data) $$
      [Hc0At Hc4At]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 52) 32 data).mp
    isimp only [sliceDescriptorAt]
    iframe
  ihave Hc8Word : pointsTo_u64 (frame + 60) (packU32 length 0) $$
      [Hc8 Hc12]
  · iapply pointsTo_u64_congr ((frame + 52) + 8) (frame + 60)
      (packU32 length 0) (packU32 length 0) (by bv_decide) rfl
    iapply (sliceDescriptorAt_eq_u64 ((frame + 52) + 8) length 0).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hc8]
    · iexact Hc8
    ihave Hc12At : pointsTo_u32 (((frame + 52) + 8) + 4) 0 $$ [Hc12]
    · iapply pointsTo_u32_congr ((frame + 52) + 12)
        (((frame + 52) + 8) + 4) 0 0 (by bv_decide) rfl
      iexact Hc12
    iexact Hc12At
  ihave Hc16Word : pointsTo_u64 (frame + 68) (packU32 length 32) $$
      [Hc16 Hc20]
  · iapply pointsTo_u64_congr ((frame + 52) + 16) (frame + 68)
      (packU32 length 32) (packU32 length 32) (by bv_decide) rfl
    iapply (sliceDescriptorAt_eq_u64 ((frame + 52) + 16) length 32).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hc16]
    · iexact Hc16
    ihave Hc20At : pointsTo_u32 (((frame + 52) + 16) + 4) 32 $$ [Hc20]
    · iapply pointsTo_u32_congr ((frame + 52) + 20)
        (((frame + 52) + 16) + 4) 32 32 (by bv_decide) rfl
      iexact Hc20
    iexact Hc20At
  ihave Hc25At : (((frame + 52) + 24 + 1) ↦w pad25) $$ [Hc25]
  · iapply pointsToByte_congr ((frame + 52) + 25) ((frame + 52) + 24 + 1)
      pad25 pad25 (by bv_decide) rfl
    iexact Hc25
  ihave Hc26At : (((frame + 52) + 24 + 2) ↦w pad26) $$ [Hc26]
  · iapply pointsToByte_congr ((frame + 52) + 26) ((frame + 52) + 24 + 2)
      pad26 pad26 (by bv_decide) rfl
    iexact Hc26
  ihave Hc27At : (((frame + 52) + 24 + 3) ↦w pad27) $$ [Hc27]
  · iapply pointsToByte_congr ((frame + 52) + 27) ((frame + 52) + 24 + 3)
      pad27 pad27 (by bv_decide) rfl
    iexact Hc27
  ihave Hc24WordAt : pointsTo_u32 ((frame + 52) + 24) tagWord $$
      [Hc24 Hc25At Hc26At Hc27At]
  · iapply (pointsToBytes4_eq_u32 ((frame + 52) + 24)
      1 pad25 pad26 pad27).mp
    iframe
  ihave Hc24Word : pointsTo_u32 (frame + 76) tagWord $$ [Hc24WordAt]
  · iapply pointsTo_u32_congr ((frame + 52) + 24) (frame + 76)
      tagWord tagWord (by bv_decide) rfl
    iexact Hc24WordAt
  simp only [func82, List.drop]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame36 hf360 hf361 hf362 hf363 $$ Hf36
  iintro Hf36
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldFrame40 hf400 hf401 hf402 hf403 $$ Hf40
  iintro Hf40
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 tagWord hf760 hf761 hf762 hf763 $$ Hc24Word
  iintro Hc24Word
  iapply twp_store32 oldFrame32 hf320 hf321 hf322 hf323 $$ Hf32
  iintro Hf32
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 length 32)
    hf680 hf681 hf682 hf683 hf684 hf685 hf686 hf687 $$ Hc16Word
  iintro Hc16Word
  iapply twp_store64 oldFrame24
    hf240 hf241 hf242 hf243 hf244 hf245 hf246 hf247 $$ Hf24
  iintro Hf24
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 length 0)
    hf600 hf601 hf602 hf603 hf604 hf605 hf606 hf607 $$ Hc8Word
  iintro Hc8Word
  iapply twp_store64 oldFrame16
    hf160 hf161 hf162 hf163 hf164 hf165 hf166 hf167 $$ Hf16
  iintro Hf16
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 32 data)
    hf520 hf521 hf522 hf523 hf524 hf525 hf526 hf527 $$ Hc0Word
  iintro Hc0Word
  iapply twp_store64 oldFrame8
    hf80 hf81 hf82 hf83 hf84 hf85 hf86 hf87 $$ Hf8
  iintro Hf8
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_owned oldFrame44 hf440 $$ Hf44
  iintro Hf44
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_owned oldFrame45 hf450 $$ Hf45
  iintro Hf45
  ihave Hf44Base : ((frame + 44) ↦w (1 : UInt8)) $$ [Hf44]
  · iapply pointsToByte_congr (frame + UInt32.ofNat 44) (frame + 44)
      ((1 : UInt32).toUInt8) 1 (by simp) (by decide)
    iexact Hf44
  ihave Hf45Base : ((frame + 45) ↦w (0 : UInt8)) $$ [Hf45]
  · iapply pointsToByte_congr (frame + UInt32.ofNat 45) (frame + 45)
      ((0 : UInt32).toUInt8) 0 (by simp) (by decide)
    iexact Hf45
  ihave Hf45At : ((frame + 44 + 1) ↦w (0 : UInt8)) $$ [Hf45Base]
  · iapply pointsToByte_congr (frame + 45) (frame + 44 + 1)
      0 0 (by bv_decide) rfl
    iexact Hf45Base
  ihave Hf46At : ((frame + 44 + 2) ↦w oldFrame46) $$ [Hf46]
  · iapply pointsToByte_congr (frame + 46) (frame + 44 + 2)
      oldFrame46 oldFrame46 (by bv_decide) rfl
    iexact Hf46
  ihave Hf47At : ((frame + 44 + 3) ↦w oldFrame47) $$ [Hf47]
  · iapply pointsToByte_congr (frame + 47) (frame + 44 + 3)
      oldFrame47 oldFrame47 (by bv_decide) rfl
    iexact Hf47
  ihave HtailHigh : pointsTo_u32 (frame + 44) tailWord $$
      [Hf44Base Hf45At Hf46At Hf47At]
  · iapply (pointsToBytes4_eq_u32 (frame + 44)
      1 0 oldFrame46 oldFrame47).mp
    iframe
  ihave Hf40Word : pointsTo_u64 (frame + 40) (packU32 length tailWord) $$
      [Hf40 HtailHigh]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 40) length tailWord).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hf40]
    · iexact Hf40
    ihave HtailHighAt : pointsTo_u32 (frame + 40 + 4) tailWord $$ [HtailHigh]
    · iapply pointsTo_u32_congr (frame + 44) (frame + 40 + 4)
        tailWord tailWord (by bv_decide) rfl
      iexact HtailHigh
    iexact HtailHighAt
  ihave Hf32Word : pointsTo_u64 (frame + 32) (packU32 tagWord 0) $$
      [Hf32 Hf36]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 32) tagWord 0).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hf32]
    · iexact Hf32
    ihave Hf36At : pointsTo_u32 (frame + 32 + 4) 0 $$ [Hf36]
    · iapply pointsTo_u32_congr (frame + UInt32.ofNat 36)
        (frame + 32 + 4) 0 0
        (by
          calc
            frame + UInt32.ofNat 36 = frame + ((32 : UInt32) + 4) := by
              congr 1
            _ = frame + 32 + 4 := (UInt32.add_assoc frame 32 4).symm)
        rfl
      iexact Hf36
    iexact Hf36At
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 length tailWord)
    hf40w0 hf40w1 hf40w2 hf40w3 hf40w4 hf40w5 hf40w6 hf40w7 $$ Hf40Word
  iintro Hf40Word
  iapply twp_store64 oldResult32
    hr320 hr321 hr322 hr323 hr324 hr325 hr326 hr327 $$ Hr32
  iintro Hr32
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 tagWord 0)
    hf32w0 hf32w1 hf32w2 hf32w3 hf32w4 hf32w5 hf32w6 hf32w7 $$ Hf32Word
  iintro Hf32Word
  iapply twp_store64 oldResult24
    hr240 hr241 hr242 hr243 hr244 hr245 hr246 hr247 $$ Hr24
  iintro Hr24
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 length 32)
    hf240 hf241 hf242 hf243 hf244 hf245 hf246 hf247 $$ Hf24
  iintro Hf24
  iapply twp_store64 oldResult16
    hr160 hr161 hr162 hr163 hr164 hr165 hr166 hr167 $$ Hr16
  iintro Hr16
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 length 0)
    hf160 hf161 hf162 hf163 hf164 hf165 hf166 hf167 $$ Hf16
  iintro Hf16
  iapply twp_store64 oldResult8
    hr80 hr81 hr82 hr83 hr84 hr85 hr86 hr87 $$ Hr8
  iintro Hr8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 32 data)
    hf80 hf81 hf82 hf83 hf84 hf85 hf86 hf87 $$ Hf8
  iintro Hf8
  ihave Hr0At : pointsTo_u64 (resultPtr + 0) oldResult0 $$ [Hr0]
  · iapply pointsTo_u64_add_zero
    iexact Hr0
  iapply twp_store64 oldResult0
    hr00 hr01 hr02 hr03 hr04 hr05 hr06 hr07 $$ Hr0At
  iintro Hr0At
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · iapply globalPointsTo_i32_congr 0 (80 + (stackTop - 80)) stackTop
      (by bv_decide)
    iexact Hglobal
  ihave Hr0Base : pointsTo_u64 resultPtr (packU32 32 data) $$ [Hr0At]
  · iapply pointsTo_u64_remove_zero
    iexact Hr0At
  ihave HresultOut : inputIteratorAt resultPtr
      (packU32 32 data) (packU32 length 0) (packU32 length 32)
      (packU32 tagWord 0) (packU32 length tailWord) $$
      [Hr0Base Hr8 Hr16 Hr24 Hr32]
  · isimp only [inputIteratorAt]
    iframe
  ihave HconstructorOut : splitConstructorAt (frame + 52) data length
      pad25 pad26 pad27 $$ [Hc0Word Hc8Word Hc16Word Hc24Word]
  · isimp only [splitConstructorAt]
    ihave Hc0Pair : sliceDescriptorAt (frame + 52) 32 data $$ [Hc0Word]
    · iapply (sliceDescriptorAt_eq_u64 (frame + 52) 32 data).mpr
      iexact Hc0Word
    ihave Hc8Pair : sliceDescriptorAt (frame + 60) length 0 $$ [Hc8Word]
    · iapply (sliceDescriptorAt_eq_u64 (frame + 60) length 0).mpr
      iexact Hc8Word
    ihave Hc16Pair : sliceDescriptorAt (frame + 68) length 32 $$ [Hc16Word]
    · iapply (sliceDescriptorAt_eq_u64 (frame + 68) length 32).mpr
      iexact Hc16Word
    isimp only [sliceDescriptorAt] at Hc0Pair Hc8Pair Hc16Pair
    icases Hc0Pair with ⟨Hc0, Hc4⟩
    icases Hc8Pair with ⟨Hc8, Hc12⟩
    icases Hc16Pair with ⟨Hc16, Hc20⟩
    ihave HtagBytes : (iprop% ((frame + 76) ↦w (1 : UInt8)) ∗
        ((frame + 76 + 1) ↦w pad25) ∗
        ((frame + 76 + 2) ↦w pad26) ∗
        ((frame + 76 + 3) ↦w pad27)) $$ [Hc24Word]
    · iapply (pointsToBytes4_eq_u32 (frame + 76)
        1 pad25 pad26 pad27).mpr
      iexact Hc24Word
    icases HtagBytes with ⟨Hc24, Hc25, Hc26, Hc27⟩
    ihave Hc8At : pointsTo_u32 ((frame + 52) + 8) length $$ [Hc8]
    · iapply pointsTo_u32_congr (frame + 60) ((frame + 52) + 8)
        length length (by bv_decide) rfl
      iexact Hc8
    ihave Hc12At : pointsTo_u32 ((frame + 52) + 12) 0 $$ [Hc12]
    · iapply pointsTo_u32_congr (frame + 60 + 4) ((frame + 52) + 12)
        0 0 (by bv_decide) rfl
      iexact Hc12
    ihave Hc16At : pointsTo_u32 ((frame + 52) + 16) length $$ [Hc16]
    · iapply pointsTo_u32_congr (frame + 68) ((frame + 52) + 16)
        length length (by bv_decide) rfl
      iexact Hc16
    ihave Hc20At : pointsTo_u32 ((frame + 52) + 20) 32 $$ [Hc20]
    · iapply pointsTo_u32_congr (frame + 68 + 4) ((frame + 52) + 20)
        32 32 (by bv_decide) rfl
      iexact Hc20
    ihave Hc24At : (((frame + 52) + 24) ↦w (1 : UInt8)) $$ [Hc24]
    · iapply pointsToByte_congr (frame + 76) ((frame + 52) + 24)
        1 1 (by bv_decide) rfl
      iexact Hc24
    ihave Hc25At : (((frame + 52) + 25) ↦w pad25) $$ [Hc25]
    · iapply pointsToByte_congr (frame + 76 + 1) ((frame + 52) + 25)
        pad25 pad25 (by bv_decide) rfl
      iexact Hc25
    ihave Hc26At : (((frame + 52) + 26) ↦w pad26) $$ [Hc26]
    · iapply pointsToByte_congr (frame + 76 + 2) ((frame + 52) + 26)
        pad26 pad26 (by bv_decide) rfl
      iexact Hc26
    ihave Hc27At : (((frame + 52) + 27) ↦w pad27) $$ [Hc27]
    · iapply pointsToByte_congr (frame + 76 + 3) ((frame + 52) + 27)
        pad27 pad27 (by bv_decide) rfl
      iexact Hc27
    iframe
  ihave Hf32Pair : sliceDescriptorAt (frame + 32) tagWord 0 $$ [Hf32Word]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 32) tagWord 0).mpr
    iexact Hf32Word
  isimp only [sliceDescriptorAt] at Hf32Pair
  icases Hf32Pair with ⟨Hf32, Hf36⟩
  ihave Hf36Base : pointsTo_u32 (frame + 36) 0 $$ [Hf36]
  · iapply pointsTo_u32_congr (frame + 32 + 4) (frame + 36)
      0 0 (by bv_decide) rfl
    iexact Hf36
  ihave Hf40Pair : sliceDescriptorAt (frame + 40) length tailWord $$ [Hf40Word]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 40) length tailWord).mpr
    iexact Hf40Word
  isimp only [sliceDescriptorAt] at Hf40Pair
  icases Hf40Pair with ⟨Hf40, HtailHigh⟩
  ihave HtailHighBase : pointsTo_u32 (frame + 44) tailWord $$ [HtailHigh]
  · iapply pointsTo_u32_congr (frame + 40 + 4) (frame + 44)
      tailWord tailWord (by bv_decide) rfl
    iexact HtailHigh
  ihave HtailBytes : (iprop% ((frame + 44) ↦w (1 : UInt8)) ∗
      ((frame + 44 + 1) ↦w (0 : UInt8)) ∗
      ((frame + 44 + 2) ↦w oldFrame46) ∗
      ((frame + 44 + 3) ↦w oldFrame47)) $$ [HtailHighBase]
  · iapply (pointsToBytes4_eq_u32 (frame + 44)
      1 0 oldFrame46 oldFrame47).mpr
    iexact HtailHighBase
  icases HtailBytes with ⟨Hf44, Hf45At, Hf46At, Hf47At⟩
  ihave Hf45 : ((frame + 45) ↦w (0 : UInt8)) $$ [Hf45At]
  · iapply pointsToByte_congr (frame + 44 + 1) (frame + 45)
      0 0 (by bv_decide) rfl
    iexact Hf45At
  ihave Hf46 : ((frame + 46) ↦w oldFrame46) $$ [Hf46At]
  · iapply pointsToByte_congr (frame + 44 + 2) (frame + 46)
      oldFrame46 oldFrame46 (by bv_decide) rfl
    iexact Hf46At
  ihave Hf47 : ((frame + 47) ↦w oldFrame47) $$ [Hf47At]
  · iapply pointsToByte_congr (frame + 44 + 3) (frame + 47)
      oldFrame47 oldFrame47 (by bv_decide) rfl
    iexact Hf47At
  iapply Hdone $$ Hruntime HglobalTop HR Hf8 Hf16 Hf24 Hf32 Hf36Base
    Hf40 Hf44 Hf45 Hf46 Hf47 HconstructorOut HresultOut

set_option maxHeartbeats 8000000 in
/-- Total exact body rule for the successful delimiter-space execution of the
unchanged generated `String::split` (`func82`). -/
theorem stringSplitSpace_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr data length stackTop : UInt32)
    (oldConstructor8 oldConstructor12 oldConstructor16 oldConstructor24 : UInt32)
    (oldConstructor22 oldConstructor23 : UInt8)
    (oldCapacity12 oldEncode12 : UInt32)
    (oldStorage0 oldStorage4 oldStorage8 oldStorage12 oldStorage16 oldStorage20 : UInt32)
    (oldStorage24 oldStorage25 oldStorage26 oldStorage27 : UInt8)
    (oldFrame8 oldFrame16 oldFrame24 : UInt64)
    (oldFrame32 oldFrame36 oldFrame40 : UInt32)
    (oldFrame44 oldFrame45 oldFrame46 oldFrame47 : UInt8)
    (oldResult0 oldResult8 oldResult16 oldResult24 oldResult32 : UInt64)
    (hframeRoom : (stackTop - 80).toNat + 80 ≤ UInt32.size)
    (hconstructorRoom : ((stackTop - 80) - 32).toNat + 32 ≤ UInt32.size)
    (hcapacityRoom : (((stackTop - 80) - 32) - 16).toNat + 16 ≤ UInt32.size)
    (hencodeRoom : ((((stackTop - 80) - 32) - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hstorageRoom : ((stackTop - 80) + 52).toNat + 28 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 40 ≤ UInt32.size)
    {calls : List CallFrame} :
    let frame := stackTop - 80
    let constructorFrame := frame - 32
    let tagWord := packBytes4 1 oldStorage25 oldStorage26 oldStorage27
    let tailWord := packBytes4 1 0 oldFrame46 oldFrame47
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (constructorFrame + 8) oldConstructor8 ∗
      pointsTo_u32 (constructorFrame + 12) oldConstructor12 ∗
      pointsTo_u32 (constructorFrame + 16) oldConstructor16 ∗
      ((constructorFrame + 22) ↦w oldConstructor22) ∗
      ((constructorFrame + 23) ↦w oldConstructor23) ∗
      pointsTo_u32 (constructorFrame + 24) oldConstructor24 ∗
      pointsTo_u32 ((constructorFrame - 16) + 12) oldCapacity12 ∗
      pointsTo_u32 (((constructorFrame - 16) - 16) + 12) oldEncode12 ∗
      pointsTo_u32 ((frame + 52) + 0) oldStorage0 ∗
      pointsTo_u32 ((frame + 52) + 4) oldStorage4 ∗
      pointsTo_u32 ((frame + 52) + 8) oldStorage8 ∗
      pointsTo_u32 ((frame + 52) + 12) oldStorage12 ∗
      pointsTo_u32 ((frame + 52) + 16) oldStorage16 ∗
      pointsTo_u32 ((frame + 52) + 20) oldStorage20 ∗
      (((frame + 52) + 24) ↦w oldStorage24) ∗
      (((frame + 52) + 25) ↦w oldStorage25) ∗
      (((frame + 52) + 26) ↦w oldStorage26) ∗
      (((frame + 52) + 27) ↦w oldStorage27) ∗
      pointsTo_u64 (frame + 8) oldFrame8 ∗
      pointsTo_u64 (frame + 16) oldFrame16 ∗
      pointsTo_u64 (frame + 24) oldFrame24 ∗
      pointsTo_u32 (frame + 32) oldFrame32 ∗
      pointsTo_u32 (frame + 36) oldFrame36 ∗
      pointsTo_u32 (frame + 40) oldFrame40 ∗
      ((frame + 44) ↦w oldFrame44) ∗ ((frame + 45) ↦w oldFrame45) ∗
      ((frame + 46) ↦w oldFrame46) ∗ ((frame + 47) ↦w oldFrame47) ∗
      inputIteratorAt resultPtr oldResult0 oldResult8 oldResult16
        oldResult24 oldResult32 ∗
      (runtimeModuleOwn «module» -∗ globalPointsTo 0 (.i32 stackTop) -∗
        splitConstructorSpaceScratchAt frame -∗
        pointsTo_u64 (frame + 8) (packU32 32 data) -∗
        pointsTo_u64 (frame + 16) (packU32 length 0) -∗
        pointsTo_u64 (frame + 24) (packU32 length 32) -∗
        pointsTo_u32 (frame + 32) tagWord -∗
        pointsTo_u32 (frame + 36) 0 -∗
        pointsTo_u32 (frame + 40) length -∗
        ((frame + 44) ↦w (1 : UInt8)) -∗ ((frame + 45) ↦w (0 : UInt8)) -∗
        ((frame + 46) ↦w oldFrame46) -∗ ((frame + 47) ↦w oldFrame47) -∗
        splitConstructorAt (frame + 52) data length
          oldStorage25 oldStorage26 oldStorage27 -∗
        inputIteratorAt resultPtr
          (packU32 32 data) (packU32 length 0) (packU32 length 32)
          (packU32 tagWord 0) (packU32 length tailWord) -∗
        WP (.running
          ⟨⟨splitParams resultPtr data length 32, [.i32 frame], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨splitParams resultPtr data length 32, [.i32 0], []⟩,
        func82, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  let frame := stackTop - 80
  let constructorFrame := frame - 32
  let tagWord := packBytes4 1 oldStorage25 oldStorage26 oldStorage27
  let tailWord := packBytes4 1 0 oldFrame46 oldFrame47
  iintro ⟨Hruntime, Hglobal, Hc8, Hc12, Hc16, Hc22, Hc23, Hc24,
    Hcap12, Henc12, Hs0, Hs4, Hs8, Hs12, Hs16, Hs20,
    Hs24, Hs25, Hs26, Hs27, Hf8, Hf16, Hf24, Hf32, Hf36, Hf40,
    Hf44, Hf45, Hf46, Hf47, Hresult, Hdone⟩
  simp only [func82]
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
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [splitParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  rw [show (52 : UInt32) + (stackTop - 80) =
      (stackTop - 80) + 52 by bv_decide]
  have HconstructorCall := splitConstructorSpace_call_twp (α := α)
    (frame + 52) data length frame
    oldConstructor8 oldConstructor12 oldConstructor16 oldConstructor24
    oldConstructor22 oldConstructor23 oldCapacity12 oldEncode12
    oldStorage0 oldStorage4 oldStorage8 oldStorage12 oldStorage16 oldStorage20
    oldStorage24 oldStorage25 oldStorage26 oldStorage27
    hconstructorRoom hcapacityRoom hencodeRoom hstorageRoom
    (callerLocals := ⟨splitParams resultPtr data length 32, [.i32 frame], []⟩)
    (stack := []) (code := func82.drop 13) (arity := 0) (remainder := [])
    (controls := []) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil, splitParams, func82, List.drop] at HconstructorCall
  iapply HconstructorCall
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
  isplitl [Hc22]
  · iexact Hc22
  isplitl [Hc23]
  · iexact Hc23
  isplitl [Hc24]
  · iexact Hc24
  isplitl [Hcap12]
  · iexact Hcap12
  isplitl [Henc12]
  · iexact Henc12
  isplitl [Hs0]
  · iexact Hs0
  isplitl [Hs4]
  · iexact Hs4
  isplitl [Hs8]
  · iexact Hs8
  isplitl [Hs12]
  · iexact Hs12
  isplitl [Hs16]
  · iexact Hs16
  isplitl [Hs20]
  · iexact Hs20
  isplitl [Hs24]
  · iexact Hs24
  isplitl [Hs25]
  · iexact Hs25
  isplitl [Hs26]
  · iexact Hs26
  isplitl [Hs27]
  · iexact Hs27
  iintro Hruntime Hglobal Hc8 Hc12 Hc16 Hc22 Hc23 Hc24 Hcap12 Henc12
    Hconstructor
  ihave HR : splitConstructorSpaceScratchAt frame $$
      [Hc8 Hc12 Hc16 Hc22 Hc23 Hc24 Hcap12 Henc12]
  · isimp only [splitConstructorSpaceScratchAt]
    iframe
  have Hafter := stringSplitSpace_after_constructor_twp (α := α)
    resultPtr data length stackTop oldStorage25 oldStorage26 oldStorage27
    oldFrame8 oldFrame16 oldFrame24 oldFrame32 oldFrame36 oldFrame40
    oldFrame44 oldFrame45 oldFrame46 oldFrame47
    oldResult0 oldResult8 oldResult16 oldResult24 oldResult32
    (splitConstructorSpaceScratchAt frame) hframeRoom hresultRoom
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [splitParams, func82, List.drop] at Hafter
  iapply Hafter
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [HR]
  · iexact HR
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hf16]
  · iexact Hf16
  isplitl [Hf24]
  · iexact Hf24
  isplitl [Hf32]
  · iexact Hf32
  isplitl [Hf36]
  · iexact Hf36
  isplitl [Hf40]
  · iexact Hf40
  isplitl [Hf44]
  · iexact Hf44
  isplitl [Hf45]
  · iexact Hf45
  isplitl [Hf46]
  · iexact Hf46
  isplitl [Hf47]
  · iexact Hf47
  isplitl [Hconstructor]
  · iexact Hconstructor
  isplitl [Hresult]
  · iexact Hresult
  iintro Hruntime Hglobal HR Hf8 Hf16 Hf24 Hf32 Hf36 Hf40
    Hf44 Hf45 Hf46 Hf47 Hconstructor Hresult
  iapply Hdone $$ Hruntime Hglobal HR Hf8 Hf16 Hf24 Hf32 Hf36 Hf40
    Hf44 Hf45 Hf46 Hf47 Hconstructor Hresult

/-- Composable absolute-index-84 entry rule for the verified space path of
`String::split`.  Its continuation is exactly the total body rule above. -/
theorem stringSplitSpace_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr data length : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨splitParams resultPtr data length 32, [.i32 0], []⟩,
            func82, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 32, .i32 length, .i32 data, .i32 resultPtr] ++ stack },
        .call 84 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hbody⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 84 func82Def
      (by decide) stringSplit_index $$ Hruntime
  iintro Hruntime
  simp [func82Def, Function.toLocals, Function.numParams, ValueType.zero]
  isimp only [splitParams] at Hbody
  iapply Hbody $$ Hruntime

/-- Exact generated prefix of local `func82`: allocate its eighty-byte
shadow frame and prepare the absolute-index-85 internal split-constructor
call.  This names the only non-leaf seam inside `String::split`. -/
theorem stringSplit_to_constructor_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr data length delimiter stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 80)) -∗
        WP (.running
          ⟨⟨splitParams resultPtr data length delimiter,
              [.i32 (stackTop - 80)],
              [.i32 length, .i32 data, .i32 delimiter,
                .i32 ((stackTop - 80) + 52)]⟩,
            .call 85 :: func82.drop 13, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨splitParams resultPtr data length delimiter, [.i32 0], []⟩,
        func82, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hdone⟩
  simp only [func82, List.drop]
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
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [splitParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  rw [show (52 : UInt32) + (stackTop - 80) =
      (stackTop - 80) + 52 by bv_decide]
  iapply Hdone $$ Hglobal

/-- Absolute-index-84 entry rule for `func82`, exposing its exact internal
absolute-index-85 constructor seam while preserving the caller frame. -/
theorem stringSplit_call_to_constructor_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr data length delimiter stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 80)) -∗
        WP (.running
          ⟨⟨splitParams resultPtr data length delimiter,
              [.i32 (stackTop - 80)],
              [.i32 length, .i32 data, .i32 delimiter,
                .i32 ((stackTop - 80) + 52)]⟩,
            .call 85 :: func82.drop 13, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 delimiter, .i32 length, .i32 data, .i32 resultPtr] ++ stack },
        .call 84 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 84 func82Def
      (by decide) stringSplit_index $$ Hruntime
  iintro Hruntime
  simp [func82Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hprefix := stringSplit_to_constructor_call_twp (α := α)
    resultPtr data length delimiter stackTop
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [splitParams] at Hprefix
  isimp only [splitParams] at Hdone
  iapply Hprefix
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hdone $$ Hruntime Hglobal

/-- Exact body rule for generated local `func90`, `Iterator::map`. -/
theorem iteratorMap_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr : UInt32)
    (word0 word1 word2 word3 word4 : UInt64)
    (old0 old1 old2 old3 old4 : UInt64)
    (hsourceRoom : sourcePtr.toNat + 40 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 40 ≤ UInt32.size)
    {calls : List CallFrame} :
    inputIteratorAt sourcePtr word0 word1 word2 word3 word4 ∗
      inputIteratorAt resultPtr old0 old1 old2 old3 old4 ∗
      (inputIteratorAt sourcePtr word0 word1 word2 word3 word4 -∗
        inputIteratorAt resultPtr word0 word1 word2 word3 word4 -∗
        WP (.running
          ⟨⟨mapParams resultPtr sourcePtr, [], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨mapParams resultPtr sourcePtr, [], []⟩,
        func90, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hs00, hs01, hs02, hs03, hs04, hs05, hs06, hs07⟩ :=
    descriptorSlot64Facts sourcePtr 0 40 hsourceRoom (by decide)
  obtain ⟨hs80, hs81, hs82, hs83, hs84, hs85, hs86, hs87⟩ :=
    descriptorSlot64Facts sourcePtr 8 40 hsourceRoom (by decide)
  obtain ⟨hs160, hs161, hs162, hs163, hs164, hs165, hs166, hs167⟩ :=
    descriptorSlot64Facts sourcePtr 16 40 hsourceRoom (by decide)
  obtain ⟨hs240, hs241, hs242, hs243, hs244, hs245, hs246, hs247⟩ :=
    descriptorSlot64Facts sourcePtr 24 40 hsourceRoom (by decide)
  obtain ⟨hs320, hs321, hs322, hs323, hs324, hs325, hs326, hs327⟩ :=
    descriptorSlot64Facts sourcePtr 32 40 hsourceRoom (by decide)
  obtain ⟨hr00, hr01, hr02, hr03, hr04, hr05, hr06, hr07⟩ :=
    descriptorSlot64Facts resultPtr 0 40 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83, hr84, hr85, hr86, hr87⟩ :=
    descriptorSlot64Facts resultPtr 8 40 hresultRoom (by decide)
  obtain ⟨hr160, hr161, hr162, hr163, hr164, hr165, hr166, hr167⟩ :=
    descriptorSlot64Facts resultPtr 16 40 hresultRoom (by decide)
  obtain ⟨hr240, hr241, hr242, hr243, hr244, hr245, hr246, hr247⟩ :=
    descriptorSlot64Facts resultPtr 24 40 hresultRoom (by decide)
  obtain ⟨hr320, hr321, hr322, hr323, hr324, hr325, hr326, hr327⟩ :=
    descriptorSlot64Facts resultPtr 32 40 hresultRoom (by decide)
  iintro ⟨Hsource, Hresult, Hdone⟩
  isimp only [inputIteratorAt] at Hsource Hresult
  icases Hsource with ⟨Hs0, Hs8, Hs16, Hs24, Hs32⟩
  icases Hresult with ⟨Hr0, Hr8, Hr16, Hr24, Hr32⟩
  simp only [func90]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 word4
    hs320 hs321 hs322 hs323 hs324 hs325 hs326 hs327 $$ Hs32
  iintro Hs32
  iapply twp_store64 old4
    hr320 hr321 hr322 hr323 hr324 hr325 hr326 hr327 $$ Hr32
  iintro Hr32
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 word3
    hs240 hs241 hs242 hs243 hs244 hs245 hs246 hs247 $$ Hs24
  iintro Hs24
  iapply twp_store64 old3
    hr240 hr241 hr242 hr243 hr244 hr245 hr246 hr247 $$ Hr24
  iintro Hr24
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 word2
    hs160 hs161 hs162 hs163 hs164 hs165 hs166 hs167 $$ Hs16
  iintro Hs16
  iapply twp_store64 old2
    hr160 hr161 hr162 hr163 hr164 hr165 hr166 hr167 $$ Hr16
  iintro Hr16
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 word1
    hs80 hs81 hs82 hs83 hs84 hs85 hs86 hs87 $$ Hs8
  iintro Hs8
  iapply twp_store64 old1
    hr80 hr81 hr82 hr83 hr84 hr85 hr86 hr87 $$ Hr8
  iintro Hr8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hs0At : pointsTo_u64 (sourcePtr + 0) word0 $$ [Hs0]
  · iapply pointsTo_u64_add_zero
    iexact Hs0
  iapply twp_load64 word0
    hs00 hs01 hs02 hs03 hs04 hs05 hs06 hs07 $$ Hs0At
  iintro Hs0At
  ihave Hr0At : pointsTo_u64 (resultPtr + 0) old0 $$ [Hr0]
  · iapply pointsTo_u64_add_zero
    iexact Hr0
  iapply twp_store64 old0
    hr00 hr01 hr02 hr03 hr04 hr05 hr06 hr07 $$ Hr0At
  iintro Hr0At
  simp only [mapParams]
  ihave Hs0Base : pointsTo_u64 sourcePtr word0 $$ [Hs0At]
  · iapply pointsTo_u64_remove_zero
    iexact Hs0At
  ihave Hr0Base : pointsTo_u64 resultPtr word0 $$ [Hr0At]
  · iapply pointsTo_u64_remove_zero
    iexact Hr0At
  ihave Hsource : inputIteratorAt sourcePtr word0 word1 word2 word3 word4 $$
      [Hs0Base Hs8 Hs16 Hs24 Hs32]
  · isimp only [inputIteratorAt]
    iframe
  ihave Hresult : inputIteratorAt resultPtr word0 word1 word2 word3 word4 $$
      [Hr0Base Hr8 Hr16 Hr24 Hr32]
  · isimp only [inputIteratorAt]
    iframe
  iapply Hdone $$ Hsource Hresult

/-- Composable absolute-index-92 call rule for generated `func90`. -/
theorem iteratorMap_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr : UInt32)
    (word0 word1 word2 word3 word4 : UInt64)
    (old0 old1 old2 old3 old4 : UInt64)
    (hsourceRoom : sourcePtr.toNat + 40 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 40 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      inputIteratorAt sourcePtr word0 word1 word2 word3 word4 ∗
      inputIteratorAt resultPtr old0 old1 old2 old3 old4 ∗
      (runtimeModuleOwn «module» -∗
        inputIteratorAt sourcePtr word0 word1 word2 word3 word4 -∗
        inputIteratorAt resultPtr word0 word1 word2 word3 word4 -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 sourcePtr, .i32 resultPtr] ++ stack },
        .call 92 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsource, Hresult, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 92 func90Def
      (by decide) iteratorMap_index $$ Hruntime
  iintro Hruntime
  simp [func90Def, Function.toLocals, Function.numParams]
  have Hbody := iteratorMap_body_twp (α := α)
    resultPtr sourcePtr word0 word1 word2 word3 word4
    old0 old1 old2 old3 old4 hsourceRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [mapParams] at Hbody
  iapply Hbody
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hresult]
  · iexact Hresult
  iintro Hsource Hresult
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hsource Hresult

private def collectParams (resultPtr sourcePtr : UInt32) : List Value :=
  [.i32 resultPtr, .i32 sourcePtr]

/-- Capacity candidate computed by the generated collect core from its lower
size hint, including the overflow-to-`u32::MAX` select. -/
def collectInitialCapacity (hint : UInt32) : UInt32 :=
  if hint + 1 ≠ 0 then hint + 1 else 4294967295

/-- Branch flag selecting the generated minimum-capacity-four path. -/
def collectCapacityTooSmall (hint : UInt32) : UInt32 :=
  if collectInitialCapacity hint < 4 then 1 else 0

private def leadingBlockBody (program : Program) : Program :=
  match program with
  | .block 0 0 body :: _ => body
  | _ => []

private def collectCoreOuterBody : Program :=
  leadingBlockBody (func10.drop 11)

private def collectCoreBlock1Body : Program :=
  leadingBlockBody collectCoreOuterBody

private def collectCoreBlock2Body : Program :=
  leadingBlockBody collectCoreBlock1Body

private def collectCoreBlock3Body : Program :=
  leadingBlockBody collectCoreBlock2Body

private def collectCoreInnerBody : Program :=
  leadingBlockBody collectCoreBlock3Body

private def collectBlockFrame (body continuation : Program) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := body
    continuation := continuation
    belowStack := [] }

private def collectCoreSomeControls
    (controls : List ControlFrame) : List ControlFrame :=
  collectBlockFrame collectCoreInnerBody (collectCoreBlock3Body.drop 1) ::
    collectBlockFrame collectCoreBlock3Body (collectCoreBlock2Body.drop 1) ::
    collectBlockFrame collectCoreBlock2Body (collectCoreBlock1Body.drop 1) ::
    collectBlockFrame collectCoreBlock1Body (collectCoreOuterBody.drop 1) ::
    collectBlockFrame collectCoreOuterBody (func10.drop 12) :: controls

private def collectCoreAllocationControls
    (controls : List ControlFrame) : List ControlFrame :=
  collectBlockFrame collectCoreOuterBody (func10.drop 12) :: controls

/-- Local `func118` is byte-for-byte the same five-word iterator copy as
`func90`; reuse the proved body rather than duplicating its stores. -/
theorem iteratorFromIter_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr : UInt32)
    (word0 word1 word2 word3 word4 : UInt64)
    (old0 old1 old2 old3 old4 : UInt64)
    (hsourceRoom : sourcePtr.toNat + 40 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 40 ≤ UInt32.size)
    {calls : List CallFrame} :
    inputIteratorAt sourcePtr word0 word1 word2 word3 word4 ∗
      inputIteratorAt resultPtr old0 old1 old2 old3 old4 ∗
      (inputIteratorAt sourcePtr word0 word1 word2 word3 word4 -∗
        inputIteratorAt resultPtr word0 word1 word2 word3 word4 -∗
        WP (.running
          ⟨⟨mapParams resultPtr sourcePtr, [], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨mapParams resultPtr sourcePtr, [], []⟩,
        func118, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [show func118 = func90 by rfl]
  exact iteratorMap_body_twp resultPtr sourcePtr
    word0 word1 word2 word3 word4 old0 old1 old2 old3 old4
    hsourceRoom hresultRoom

/-- Composable absolute-index-120 rule for the local-118 iterator copy. -/
theorem iteratorFromIter_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr : UInt32)
    (word0 word1 word2 word3 word4 : UInt64)
    (old0 old1 old2 old3 old4 : UInt64)
    (hsourceRoom : sourcePtr.toNat + 40 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 40 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      inputIteratorAt sourcePtr word0 word1 word2 word3 word4 ∗
      inputIteratorAt resultPtr old0 old1 old2 old3 old4 ∗
      (runtimeModuleOwn «module» -∗
        inputIteratorAt sourcePtr word0 word1 word2 word3 word4 -∗
        inputIteratorAt resultPtr word0 word1 word2 word3 word4 -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 sourcePtr, .i32 resultPtr] ++ stack },
        .call 120 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsource, Hresult, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 120 func118Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func118Def, Function.toLocals, Function.numParams]
  have Hbody := iteratorFromIter_body_twp (α := α)
    resultPtr sourcePtr word0 word1 word2 word3 word4
    old0 old1 old2 old3 old4 hsourceRoom hresultRoom
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [mapParams] at Hbody
  iapply Hbody
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hresult]
  · iexact Hresult
  iintro Hsource Hresult
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hsource Hresult

/-- Exact local-91 forwarding body: `Iterator::collect` delegates unchanged
to absolute call 94 (local `func92`). -/
theorem iteratorCollect_to_impl_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr : UInt32) {calls : List CallFrame} :
    (WP (.running
      ⟨⟨collectParams resultPtr sourcePtr, [], [.i32 sourcePtr, .i32 resultPtr]⟩,
        [.call 94, .ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr sourcePtr, [], []⟩,
        func91, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hdone
  simp only [func91]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [collectParams]
  iexact Hdone

/-- Absolute-index-93 entry for the forwarding collect shim. -/
theorem iteratorCollect_call_to_impl_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨collectParams resultPtr sourcePtr, [],
              [.i32 sourcePtr, .i32 resultPtr]⟩,
            [.call 94, .ret], 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 sourcePtr, .i32 resultPtr] ++ stack },
        .call 93 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 93 func91Def
      (by decide) iteratorCollect_index $$ Hruntime
  iintro Hruntime
  simp [func91Def, Function.toLocals, Function.numParams]
  have Hforward := iteratorCollect_to_impl_twp (α := α) resultPtr sourcePtr
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [collectParams] at Hforward
  iapply Hforward
  isimp only [collectParams] at Hdone
  iapply Hdone $$ Hruntime

/-- Exact prefix of local `func92`: establish its forty-eight-byte shadow
frame and expose absolute call 120, the next collect implementation seam. -/
theorem iteratorCollectImpl_to_from_iter_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr stackTop : UInt32) {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        WP (.running
          ⟨⟨collectParams resultPtr sourcePtr, [.i32 (stackTop - 48)],
              [.i32 sourcePtr, .i32 ((stackTop - 48) + 8)]⟩,
            .call 120 :: func92.drop 11, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr sourcePtr, [.i32 0], []⟩,
        func92, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hdone⟩
  simp only [func92]
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
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  simp only [collectParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  rw [show (8 : UInt32) + (stackTop - 48) =
      (stackTop - 48) + 8 by bv_decide]
  isimp only [func92, List.drop] at Hdone
  iapply Hdone $$ Hglobal

/-- Absolute-index-94 entry for local `func92`, exposing the exact call-120
boundary while preserving the outer caller frame. -/
theorem iteratorCollectImpl_call_to_from_iter_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗ globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        WP (.running
          ⟨⟨collectParams resultPtr sourcePtr, [.i32 (stackTop - 48)],
              [.i32 sourcePtr, .i32 ((stackTop - 48) + 8)]⟩,
            .call 120 :: func92.drop 11, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 sourcePtr, .i32 resultPtr] ++ stack },
        .call 94 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 94 func92Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func92Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Himpl := iteratorCollectImpl_to_from_iter_call_twp (α := α)
    resultPtr sourcePtr stackTop
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [collectParams] at Himpl
  iapply Himpl
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  isimp only [collectParams] at Hdone
  iapply Hdone $$ Hruntime Hglobal

/-- Local `func124` is the generated consumption shim; it forwards its result
and iterator pointers unchanged to absolute call 12 (local `func10`). -/
theorem iteratorCollectConsume_to_core_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr : UInt32) {calls : List CallFrame} :
    (WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr, [],
          [.i32 iteratorPtr, .i32 resultPtr]⟩,
        [.call 12, .ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr, [], []⟩,
        func124, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hdone
  simp only [func124]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [collectParams]
  iexact Hdone

/-- Absolute-index-126 entry for the consumption shim, exposing the exact
absolute-12/local-10 collect-core seam. -/
theorem iteratorCollectConsume_call_to_core_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr, [],
              [.i32 iteratorPtr, .i32 resultPtr]⟩,
            [.call 12, .ret], 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 iteratorPtr, .i32 resultPtr] ++ stack },
        .call 126 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 126 func124Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func124Def, Function.toLocals, Function.numParams]
  have Hforward := iteratorCollectConsume_to_core_twp (α := α)
    resultPtr iteratorPtr
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [collectParams] at Hforward
  iapply Hforward
  isimp only [collectParams] at Hdone
  iapply Hdone $$ Hruntime

/-- Once the local-10 collect core has populated the result descriptor, the
remaining local-92 epilogue preserves it and restores the forty-eight-byte
shadow frame exactly. -/
theorem iteratorCollectImpl_after_consume_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr stackTop capacity data length : UInt32)
    (R : IProp WasmHeapGF) {calls : List CallFrame} :
    let frame := stackTop - 48
    globalPointsTo 0 (.i32 frame) ∗
      vecDescriptorAt resultPtr capacity data length ∗ R ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        vecDescriptorAt resultPtr capacity data length -∗ R -∗
        WP (.running
          ⟨⟨collectParams resultPtr sourcePtr, [.i32 frame], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr sourcePtr, [.i32 frame], []⟩,
        func92.drop 16, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  let frame := stackTop - 48
  iintro ⟨Hglobal, Hresult, HR, Hdone⟩
  simp only [func92, List.drop]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · iapply globalPointsTo_i32_congr 0 (48 + (stackTop - 48)) stackTop
      (by bv_decide)
    iexact Hglobal
  iapply Hdone $$ HglobalTop Hresult HR

/-- Exact local-92 path through the proved local-118 copy and local-124
forwarder.  The only remaining obligation is the isolated absolute-12/local-10
collection core; its caller continuation is already the verified descriptor
preserving/global-restoring epilogue. -/
theorem iteratorCollectImpl_to_core_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr sourcePtr stackTop : UInt32)
    (word0 word1 word2 word3 word4 : UInt64)
    (oldTemp0 oldTemp1 oldTemp2 oldTemp3 oldTemp4 : UInt64)
    (hsourceRoom : sourcePtr.toNat + 40 ≤ UInt32.size)
    (htempRoom : ((stackTop - 48) + 8).toNat + 40 ≤ UInt32.size)
    {calls : List CallFrame} :
    let frame := stackTop - 48
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 frame) ∗
      inputIteratorAt sourcePtr word0 word1 word2 word3 word4 ∗
      inputIteratorAt (frame + 8) oldTemp0 oldTemp1 oldTemp2 oldTemp3 oldTemp4 ∗
      (runtimeModuleOwn «module» -∗ globalPointsTo 0 (.i32 frame) -∗
        inputIteratorAt sourcePtr word0 word1 word2 word3 word4 -∗
        inputIteratorAt (frame + 8) word0 word1 word2 word3 word4 -∗
        WP (.running
          ⟨⟨collectParams resultPtr (frame + 8), [],
              [.i32 (frame + 8), .i32 resultPtr]⟩,
            [.call 12, .ret], 0, [], [],
            { locals :=
                ⟨collectParams resultPtr sourcePtr, [.i32 frame], []⟩
              continuation := func92.drop 16
              resultArity := 0
              callerRemainder := []
              control := [] } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr sourcePtr, [.i32 frame],
          [.i32 sourcePtr, .i32 (frame + 8)]⟩,
        .call 120 :: func92.drop 11, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  dsimp only
  let frame := stackTop - 48
  iintro ⟨Hruntime, Hglobal, Hsource, Htemp, Hcore⟩
  simp only [func92, List.drop]
  have Hcopy := iteratorFromIter_call_twp (α := α)
    (frame + 8) sourcePtr word0 word1 word2 word3 word4
    oldTemp0 oldTemp1 oldTemp2 oldTemp3 oldTemp4 hsourceRoom htempRoom
    (callerLocals := ⟨collectParams resultPtr sourcePtr, [.i32 frame], []⟩)
    (stack := []) (code := func92.drop 11) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil, func92, List.drop] at Hcopy
  iapply Hcopy
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemp]
  · iexact Htemp
  iintro Hruntime Hsource Htemp
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (8 : UInt32) + frame = frame + 8 by bv_decide]
  have Hconsume := iteratorCollectConsume_call_to_core_twp (α := α)
    resultPtr (frame + 8)
    (callerLocals := ⟨collectParams resultPtr sourcePtr, [.i32 frame], []⟩)
    (stack := []) (code := func92.drop 16) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil, func92, List.drop] at Hconsume
  iapply Hconsume
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  iapply Hcore $$ Hruntime Hglobal Hsource Htemp

/-- Exact body rule for local `func4`, the size-hint leaf used by collect.
The two static words are read-only inputs and are returned unchanged. -/
theorem iteratorSizeHint_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr low high old0 old4 old8 : UInt32)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 resultPtr old0 ∗
      pointsTo_u32 (resultPtr + 4) old4 ∗
      pointsTo_u32 (resultPtr + 8) old8 ∗
      pointsTo_u32 1049096 low ∗
      pointsTo_u32 1049100 high ∗
      (pointsTo_u32 resultPtr 0 -∗
        pointsTo_u32 (resultPtr + 4) low -∗
        pointsTo_u32 (resultPtr + 8) high -∗
        pointsTo_u32 1049096 low -∗
        pointsTo_u32 1049100 high -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 iteratorPtr], [.i32 low, .i32 high], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 iteratorPtr], [.i32 0, .i32 0], []⟩,
        func4, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    descriptorSlot32Facts resultPtr 0 12 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    descriptorSlot32Facts resultPtr 4 12 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83⟩ :=
    descriptorSlot32Facts resultPtr 8 12 hresultRoom (by decide)
  have hs0 : ((0 : UInt32) + 1049096).toNat =
      (0 : UInt32).toNat + (1049096 : UInt32).toNat := by decide
  have hs1 : (((0 : UInt32) + 1049096) + 1).toNat =
      ((0 : UInt32) + 1049096).toNat + 1 := by decide
  have hs2 : (((0 : UInt32) + 1049096) + 2).toNat =
      ((0 : UInt32) + 1049096).toNat + 2 := by decide
  have hs3 : (((0 : UInt32) + 1049096) + 3).toNat =
      ((0 : UInt32) + 1049096).toNat + 3 := by decide
  have ht0 : ((0 : UInt32) + 1049100).toNat =
      (0 : UInt32).toNat + (1049100 : UInt32).toNat := by decide
  have ht1 : (((0 : UInt32) + 1049100) + 1).toNat =
      ((0 : UInt32) + 1049100).toNat + 1 := by decide
  have ht2 : (((0 : UInt32) + 1049100) + 2).toNat =
      ((0 : UInt32) + 1049100).toNat + 2 := by decide
  have ht3 : (((0 : UInt32) + 1049100) + 3).toNat =
      ((0 : UInt32) + 1049100).toNat + 3 := by decide
  iintro ⟨Hr0, Hr4, Hr8, HstaticLow, HstaticHigh, Hdone⟩
  ihave Hr0At : pointsTo_u32 (resultPtr + 0) old0 $$ [Hr0]
  · iapply pointsTo_u32_add_zero'
    iexact Hr0
  ihave HstaticLowAt : pointsTo_u32 (0 + 1049096) low $$ [HstaticLow]
  · iapply pointsTo_u32_congr 1049096 (0 + 1049096) low low
        (by decide) rfl
    iexact HstaticLow
  ihave HstaticHighAt : pointsTo_u32 (0 + 1049100) high $$ [HstaticHigh]
  · iapply pointsTo_u32_congr 1049100 (0 + 1049100) high high
        (by decide) rfl
    iexact HstaticHigh
  simp only [func4]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old0 hr0 hr1 hr2 hr3 $$ Hr0At
  iintro Hr0At
  iapply twp_const
  iapply twp_load32 (address := 0) (offset := 1049096)
      low hs0 hs1 hs2 hs3 $$ HstaticLowAt
  iintro HstaticLowAt
  iapply twp_localSet rfl
  iapply twp_const
  iapply twp_load32 (address := 0) (offset := 1049100)
      high ht0 ht1 ht2 ht3 $$ HstaticHighAt
  iintro HstaticHighAt
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old4 hr40 hr41 hr42 hr43 $$ Hr4
  iintro Hr4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old8 hr80 hr81 hr82 hr83 $$ Hr8
  iintro Hr8
  ihave Hr0 : pointsTo_u32 resultPtr 0 $$ [Hr0At]
  · iapply pointsTo_u32_remove_zero'
    iexact Hr0At
  ihave HstaticLow : pointsTo_u32 1049096 low $$ [HstaticLowAt]
  · iapply pointsTo_u32_congr (0 + 1049096) 1049096 low low
        (by decide) rfl
    iexact HstaticLowAt
  ihave HstaticHigh : pointsTo_u32 1049100 high $$ [HstaticHighAt]
  · iapply pointsTo_u32_congr (0 + 1049100) 1049100 high high
        (by decide) rfl
    iexact HstaticHighAt
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply Hdone $$ Hr0 Hr4 Hr8 HstaticLow HstaticHigh

/-- Composable absolute-index-6 rule for the size-hint leaf. -/
theorem iteratorSizeHint_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr low high old0 old4 old8 : UInt32)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 resultPtr old0 ∗ pointsTo_u32 (resultPtr + 4) old4 ∗
      pointsTo_u32 (resultPtr + 8) old8 ∗ pointsTo_u32 1049096 low ∗
      pointsTo_u32 1049100 high ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 resultPtr 0 -∗ pointsTo_u32 (resultPtr + 4) low -∗
        pointsTo_u32 (resultPtr + 8) high -∗ pointsTo_u32 1049096 low -∗
        pointsTo_u32 1049100 high -∗
        WP (.running ⟨{ callerLocals with values := stack }, code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 iteratorPtr, .i32 resultPtr] ++ stack },
        .call 6 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hr0, Hr4, Hr8, HstaticLow, HstaticHigh, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 6 func4Def
      (by decide) iteratorSizeHint_index $$ Hruntime
  iintro Hruntime
  simp [func4Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply iteratorSizeHint_body_twp resultPtr iteratorPtr low high
      old0 old4 old8 hresultRoom
  isplitl [Hr0]
  · iexact Hr0
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  isplitl [HstaticLow]
  · iexact HstaticLow
  isplitl [HstaticHigh]
  · iexact HstaticHigh
  iintro Hr0 Hr4 Hr8 HstaticLow HstaticHigh
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hr0 Hr4 Hr8 HstaticLow HstaticHigh

/-- Exact forwarding body for local `func3`; its only behavior is the
absolute-index-6 size-hint call. -/
theorem iteratorSizeHintForward_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr : UInt32) {calls : List CallFrame} :
    (WP (.running
      ⟨⟨[.i32 resultPtr, .i32 iteratorPtr], [],
          [.i32 iteratorPtr, .i32 resultPtr]⟩,
        [.call 6, .ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 iteratorPtr], [], []⟩,
        func3, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  simp only [func3]
  iintro Hdone
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iexact Hdone

/-- Absolute-index-5/local-3 forwarding rule, exposing absolute call 6. -/
theorem iteratorSizeHintForward_call_to_leaf_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 iteratorPtr], [],
              [.i32 iteratorPtr, .i32 resultPtr]⟩,
            [.call 6, .ret], 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 iteratorPtr, .i32 resultPtr] ++ stack },
        .call 5 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 5 func3Def
      (by decide) iteratorSizeHintForward_index $$ Hruntime
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams]
  iapply iteratorSizeHintForward_body_twp resultPtr iteratorPtr
  iapply Hdone $$ Hruntime

/-- Composable absolute-index-5 rule, obtained by chaining the generated
forwarder with the exact size-hint leaf. -/
theorem iteratorSizeHintForward_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr low high old0 old4 old8 : UInt32)
    (hresultRoom : resultPtr.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 resultPtr old0 ∗ pointsTo_u32 (resultPtr + 4) old4 ∗
      pointsTo_u32 (resultPtr + 8) old8 ∗ pointsTo_u32 1049096 low ∗
      pointsTo_u32 1049100 high ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 resultPtr 0 -∗ pointsTo_u32 (resultPtr + 4) low -∗
        pointsTo_u32 (resultPtr + 8) high -∗ pointsTo_u32 1049096 low -∗
        pointsTo_u32 1049100 high -∗
        WP (.running ⟨{ callerLocals with values := stack }, code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 iteratorPtr, .i32 resultPtr] ++ stack },
        .call 5 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hr0, Hr4, Hr8, HstaticLow, HstaticHigh, Hdone⟩
  iapply iteratorSizeHintForward_call_to_leaf_twp resultPtr iteratorPtr
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  have Hleaf := iteratorSizeHint_call_twp (α := α)
    resultPtr iteratorPtr low high old0 old4 old8 hresultRoom
    (callerLocals := ⟨[.i32 resultPtr, .i32 iteratorPtr], [], []⟩)
    (stack := []) (code := [.ret]) (arity := 0) (remainder := [])
    (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil] at Hleaf
  iapply Hleaf
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hr0]
  · iexact Hr0
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  isplitl [HstaticLow]
  · iexact HstaticLow
  isplitl [HstaticHigh]
  · iexact HstaticHigh
  iintro Hruntime Hr0 Hr4 Hr8 HstaticLow HstaticHigh
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hr0 Hr4 Hr8 HstaticLow HstaticHigh

/-- The successful (`Some`) first-next discriminator in local `func10`.
This lemma is deliberately independent of the surrounding five blocks: it
records the stable invariant needed at the following size-hint call. -/
theorem iteratorCollectCore_first_some_to_size_hint_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr frame : UInt32) (first : UInt64)
    (hframeRoom : frame.toNat + 40 ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u64 (frame + 24) 1 ∗ pointsTo_u64 (frame + 32) first ∗
      (pointsTo_u64 (frame + 24) 1 -∗
        pointsTo_u64 (frame + 32) first -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 frame, .i64 first, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 iteratorPtr, .i32 (frame + 44)]⟩,
            .call 5 :: code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr,
          [.i32 frame, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        [.localGet 2, .load64 24, .wrapI64, .const 1, .and, .eqz,
          .br_if 0, .localGet 2, .load64 32, .localSet 3,
          .localGet 2, .const 44, .add, .localGet 1, .call 5] ++ code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ :=
    descriptorSlot64Facts frame 24 40 hframeRoom (by decide)
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
    descriptorSlot64Facts frame 32 40 hframeRoom (by decide)
  iintro ⟨Hdiscriminant, Hpayload, Hdone⟩
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load64 1 hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 $$ Hdiscriminant
  iintro Hdiscriminant
  iapply twp_wrapI64
  rw [show UInt32.ofNat ((1 : UInt64).toNat % 2 ^ 32) = 1 by decide]
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (value := 1) (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_load64 first hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 $$ Hpayload
  iintro Hpayload
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  simp only [collectParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  rw [show (44 : UInt32) + frame = frame + 44 by bv_decide]
  iapply Hdone $$ Hdiscriminant Hpayload

/-- Enter the five generated collect blocks after the first `next` call and
compose the successful discriminator lemma.  This connects the top-level
func10 checkpoint to its absolute-index-5 size-hint call without flattening
the generated control stack. -/
theorem iteratorCollectCore_after_first_next_some_to_size_hint_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr frame : UInt32) (first : UInt64)
    (hframeRoom : frame.toNat + 40 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u64 (frame + 24) 1 ∗ pointsTo_u64 (frame + 32) first ∗
      (pointsTo_u64 (frame + 24) 1 -∗
        pointsTo_u64 (frame + 32) first -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 frame, .i64 first, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 iteratorPtr, .i32 (frame + 44)]⟩,
            .call 5 :: collectCoreInnerBody.drop 15,
            arity, remainder, collectCoreSomeControls controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr,
          [.i32 frame, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func10.drop 11, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hdiscriminant, Hpayload, Hdone⟩
  simp only [func10, List.drop]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  have Hsome := iteratorCollectCore_first_some_to_size_hint_twp (α := α)
    resultPtr iteratorPtr frame first hframeRoom
    (code := collectCoreInnerBody.drop 15)
    (arity := arity) (remainder := remainder)
    (controls := collectCoreSomeControls controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [collectCoreInnerBody, collectCoreBlock3Body,
    collectCoreBlock2Body, collectCoreBlock1Body,
    collectCoreOuterBody, leadingBlockBody, collectCoreSomeControls,
    collectBlockFrame, func10, List.drop, List.cons_append,
    List.nil_append] at Hsome ⊢
  iapply Hsome
  isplitl [Hdiscriminant]
  · iexact Hdiscriminant
  isplitl [Hpayload]
  · iexact Hpayload
  iintro Hdiscriminant Hpayload
  iapply Hdone $$ Hdiscriminant Hpayload

/-- Linear capacity-selection suffix after the size-hint call in `func10`.
It updates frame offset 56 and stops exactly at the depth-two branch that
joins the minimum-capacity-four and ordinary allocation paths. -/
theorem iteratorCollectCore_size_hint_to_capacity_branch_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr frame : UInt32) (first : UInt64)
    (hint oldCapacity : UInt32)
    (hframeRoom : frame.toNat + 60 ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 (frame + 44) hint ∗
      pointsTo_u32 (frame + 56) oldCapacity ∗
      (pointsTo_u32 (frame + 44) hint -∗
        pointsTo_u32 (frame + 56) (collectInitialCapacity hint) -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 frame, .i64 first, .i32 (hint + 1),
                .i32 0, .i32 0, .i32 0],
              [.i32 (collectCapacityTooSmall hint)]⟩,
            .br_if 2 :: code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr,
          [.i32 frame, .i64 first, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        [.localGet 2, .load32 44, .const 1, .add, .localSet 4,
          .localGet 2, .localGet 4, .const 4294967295, .localGet 4,
          .select, .store32 56, .localGet 2, .load32 56, .const 4,
          .ltU, .const 1, .and, .br_if 2] ++ code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hh0, hh1, hh2, hh3⟩ :=
    descriptorSlot32Facts frame 44 60 hframeRoom (by decide)
  obtain ⟨hc0, hc1, hc2, hc3⟩ :=
    descriptorSlot32Facts frame 56 60 hframeRoom (by decide)
  iintro ⟨Hhint, Hcapacity, Hdone⟩
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 hint hh0 hh1 hh2 hh3 $$ Hhint
  iintro Hhint
  iapply twp_const
  iapply twp_add
  iapply twp_localSet rfl
  simp only [collectParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  rw [show (1 : UInt32) + hint = hint + 1 by bv_decide]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_selectI32 (selected := collectInitialCapacity hint) rfl
  iapply twp_store32 oldCapacity hc0 hc1 hc2 hc3 $$ Hcapacity
  iintro Hcapacity
  iapply twp_localGet rfl
  iapply twp_load32 (collectInitialCapacity hint)
      hc0 hc1 hc2 hc3 $$ Hcapacity
  iintro Hcapacity
  iapply twp_const
  iapply twp_ltU (result := collectCapacityTooSmall hint) rfl
  iapply twp_const
  iapply twp_and
  rw [show collectCapacityTooSmall hint &&& 1 =
      collectCapacityTooSmall hint by
    simp only [collectCapacityTooSmall]
    split <;> decide]
  iapply Hdone $$ Hhint Hcapacity

/-- Full nonempty prefix after the first iterator `next`: enter all generated
blocks, execute absolute call 5/6, and compute the depth-two minimum-capacity
branch.  The leaf size hint has lower bound zero, so this path deterministically
selects the generated initial-capacity-four branch. -/
theorem iteratorCollectCore_after_first_next_some_to_capacity_branch_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr frame : UInt32) (first : UInt64)
    (staticLow staticHigh old44 old48 old52 old56 : UInt32)
    (hframeRoom : frame.toNat + 60 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u64 (frame + 24) 1 ∗ pointsTo_u64 (frame + 32) first ∗
      pointsTo_u32 (frame + 44) old44 ∗ pointsTo_u32 (frame + 48) old48 ∗
      pointsTo_u32 (frame + 52) old52 ∗ pointsTo_u32 (frame + 56) old56 ∗
      pointsTo_u32 1049096 staticLow ∗ pointsTo_u32 1049100 staticHigh ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u64 (frame + 24) 1 -∗ pointsTo_u64 (frame + 32) first -∗
        pointsTo_u32 (frame + 44) 0 -∗
        pointsTo_u32 (frame + 48) staticLow -∗
        pointsTo_u32 (frame + 52) staticHigh -∗
        pointsTo_u32 (frame + 56) (collectInitialCapacity 0) -∗
        pointsTo_u32 1049096 staticLow -∗ pointsTo_u32 1049100 staticHigh -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 frame, .i64 first, .i32 1, .i32 0, .i32 0, .i32 0],
              [.i32 (collectCapacityTooSmall 0)]⟩,
            [.br_if 2, .br 1], arity, remainder,
            collectCoreSomeControls controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr,
          [.i32 frame, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func10.drop 11, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h44, _, _, _⟩ :=
    descriptorSlot32Facts frame 44 60 hframeRoom (by decide)
  have h44' : (frame + 44).toNat = frame.toNat + 44 := by
    simpa using h44
  have hsizeRoom : (frame + 44).toNat + 12 ≤ UInt32.size := by
    rw [h44']
    omega
  iintro ⟨Hruntime, Hdiscriminant, Hpayload, H44, H48, H52, H56,
    HstaticLow, HstaticHigh, Hdone⟩
  iapply iteratorCollectCore_after_first_next_some_to_size_hint_twp
      resultPtr iteratorPtr frame first (by omega)
  isplitl [Hdiscriminant]
  · iexact Hdiscriminant
  isplitl [Hpayload]
  · iexact Hpayload
  iintro Hdiscriminant Hpayload
  ihave H48At : pointsTo_u32 ((frame + 44) + 4) old48 $$ [H48]
  · iapply pointsTo_u32_congr (frame + 48) ((frame + 44) + 4)
        old48 old48 (by bv_decide) rfl
    iexact H48
  ihave H52At : pointsTo_u32 ((frame + 44) + 8) old52 $$ [H52]
  · iapply pointsTo_u32_congr (frame + 52) ((frame + 44) + 8)
        old52 old52 (by bv_decide) rfl
    iexact H52
  have Hsize := iteratorSizeHintForward_call_twp (α := α)
    (frame + 44) iteratorPtr staticLow staticHigh old44 old48 old52
    hsizeRoom
    (callerLocals :=
      ⟨collectParams resultPtr iteratorPtr,
        [.i32 frame, .i64 first, .i32 0, .i32 0, .i32 0, .i32 0], []⟩)
    (stack := []) (code := collectCoreInnerBody.drop 15)
    (arity := arity) (remainder := remainder)
    (controls := collectCoreSomeControls controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil] at Hsize
  iapply Hsize
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [H44]
  · iexact H44
  isplitl [H48At]
  · iexact H48At
  isplitl [H52At]
  · iexact H52At
  isplitl [HstaticLow]
  · iexact HstaticLow
  isplitl [HstaticHigh]
  · iexact HstaticHigh
  iintro Hruntime H44 H48At H52At HstaticLow HstaticHigh
  ihave H48 : pointsTo_u32 (frame + 48) staticLow $$ [H48At]
  · iapply pointsTo_u32_congr ((frame + 44) + 4) (frame + 48)
        staticLow staticLow (by bv_decide) rfl
    iexact H48At
  ihave H52 : pointsTo_u32 (frame + 52) staticHigh $$ [H52At]
  · iapply pointsTo_u32_congr ((frame + 44) + 8) (frame + 52)
        staticHigh staticHigh (by bv_decide) rfl
    iexact H52At
  have Hcapacity := iteratorCollectCore_size_hint_to_capacity_branch_twp
    (α := α) resultPtr iteratorPtr frame first 0 old56 hframeRoom
    (code := [.br 1]) (arity := arity) (remainder := remainder)
    (controls := collectCoreSomeControls controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [collectCoreInnerBody, collectCoreBlock3Body,
    collectCoreBlock2Body, collectCoreBlock1Body, collectCoreOuterBody,
    leadingBlockBody, func10, List.drop, List.cons_append,
    List.nil_append] at Hcapacity ⊢
  iapply Hcapacity
  isplitl [H44]
  · iexact H44
  isplitl [H56]
  · iexact H56
  iintro H44 H56
  rw [show (0 : UInt32) + 1 = 1 by decide]
  iapply Hdone $$ Hruntime Hdiscriminant Hpayload H44 H48 H52 H56
    HstaticLow HstaticHigh

/-- Resolve the deterministic depth-two branch for lower hint zero, install
the minimum capacity four, exit to the allocation continuation, and prepare
the exact absolute-index-142 call arguments. -/
theorem iteratorCollectCore_capacity_branch_to_allocator_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr frame : UInt32) (first : UInt64)
    (oldCapacity : UInt32)
    (hframeRoom : frame.toNat + 60 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 (frame + 56) oldCapacity ∗
      (pointsTo_u32 (frame + 56) 4 -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 frame, .i64 first, .i32 1, .i32 4, .i32 8, .i32 0],
              [.i32 8, .i32 8, .i32 4, .i32 frame]⟩,
            .call 142 :: collectCoreOuterBody.drop 11,
            arity, remainder, collectCoreAllocationControls controls, calls⟩
            : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr,
          [.i32 frame, .i64 first, .i32 1, .i32 0, .i32 0, .i32 0],
          [.i32 (collectCapacityTooSmall 0)]⟩,
        [.br_if 2, .br 1], arity, remainder,
        collectCoreSomeControls controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hc0, hc1, hc2, hc3⟩ :=
    descriptorSlot32Facts frame 56 60 hframeRoom (by decide)
  have hflag : collectCapacityTooSmall 0 = 1 := by
    simp [collectCapacityTooSmall, collectInitialCapacity]
  iintro ⟨Hcapacity, Hdone⟩
  rw [hflag]
  simp only [collectCoreSomeControls, collectCoreAllocationControls,
    collectBlockFrame, collectCoreInnerBody, collectCoreBlock3Body,
    collectCoreBlock2Body, collectCoreBlock1Body, collectCoreOuterBody,
    leadingBlockBody, func10, List.drop]
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldCapacity hc0 hc1 hc2 hc3 $$ Hcapacity
  iintro Hcapacity
  iapply twp_exitControl rfl
  iapply twp_localGet rfl
  iapply twp_load32 4 hc0 hc1 hc2 hc3 $$ Hcapacity
  iintro Hcapacity
  iapply twp_localSet rfl
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [collectParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set, List.take_zero, List.nil_append]
  iapply Hdone $$ Hcapacity

/-- Build-clean nonempty func10 prefix from the returned first option all the
way to the allocation call.  Everything preceding absolute call 142 is now
composed; the remaining ownership-producing allocator core is explicit. -/
theorem iteratorCollectCore_after_first_next_some_to_allocator_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr frame : UInt32) (first : UInt64)
    (staticLow staticHigh old44 old48 old52 old56 : UInt32)
    (hframeRoom : frame.toNat + 60 ≤ UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u64 (frame + 24) 1 ∗ pointsTo_u64 (frame + 32) first ∗
      pointsTo_u32 (frame + 44) old44 ∗ pointsTo_u32 (frame + 48) old48 ∗
      pointsTo_u32 (frame + 52) old52 ∗ pointsTo_u32 (frame + 56) old56 ∗
      pointsTo_u32 1049096 staticLow ∗ pointsTo_u32 1049100 staticHigh ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u64 (frame + 24) 1 -∗ pointsTo_u64 (frame + 32) first -∗
        pointsTo_u32 (frame + 44) 0 -∗
        pointsTo_u32 (frame + 48) staticLow -∗
        pointsTo_u32 (frame + 52) staticHigh -∗
        pointsTo_u32 (frame + 56) 4 -∗
        pointsTo_u32 1049096 staticLow -∗ pointsTo_u32 1049100 staticHigh -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 frame, .i64 first, .i32 1, .i32 4, .i32 8, .i32 0],
              [.i32 8, .i32 8, .i32 4, .i32 frame]⟩,
            .call 142 :: collectCoreOuterBody.drop 11,
            arity, remainder, collectCoreAllocationControls controls, calls⟩
            : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr,
          [.i32 frame, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func10.drop 11, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hdiscriminant, Hpayload, H44, H48, H52, H56,
    HstaticLow, HstaticHigh, Hdone⟩
  iapply iteratorCollectCore_after_first_next_some_to_capacity_branch_twp
      resultPtr iteratorPtr frame first staticLow staticHigh
      old44 old48 old52 old56 hframeRoom
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hdiscriminant]
  · iexact Hdiscriminant
  isplitl [Hpayload]
  · iexact Hpayload
  isplitl [H44]
  · iexact H44
  isplitl [H48]
  · iexact H48
  isplitl [H52]
  · iexact H52
  isplitl [H56]
  · iexact H56
  isplitl [HstaticLow]
  · iexact HstaticLow
  isplitl [HstaticHigh]
  · iexact HstaticHigh
  iintro Hruntime Hdiscriminant Hpayload H44 H48 H52 H56
    HstaticLow HstaticHigh
  iapply iteratorCollectCore_capacity_branch_to_allocator_twp
      resultPtr iteratorPtr frame first (collectInitialCapacity 0) hframeRoom
  isplitl [H56]
  · iexact H56
  iintro H56
  iapply Hdone $$ Hruntime Hdiscriminant Hpayload H44 H48 H52 H56
    HstaticLow HstaticHigh

/-- Exact first boundary of local `func140`, the allocation wrapper called by
the collect core at absolute index 142.  It allocates its private 16-byte frame
and exposes the deeper absolute-index-146 allocator call. -/
theorem iteratorCollectAllocator_to_core_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count alignA alignB stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 count, .i32 alignA, .i32 alignB],
              [.i32 (stackTop - 16), .i32 0, .i32 0],
              [.i32 alignB, .i32 alignA, .i32 0, .i32 count,
                .i32 (stackTop - 16)]⟩,
            .call 146 :: func140.drop 14, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 count, .i32 alignA, .i32 alignB],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func140, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hdone⟩
  simp only [func140]
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
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  isimp only [func140, List.drop] at Hdone
  iapply Hdone $$ Hglobal

/-- Absolute-index-142/local-140 entry, preserving the caller while exposing
the exact absolute-index-146 allocation seam. -/
theorem iteratorCollectAllocator_call_to_core_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr count alignA alignB stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 count, .i32 alignA, .i32 alignB],
              [.i32 (stackTop - 16), .i32 0, .i32 0],
              [.i32 alignB, .i32 alignA, .i32 0, .i32 count,
                .i32 (stackTop - 16)]⟩,
            .call 146 :: func140.drop 14, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 alignB, .i32 alignA, .i32 count, .i32 resultPtr] ++ stack },
        .call 142 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 142 func140Def
      (by decide) iteratorCollectAllocator_index $$ Hruntime
  iintro Hruntime
  simp [func140Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply iteratorCollectAllocator_to_core_twp
      resultPtr count alignA alignB stackTop
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hdone $$ Hruntime Hglobal

/-- Exact first boundary of local `func1` (`Split::next`): allocate its
16-byte result frame and call the generated split-search implementation at
absolute index 86. -/
theorem splitNext_to_internal_next_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr stackTop : UInt32) {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 iteratorPtr],
              [.i32 (stackTop - 16), .i32 0],
              [.i32 iteratorPtr, .i32 ((stackTop - 16) + 8)]⟩,
            .call 86 :: func1.drop 11, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 iteratorPtr], [.i32 0, .i32 0], []⟩,
        func1, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hdone⟩
  simp only [func1]
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
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  rw [show (8 : UInt32) + (stackTop - 16) =
      (stackTop - 16) + 8 by bv_decide]
  isimp only [func1, List.drop] at Hdone
  iapply Hdone $$ Hglobal

/-- Absolute-index-3/local-1 entry, exposing the internal split-next call. -/
theorem splitNext_call_to_internal_next_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗ globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 iteratorPtr],
              [.i32 (stackTop - 16), .i32 0],
              [.i32 iteratorPtr, .i32 ((stackTop - 16) + 8)]⟩,
            .call 86 :: func1.drop 11, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 iteratorPtr, .i32 resultPtr] ++ stack },
        .call 3 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 3 func1Def
      (by decide) splitNext_index $$ Hruntime
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply splitNext_to_internal_next_twp resultPtr iteratorPtr stackTop
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hdone $$ Hruntime Hglobal

/-- Exact first boundary of local `func0` (`Map::next`): allocate its
16-byte frame and expose absolute call 3 to the split iterator. -/
theorem mapNext_to_split_next_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr stackTop : UInt32) {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 iteratorPtr],
              [.i32 (stackTop - 16), .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 iteratorPtr, .i32 (stackTop - 16)]⟩,
            .call 3 :: func0.drop 9, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 iteratorPtr],
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func0, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hdone⟩
  simp only [func0]
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
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  isimp only [func0, List.drop] at Hdone
  iapply Hdone $$ Hglobal

/-- Absolute-index-2/local-0 entry, exposing the split-next leaf. -/
theorem mapNext_call_to_split_next_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗ globalPointsTo 0 (.i32 (stackTop - 16)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 iteratorPtr],
              [.i32 (stackTop - 16), .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 iteratorPtr, .i32 (stackTop - 16)]⟩,
            .call 3 :: func0.drop 9, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 iteratorPtr, .i32 resultPtr] ++ stack },
        .call 2 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 2 func0Def
      (by decide) mapNext_index $$ Hruntime
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply mapNext_to_split_next_twp resultPtr iteratorPtr stackTop
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply Hdone $$ Hruntime Hglobal

/-- Exact first invariant boundary of local `func10`: allocate its 112-byte
collection frame and ask the map/split/parse iterator for the first element at
absolute call 2.  The option result occupies frame offsets 24 and 32. -/
theorem iteratorCollectCore_to_first_next_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr stackTop : UInt32) {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 112)) -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 (stackTop - 112), .i64 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 iteratorPtr, .i32 ((stackTop - 112) + 24)]⟩,
            .call 2 :: func10.drop 11, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨collectParams resultPtr iteratorPtr,
          [.i32 0, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func10, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hdone⟩
  simp only [func10]
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
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  simp only [collectParams, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  rw [show (24 : UInt32) + (stackTop - 112) =
      (stackTop - 112) + 24 by bv_decide]
  isimp only [func10, List.drop] at Hdone
  iapply Hdone $$ Hglobal

/-- Absolute-index-12/local-10 entry, exposing the exact first-next boundary
while preserving the local-124 and outer collect continuations. -/
theorem iteratorCollectCore_call_to_first_next_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr iteratorPtr stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗ globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 112)) -∗
        WP (.running
          ⟨⟨collectParams resultPtr iteratorPtr,
              [.i32 (stackTop - 112), .i64 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 iteratorPtr, .i32 ((stackTop - 112) + 24)]⟩,
            .call 2 :: func10.drop 11, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := [.i32 iteratorPtr, .i32 resultPtr] ++ stack },
        .call 12 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 12 func10Def
      (by decide) (by rfl) $$ Hruntime
  iintro Hruntime
  simp [func10Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hprefix := iteratorCollectCore_to_first_next_twp (α := α)
    resultPtr iteratorPtr stackTop
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [collectParams] at Hprefix
  iapply Hprefix
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  isimp only [collectParams] at Hdone
  iapply Hdone $$ Hruntime Hglobal

end Project.Mergesort.InputIteratorProof
