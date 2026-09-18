import Project.RustHashMap.PairGrow
import Project.RustHashMap.Func55Proof
import Project.RustHashMap.Func58Proof
import Project.RustHashMap.Func97Proof

/-!
# Proof of the generic `finish_grow` of the pair layer

This file proves local `func24` (absolute index 27) against `Func24Spec`.
The body is the one that `Project.RustHashMap.Func97Proof` proves at
absolute 100, with two extra guards in front:

* a 64-bit multiply of the element size by the new capacity, which rejects
  a product that does not fit in 32 bits;
* an unsigned test of that product against `0x80000000` minus the
  alignment.

`newLayout.Valid` excludes both arms.  It bounds the size by `UInt32.size`
and by `2147483648 - alignment`, and `Func24Spec` ties the size to the
product.

The null-pointer arm is dead as well, because `LiveBlock` carries a
non-null pointer.  The theorem is unconditional, because
`Project.RustHashMap.Func55Proof.func55_correct` and
`Project.RustHashMap.Func58Proof.func58_correct` are.
-/

namespace Project.RustHashMap.Func24Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

private theorem func24_index :
    Project.RustHashMap.«module».funcs[24]? =
      some Project.RustHashMap.func24Def := by rfl

/-! ## The two arithmetic guards -/

/-- The 64-bit widening of a 32-bit word keeps its value. -/
private theorem toNat_ofNat_u32 (w : UInt32) :
    (UInt64.ofNat w.toNat).toNat = w.toNat := by
  have hsize : (UInt64.size : Nat) = 2 ^ 64 := rfl
  have hlt : w.toNat < 2 ^ 32 := w.toBitVec.isLt
  exact UInt64.toNat_ofNat_of_lt (by omega)

/-- A product that fits in 32 bits keeps its value in 64 bits. -/
private theorem product_toNat (a b : UInt32) (size : Nat)
    (hsize : a.toNat * b.toNat = size) (hfit : size < 2 ^ 32) :
    (UInt64.ofNat a.toNat * UInt64.ofNat b.toNat).toNat = size := by
  rw [UInt64.toNat_mul, toNat_ofNat_u32, toNat_ofNat_u32, hsize]
  exact Nat.mod_eq_of_lt (by omega)

/-- The high word of the product is zero, so the overflow arm is dead. -/
private theorem high_word_zero (a b : UInt32) (size : Nat)
    (hsize : a.toNat * b.toNat = size) (hfit : size < 2 ^ 32) :
    (UInt64.ofNat a.toNat * UInt64.ofNat b.toNat) >>> (32 % 64) = 0 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, product_toNat a b size hsize hfit,
    show ((32 % 64 : UInt64).toNat % 64) = 32 from by decide,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hfit]
  rfl

/-- The low word of the product is the size itself. -/
private theorem low_word (a b : UInt32) (size : Nat)
    (hsize : a.toNat * b.toNat = size) (hfit : size < 2 ^ 32) :
    UInt32.ofNat ((UInt64.ofNat a.toNat * UInt64.ofNat b.toNat).toNat % 2 ^ 32)
      = UInt32.ofNat size := by
  rw [product_toNat a b size hsize hfit, Nat.mod_eq_of_lt hfit]

/-- The pure facts of a live block, without giving the block up. -/
private theorem LiveBlock_facts [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId : Nat) (ptr : UInt32)
    (layout : AllocLayout) (bytes : List UInt8) :
    LiveBlock heapId allocationId ptr layout bytes ⊢
      iprop(LiveBlock heapId allocationId ptr layout bytes ∗
        ⌜bytes.length = layout.size ∧ ptr ≠ 0⌝) := by
  iintro Hblock
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
  isplitl [Htoken Hbytes]
  · unfold LiveBlock
    iframe_pureexact using [Htoken Hbytes] => hfacts
  · ipureexact ⟨hfacts.1, hfacts.2.1⟩

/-! ## The shape of the emitted body -/

/-- The instructions after the outer block: the size word at the selected
offset, then the flag word at the result slot. -/
private def func24FinalCode : Program :=
  [.localGet 0, .localGet 7, .add, .localGet 3, .store32 0,
    .localGet 0, .localGet 6, .store32 0]

/-- The outer block body, taken from the emitted program. -/
private def func24OuterBody : Program :=
  match Project.RustHashMap.func24.drop 4 with
  | .block _ _ body :: _ => body
  | _ => []

/-- The third block of the outer body.  Its continuation stores the offset
`8` for the size word. -/
private def func24MiddleBody : Program :=
  match func24OuterBody.drop 2 with
  | .block _ _ body :: _ => body
  | _ => []

set_option maxHeartbeats 2000000 in
/-- The common normal-return tail after the allocator returned a non-null
pointer.  Local `7` holds the pointer.  The tail writes the pointer at
offset `4`, the size at offset `8`, and the flag `0` at offset `0`. -/
private theorem twp_func24_success_tail
    [WasmSmallStepGS hlc Universal.State]
    (result oldCapacity oldPtr newSize alignment elemSize newPtr finish :
      UInt32)
    (product : UInt64)
    (newBytes resultBefore : List UInt8)
    (heapId : GName) (newId : Nat)
    (oldLayout newLayout : AllocLayout) (source : FinishSource)
    (finalHistory : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (hresultLength : resultBefore.length = 12)
    (hresultNowrap : result.toNat + 12 < UInt32.size)
    (hcopied : finishCopied source oldLayout newBytes)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (middleBody outerBody : Program)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) :
    iprop(
      RuntimeContext ∗
      Slices.ByteSlice 0 result resultBefore ∗
      BumpHeap heapId finish finish.toNat finalHistory ∗
      LiveBlock heapId newId newPtr newLayout newBytes ∗
      Streams input output raised ∗
      (RuntimeContext -∗
        Slices.ByteSlice 0 result (finishResultBytes newPtr newSize) -∗
        BumpHeap heapId finish finish.toNat finalHistory -∗
        LiveBlock heapId newId newPtr newLayout newBytes -∗
        ⌜finishCopied source oldLayout newBytes⌝ -∗
        Streams input output raised -∗
        ResumeWP [] callerLocals stack code arity remainder controls calls
          s E Φ)) ⊢
      WP (.running
        ⟨{ params := [.i32 result, .i32 oldCapacity, .i32 oldPtr,
              .i32 newSize, .i32 alignment, .i32 elemSize],
            locals := [.i32 1, .i32 newPtr, .i64 product],
            values := [] },
          [.localGet 0, .localGet 7, .store32 4,
            .const 0, .localSet 6], 0, [],
          { kind := .block, paramArity := 0, resultArity := 0,
            body := middleBody,
            continuation := [.const 8, .localSet 7],
            belowStack := [] } ::
          { kind := .block, paramArity := 0, resultArity := 0,
            body := outerBody, continuation := func24FinalCode,
            belowStack := [] } :: [],
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hresult, Hbump, Hblock, Hstreams, Hcont⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  ihave Hfocus := Project.RustHashMap.Func97Proof.ByteSlice_twelve_storeFocus
    result resultBefore hresultLength $$ Hresult
  icases Hfocus with
    ⟨%oldTag, %oldResultPtr, %oldResultSize,
      Htag, Hpointer, Hsize, Hclose⟩
  have hresult4 : (result + 4).toNat = result.toNat + 4 := by
    simpa using Slices.byteOffset_toNat result 4 (by omega)
  have hresult8 : (result + 8).toNat = result.toNat + 8 := by
    simpa using Slices.byteOffset_toNat result 8 (by omega)
  have h4_1 : ((result + 4) + 1).toNat = (result + 4).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (result + 4) 1 (by omega)
  have h4_2 : ((result + 4) + 2).toNat = (result + 4).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (result + 4) 2 (by omega)
  have h4_3 : ((result + 4) + 3).toNat = (result + 4).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (result + 4) 3 (by omega)
  have h8_1 : ((result + 8) + 1).toNat = (result + 8).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (result + 8) 1 (by omega)
  have h8_2 : ((result + 8) + 2).toNat = (result + 8).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (result + 8) 2 (by omega)
  have h8_3 : ((result + 8) + 3).toNat = (result + 8).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (result + 8) 3 (by omega)
  have h0_1 : (result + 1).toNat = result.toNat + 1 := by
    simpa using Slices.byteOffset_toNat result 1 (by omega)
  have h0_2 : (result + 2).toNat = result.toNat + 2 := by
    simpa using Slices.byteOffset_toNat result 2 (by omega)
  have h0_3 : (result + 3).toNat = result.toNat + 3 := by
    simpa using Slices.byteOffset_toNat result 3 (by omega)
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := result) (offset := 4) oldResultPtr
      hresult4 h4_1 h4_2 h4_3 with Hpointer
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length, List.set]
  wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length, List.set]
  wasm_twp_pures [twp_exitControl] using [func24FinalCode, List.take_zero,
    List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_add twp_localGet]
  have hresult8Comm : 8 + result = result + 8 := by
    ac_rfl
  ihave Hsize' : pointsTo_u32 0 (8 + result + 0)
      oldResultSize $$ [Hsize]
  · irw_exact [show 8 + result + 0 = result + 8 by simp [hresult8Comm]] with
      Hsize
  iapply twp_store32 (address := 8 + result) (offset := 0)
      oldResultSize
      (by simp)
      (by simpa [hresult8Comm] using h8_1)
      (by simpa [hresult8Comm] using h8_2)
      (by simpa [hresult8Comm] using h8_3) $$ Hsize'
  iintro Hsize
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Htag' : pointsTo_u32 0 (result + 0) oldTag $$ [Htag]
  · irw_exact [show result + 0 = result by simp] with Htag
  iapply twp_store32 (address := result) (offset := 0) oldTag
      (by simp) (by simpa using h0_1) (by simpa using h0_2)
      (by simpa using h0_3) $$ Htag'
  iintro Htag
  isimp only [UInt32.add_zero] at Htag
  isimp only [UInt32.add_zero, hresult8Comm] at Hsize
  wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  ihave Hresult := Hclose $$ Htag Hpointer Hsize
  isimp only [finishResultBytes] at Hcont
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hcont
  iclose_map_runtime Hruntime with Hmodule Henv
  iapply Hcont $$ Hruntime Hresult Hbump Hblock %hcopied Hstreams

set_option maxHeartbeats 2000000 in
/-- The generic `finish_grow`.  Both arithmetic guards and the null-pointer
arm are dead under `Func24Spec`. -/
theorem func24_correct [WasmSmallStepGS hlc Universal.State] :
    Func24Spec (hlc := hlc) := by
  unfold Func24Spec CallContract callExpr
  intro result oldCapacity oldPtr newCapacity alignment elemSize oldLayout
    newLayout source resultBefore heapId storedCursor frontier history input
    output raised callerLocals stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hresult, Hsource, Hbump, Hstreams, %hfacts, Hcont⟩
  rcases hfacts with ⟨hresultLength, hresultNowrap, holdSize, hnewSize,
    holdAlign, hnewAlign, halignChoice, hnewValid, holdNew⟩
  have hsize32 : (UInt32.size : Nat) = 2 ^ 32 := rfl
  have hnewFit : newLayout.size < 2 ^ 32 := by
    have hbound := hnewValid.2.2.2.2.2.1
    omega
  have hnewSizeNat :
      (UInt32.ofNat newLayout.size).toNat = newLayout.size :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hnewMatches :
      newLayout.Matches (UInt32.ofNat newLayout.size) alignment :=
    ⟨hnewSizeNat, hnewAlign.symm⟩
  have hnewSizeNonzero : UInt32.ofNat newLayout.size ≠ 0 := by
    intro hzero
    have hzeroNat := congrArg UInt32.toNat hzero
    rw [hnewSizeNat] at hzeroNat
    simp only [UInt32.toNat_zero] at hzeroNat
    have hpositive := hnewValid.1
    omega
  have halignLiteral : (2147483648 : UInt32).toNat = 2147483648 := rfl
  have halignLe : alignment ≤ 2147483648 :=
    UInt32.le_iff_toNat_le.mpr (by rw [halignLiteral]; rcases halignChoice with
      h | h <;> omega)
  have hsubNat :
      ((2147483648 : UInt32) - alignment).toNat = 2147483648 - alignment.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ halignLe, halignLiteral]
  have hleGuard :
      UInt32.ofNat newLayout.size ≤ (2147483648 : UInt32) - alignment := by
    apply UInt32.le_iff_toNat_le.mpr
    rw [hsubNat, hnewSizeNat, ← hnewAlign]
    exact hnewValid.2.2.2.2.1
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 27
      Project.RustHashMap.func24Def (by decide) func24_index with Hmodule
  simp [Project.RustHashMap.func24Def, Project.RustHashMap.func24,
    Function.toLocals, Function.numParams]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_extendUI32
    twp_localGet twp_extendUI32 twp_mulI64]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_constI64 twp_shrUI64 twp_wrapI64]
  simp only [high_word_zero elemSize newCapacity newLayout.size hnewSize.symm
      hnewFit,
    show UInt32.ofNat ((0 : UInt64).toNat % 2 ^ 32) = 0 from rfl]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_block twp_localGet twp_wrapI64]
  simp only [low_word elemSize newCapacity newLayout.size hnewSize.symm hnewFit]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_localGet twp_sub]
  iapply twp_leU (result := 1) (by rw [if_pos hleGuard])
  iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_block twp_block twp_block twp_block]
  have halignNewChoice :
      newLayout.alignment = 1 ∨ newLayout.alignment = 4 := by
    rw [hnewAlign]; exact halignChoice
  cases source with
  | empty =>
      isimp only [FinishSourceOwn] at Hsource
      icases Hsource with %hsource
      subst hsource
      wasm_twp_pures [twp_localGet twp_eqz]
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      wasm_twp_pures [twp_block twp_localGet]
      iapply twp_brIf hnewSizeNonzero (by rfl)
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      have Hmark : Func30Spec (hlc := hlc) :=
        Project.RustHashMap.Func30Proof.func30_correct
      unfold Func30Spec CallContract callExpr at Hmark
      simp only [List.nil_append] at Hmark
      iapply Hmark
        (callerLocals :=
          { params := [.i32 result, .i32 0, .i32 oldPtr,
              .i32 (UInt32.ofNat newLayout.size), .i32 alignment,
              .i32 elemSize]
            locals := [.i32 1, .i32 4,
              .i64 (UInt64.ofNat elemSize.toNat * UInt64.ofNat newCapacity.toNat)]
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      · unfold ResumeWP resumeExpr
        simp only [List.nil_append]
        iintro Hruntime
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        wasm_twp_pures [twp_localGet twp_localGet]
        have Halloc : Func55Spec (hlc := hlc) :=
          Project.RustHashMap.Func55Proof.func55_correct
        unfold Func55Spec CallContract callExpr at Halloc
        simp only [List.cons_append, List.nil_append] at Halloc
        iapply Halloc (size := UInt32.ofNat newLayout.size)
          (alignment := alignment) (layout := newLayout) (heapId := heapId)
          (storedCursor := storedCursor) (frontier := frontier)
          (history := history) (input := input) (output := output)
          (raised := raised)
          (callerLocals :=
            { params := [.i32 result, .i32 0, .i32 oldPtr,
                .i32 (UInt32.ofNat newLayout.size), .i32 alignment,
                .i32 elemSize]
              locals := [.i32 1, .i32 4,
                .i64 (UInt64.ofNat elemSize.toNat *
                  UInt64.ofNat newCapacity.toNat)]
              values := [] })
          (stack := [])
        isplitl [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isplitl_exacts [Hbump Hstreams]
        isplitl_pureexact ⟨hnewMatches, hnewValid, halignNewChoice⟩
        cases hdecision : classifyBump frontier newLayout with
        | oom =>
            isimp only [AllocContinuation, hdecision,
              FinishContinuation] at Hcont
            isimp only [AllocContinuation, hdecision, FinishContinuation]
            iintro Hbump Hstreams
            ihave Hsource : FinishSourceOwn heapId 0 oldPtr oldLayout
                .empty $$ []
            · unfold FinishSourceOwn
              ipureexact rfl
            iapply Hcont $$ Hresult Hsource Hbump Hstreams
        | success newPtr finish =>
            isimp only [AllocContinuation, hdecision,
              FinishContinuation] at Hcont
            isimp only [AllocContinuation, hdecision, FinishContinuation]
            isplit
            · iintro %newBytes Hruntime Hbump Hblock Hstreams
              isimp only [ResumeWP, resumeExpr, List.nil_append,
                List.append_nil]
              wasm_twp_localSet [List.length_cons, List.length_nil,
                Nat.reduceAdd, Nat.reduceSub, List.set]
              wasm_twp_pures [twp_exitControl] using [List.take_zero,
                List.nil_append]
              ihave ⟨Hblock, %hnewFacts⟩ := LiveBlock_facts heapId
                history.nextId newPtr newLayout newBytes $$ Hblock
              wasm_twp_pures [twp_localGet]
              iapply twp_brIf hnewFacts.2 (by rfl)
              simp only [List.take_zero, List.nil_append]
              ihave Hnormal := BI.and_elim_l $$ Hcont
              ihave Hnormal := Hnormal $$ %newBytes
              have Htail := twp_func24_success_tail
                  (result := result) (oldCapacity := 0) (oldPtr := oldPtr)
                  (newSize := UInt32.ofNat newLayout.size)
                  (alignment := alignment) (elemSize := elemSize)
                  (newPtr := newPtr) (finish := finish)
                  (product :=
                    UInt64.ofNat elemSize.toNat * UInt64.ofNat newCapacity.toNat)
                  (newBytes := newBytes) (resultBefore := resultBefore)
                  (heapId := heapId) (newId := history.nextId)
                  (oldLayout := oldLayout) (newLayout := newLayout)
                  (source := FinishSource.empty)
                  (finalHistory := history.allocate newPtr newLayout)
                  (input := input) (output := output) (raised := raised)
                  (callerLocals := callerLocals) (stack := stack)
                  (code := code) (arity := arity) (remainder := remainder)
                  (controls := controls) (calls := calls)
                  (middleBody := func24MiddleBody)
                  (outerBody := func24OuterBody)
                  (s := s) (E := E) (Φ := Φ)
                  hresultLength hresultNowrap (by simp [finishCopied])
              simp only [func24MiddleBody, func24OuterBody, func24FinalCode,
                Project.RustHashMap.func24, List.drop] at Htail
              iapply Htail
              isimp only [finishHistory] at Hnormal
              isplitl_exacts [Hruntime Hresult Hbump Hblock Hstreams]
              · iexact Hnormal
            · iintro Hbump Hstreams
              ihave Hoom := BI.and_elim_r $$ Hcont
              ihave Hsource : FinishSourceOwn heapId 0 oldPtr oldLayout
                  .empty $$ []
              · unfold FinishSourceOwn
                ipureexact rfl
              iapply Hoom $$ Hresult Hsource Hbump Hstreams
  | allocated oldId allBytes =>
      isimp only [FinishSourceOwn] at Hsource
      icases Hsource with ⟨%hsource, Hblock⟩
      have holdPositive : 0 < oldCapacity.toNat := hsource.1
      have holdValid : oldLayout.Valid := hsource.2
      have holdFit : oldLayout.size < 2 ^ 32 := by
        have hbound := holdValid.2.2.2.2.2.1
        omega
      have holdNonzero : oldCapacity ≠ 0 := by
        intro hzero
        have hzeroNat := congrArg UInt32.toNat hzero
        simp only [UInt32.toNat_zero] at hzeroNat
        omega
      have holdSizeNat : (oldCapacity * elemSize).toNat = oldLayout.size := by
        rw [UInt32.toNat_mul, holdSize, Nat.mul_comm]
        exact Nat.mod_eq_of_lt (by omega)
      have holdMatches : oldLayout.Matches (oldCapacity * elemSize) alignment :=
        ⟨holdSizeNat, holdAlign.symm⟩
      have holdAlignChoice :
          oldLayout.alignment = 1 ∨ oldLayout.alignment = 4 := by
        rw [holdAlign]; exact halignChoice
      ihave ⟨Hblock, %hblockFacts⟩ :=
        LiveBlock_facts heapId oldId oldPtr oldLayout allBytes $$ Hblock
      wasm_twp_pures [twp_localGet]
      iapply twp_eqz (by rw [if_neg holdNonzero])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet
        twp_mul twp_localGet twp_localGet]
      have Hrealloc : Func58Spec (hlc := hlc) :=
        Project.RustHashMap.Func58Proof.func58_correct
      unfold Func58Spec CallContract callExpr at Hrealloc
      simp only [List.cons_append, List.nil_append] at Hrealloc
      iapply Hrealloc (oldPtr := oldPtr) (oldSize := oldCapacity * elemSize)
        (alignment := alignment) (newSize := UInt32.ofNat newLayout.size)
        (oldLayout := oldLayout) (newLayout := newLayout) (heapId := heapId)
        (oldId := oldId) (oldBytes := allBytes)
        (storedCursor := storedCursor) (frontier := frontier)
        (history := history) (input := input) (output := output)
        (raised := raised)
        (callerLocals :=
          { params := [.i32 result, .i32 oldCapacity, .i32 oldPtr,
              .i32 (UInt32.ofNat newLayout.size), .i32 alignment,
              .i32 elemSize]
            locals := [.i32 1, .i32 4,
              .i64 (UInt64.ofNat elemSize.toNat * UInt64.ofNat newCapacity.toNat)]
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      isplitl_exacts [Hbump Hblock Hstreams]
      isplitl_pureexact ⟨holdMatches, hnewMatches, holdValid, hnewValid,
          holdAlignChoice, holdNew⟩
      cases hdecision : classifyBump frontier newLayout with
      | oom =>
          isimp only [ReallocContinuation, hdecision,
            FinishContinuation] at Hcont
          isimp only [ReallocContinuation, hdecision, FinishContinuation]
          iintro Hbump Hblock Hstreams
          ihave Hsource : FinishSourceOwn heapId oldCapacity oldPtr oldLayout
              (.allocated oldId allBytes) $$ [Hblock]
          · unfold FinishSourceOwn
            isplitr_pureexact hsource
            · iexact Hblock
          iapply Hcont $$ Hresult Hsource Hbump Hstreams
      | success newPtr finish =>
          isimp only [ReallocContinuation, hdecision,
            FinishContinuation] at Hcont
          isimp only [ReallocContinuation, hdecision, FinishContinuation]
          isplit
          · iintro %newBytes Hruntime Hbump Hblock %hcopy Hstreams
            rw [min_eq_left (Nat.le_of_lt holdNew)] at hcopy
            rw [(List.take_eq_self_iff allBytes).mpr
              (Nat.le_of_eq hblockFacts.1)] at hcopy
            isimp only [ResumeWP, resumeExpr, List.nil_append, List.append_nil]
            wasm_twp_localSet [List.length_cons, List.length_nil,
              Nat.reduceAdd, Nat.reduceSub, List.set]
            wasm_twp_pures [twp_br] using [List.take_zero, List.nil_append]
            ihave ⟨Hblock, %hnewFacts⟩ := LiveBlock_facts heapId
              history.nextId newPtr newLayout newBytes $$ Hblock
            wasm_twp_pures [twp_localGet]
            iapply twp_brIf hnewFacts.2 (by rfl)
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            ihave Hnormal := BI.and_elim_l $$ Hcont
            ihave Hnormal := Hnormal $$ %newBytes
            have Htail := twp_func24_success_tail
                (result := result) (oldCapacity := oldCapacity)
                (oldPtr := oldPtr)
                (newSize := UInt32.ofNat newLayout.size)
                (alignment := alignment) (elemSize := elemSize)
                (newPtr := newPtr) (finish := finish)
                (product :=
                  UInt64.ofNat elemSize.toNat * UInt64.ofNat newCapacity.toNat)
                (newBytes := newBytes) (resultBefore := resultBefore)
                (heapId := heapId) (newId := history.nextId)
                (oldLayout := oldLayout) (newLayout := newLayout)
                (source := FinishSource.allocated oldId allBytes)
                (finalHistory :=
                  history.reallocate oldId oldPtr oldLayout newPtr newLayout)
                (input := input) (output := output) (raised := raised)
                (callerLocals := callerLocals) (stack := stack)
                (code := code) (arity := arity) (remainder := remainder)
                (controls := controls) (calls := calls)
                (middleBody := func24MiddleBody)
                (outerBody := func24OuterBody)
                (s := s) (E := E) (Φ := Φ)
                hresultLength hresultNowrap hcopy
            simp only [func24MiddleBody, func24OuterBody, func24FinalCode,
              Project.RustHashMap.func24, List.drop] at Htail
            iapply Htail
            isimp only [finishHistory] at Hnormal
            isplitl_exacts [Hruntime Hresult Hbump Hblock Hstreams]
            · iexact Hnormal
          · iintro Hbump Hblock Hstreams
            ihave Hoom := BI.and_elim_r $$ Hcont
            ihave Hsource : FinishSourceOwn heapId oldCapacity oldPtr oldLayout
                (.allocated oldId allBytes) $$ [Hblock]
            · unfold FinishSourceOwn
              isplitr_pureexact hsource
              · iexact Hblock
            iapply Hoom $$ Hresult Hsource Hbump Hstreams

end Project.RustHashMap.Func24Proof
