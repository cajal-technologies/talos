import Project.Mergesort.ContractProofs

/-!
# Proof of the generated RawVec grow wrapper

This file proves local `func0` (absolute Wasm index 3) from the two allocator
contracts that cover its valid-input branches.  The compiler-generated
capacity-overflow branches are excluded at their originating arithmetic
guards by `Func0Spec`'s valid-layout hypotheses.
-/

namespace Project.Mergesort.Func0Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

private theorem func0_index :
    Project.Mergesort.module.funcs[0]? =
      some Project.Mergesort.func0Def := by
  rfl

private def func0Locals
    (result oldCapacity oldPtr newCapacity alignment elementSize tag pointer : UInt32)
    (product : UInt64) (values : List Value := []) : Locals :=
  { params := [.i32 result, .i32 oldCapacity, .i32 oldPtr,
      .i32 newCapacity, .i32 alignment, .i32 elementSize]
    locals := [.i32 tag, .i32 pointer, .i64 product]
    values := values }

/-- A four-byte slice may be overwritten by any word, with ownership returned
in the canonical serialized form. -/
private theorem ByteSlice_storeAnyWordFocus
    [WasmSmallStepGS hlc Universal.State]
    (ptr : UInt32) (oldBytes : List UInt8)
    (hlength : oldBytes.length = 4)
    (hnowrap : ptr.toNat + 4 < UInt32.size) :
    Representations.ByteSlice ptr oldBytes ⊢
      iprop(pointsTo_u32 0 ptr (Spec.decodeWord oldBytes) ∗
        (∀ newValue : UInt32, pointsTo_u32 0 ptr newValue -∗
          Representations.ByteSlice ptr (serialize [newValue]))) := by
  iintro Hslice
  ihave Hold := (ByteSlice_four_as_word ptr oldBytes hlength hnowrap).mp $$
    Hslice
  isplitl_exact Hold
  · iintro %newValue
    iintro Hnew
    have hnewLength : (serialize [newValue]).length = 4 := by
      rw [serialize_length]
      norm_num
    have hdecode : Spec.decodeWord (serialize [newValue]) = newValue := by
      change Spec.decodeWord (Spec.encodeWord newValue) = newValue
      exact Spec.u32Codec.decode_encode newValue
    iapply (ByteSlice_four_as_word ptr (serialize [newValue])
      hnewLength hnowrap).mpr
    rw [hdecode]
    iexact Hnew

/-- Expose an arbitrary twelve-byte result slot as three writable words, with
an exact close operation for the generated grow result.  No alignment premise
is needed: Wasm's scalar loads/stores are valid at unaligned addresses. -/
private theorem ByteSlice_twelve_storeFocus
    [WasmSmallStepGS hlc Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (hlength : bytes.length = 12) :
    Representations.ByteSlice ptr bytes ⊢
      iprop(∃ oldTag oldPtr oldCapacity : UInt32,
        pointsTo_u32 0 ptr oldTag ∗
        pointsTo_u32 0 (ptr + 4) oldPtr ∗
        pointsTo_u32 0 (ptr + 8) oldCapacity ∗
        (∀ tag : UInt32, ∀ pointer : UInt32, ∀ capacity : UInt32,
          pointsTo_u32 0 ptr tag -∗
          pointsTo_u32 0 (ptr + 4) pointer -∗
          pointsTo_u32 0 (ptr + 8) capacity -∗
          Representations.ByteSlice ptr
            (serialize [tag, pointer, capacity]))) := by
  iintro Hbytes
  isimp only [Representations.ByteSlice] at Hbytes
  icases Hbytes with ⟨%hnowrap, HrawBytes⟩
  ihave Hbytes : Representations.ByteSlice ptr bytes $$ [HrawBytes]
  · unfold Representations.ByteSlice
    iframe HrawBytes
    ipureexact hnowrap
  let first := bytes.take 4
  let rest := bytes.drop 4
  let second := rest.take 4
  let third := rest.drop 4
  have hfirstRest : bytes = first ++ rest := by
    dsimp only [first, rest]
    exact (List.take_append_drop 4 bytes).symm
  have hsecondThird : rest = second ++ third := by
    dsimp only [second, third]
    exact (List.take_append_drop 4 rest).symm
  have hfirstLength : first.length = 4 := by
    simp [first, hlength]
  have hrestLength : rest.length = 8 := by
    simp [rest, hlength]
  have hsecondLength : second.length = 4 := by
    simp [second, hrestLength]
  have hthirdLength : third.length = 4 := by
    simp [third, hrestLength]
  ihave Hsplit : Representations.ByteSlice ptr (first ++ rest) $$ [Hbytes]
  · rw [← hfirstRest]
    iexact Hbytes
  icases (ByteSlice_append ptr first rest).mp $$ Hsplit with
    ⟨Hfirst, Hrest⟩
  have hfirstAddress : ptr + UInt32.ofNat first.length = ptr + 4 := by
    simp [hfirstLength]
  ihave HrestAt4 : Representations.ByteSlice (ptr + 4) rest $$ [Hrest]
  · rw [← hfirstAddress]
    iexact Hrest
  ihave Hrest' : Representations.ByteSlice (ptr + 4)
      (second ++ third) $$ [HrestAt4]
  · rw [← hsecondThird]
    iexact HrestAt4
  icases (ByteSlice_append (ptr + 4) second third).mp $$ Hrest' with
    ⟨Hsecond, Hthird⟩
  have hfirstNowrap : ptr.toNat + 4 < UInt32.size := by omega
  have hptr4Nat : (ptr + 4).toNat = ptr.toNat + 4 := by
    simpa using byteOffset_toNat ptr 4 hfirstNowrap
  have hsecondNowrap : (ptr + 4).toNat + 4 < UInt32.size := by
    rw [hptr4Nat]
    omega
  have hptr8 : (ptr + 4) + 4 = ptr + 8 := by bv_decide
  have hthirdNowrap : (ptr + 8).toNat + 4 < UInt32.size := by
    have hptr8Nat : (ptr + 8).toNat = ptr.toNat + 8 := by
      simpa using byteOffset_toNat ptr 8 (by omega)
    rw [hptr8Nat]
    omega
  ihave HfirstFocus := ByteSlice_storeAnyWordFocus ptr first
    hfirstLength hfirstNowrap $$ Hfirst
  icases HfirstFocus with ⟨Hfirst, HcloseFirst⟩
  ihave HsecondFocus := ByteSlice_storeAnyWordFocus (ptr + 4) second
    hsecondLength hsecondNowrap $$ Hsecond
  icases HsecondFocus with ⟨Hsecond, HcloseSecond⟩
  have hthirdAddress :
      ptr + 4 + UInt32.ofNat second.length = ptr + 8 := by
    simp [hsecondLength, hptr8]
  ihave Hthird' : Representations.ByteSlice (ptr + 8) third $$ [Hthird]
  · rw [← hthirdAddress]
    iexact Hthird
  ihave HthirdFocus := ByteSlice_storeAnyWordFocus (ptr + 8) third
    hthirdLength hthirdNowrap $$ Hthird'
  icases HthirdFocus with ⟨Hthird, HcloseThird⟩
  iexists Spec.decodeWord first, Spec.decodeWord second,
    Spec.decodeWord third
  iframe Hfirst Hsecond Hthird
  iintro %tag
  iintro %pointer
  iintro %capacity
  iintro Htag
  iintro Hpointer
  iintro Hcapacity
  ihave Htag := HcloseFirst $$ Htag
  ihave Hpointer := HcloseSecond $$ Hpointer
  ihave Hcapacity := HcloseThird $$ Hcapacity
  ihave Hhead : Representations.ByteSlice ptr
      (serialize [tag] ++ serialize [pointer]) $$ [Htag Hpointer]
  · iapply (ByteSlice_append ptr (serialize [tag])
      (serialize [pointer])).mpr
    isplitl_exact Htag
    · have hpointerAddress :
          ptr + UInt32.ofNat (serialize [tag]).length = ptr + 4 := by
        have htagLength : (serialize [tag]).length = 4 := by
          rw [serialize_length]
          norm_num
        rw [htagLength,
          show UInt32.ofNat 4 = (4 : UInt32) by decide]
      ihave Hpointer' : Representations.ByteSlice
          (ptr + UInt32.ofNat (serialize [tag]).length)
          (serialize [pointer]) $$ [Hpointer]
      · rw [hpointerAddress]
        iexact Hpointer
      iexact Hpointer'
  ihave Hall : Representations.ByteSlice ptr
      ((serialize [tag] ++ serialize [pointer]) ++ serialize [capacity]) $$
      [Hhead Hcapacity]
  · iapply (ByteSlice_append ptr
      (serialize [tag] ++ serialize [pointer])
      (serialize [capacity])).mpr
    isplitl_exact Hhead
    · have hcapacityAddress : ptr + UInt32.ofNat
            (serialize [tag] ++ serialize [pointer]).length = ptr + 8 := by
        have hpairLength :
            (serialize [tag] ++ serialize [pointer]).length = 8 := by
          rw [List.length_append, serialize_length, serialize_length]
          norm_num
        rw [hpairLength,
          show UInt32.ofNat 8 = (8 : UInt32) by decide]
      ihave Hcapacity' : Representations.ByteSlice
          (ptr + UInt32.ofNat
            (serialize [tag] ++ serialize [pointer]).length)
          (serialize [capacity]) $$ [Hcapacity]
      · rw [hcapacityAddress]
        iexact Hcapacity
      iexact Hcapacity'
  rw [show serialize [tag, pointer, capacity] =
      (serialize [tag] ++ serialize [pointer]) ++ serialize [capacity] by
    simp [serialize, Wasm.WordCodec.serialize_cons]]
  iexact Hall

private def func0FinalCode : Program :=
  [.localGet 0, .localGet 7, .add, .localGet 3, .store32 0,
    .localGet 0, .localGet 6, .store32 0]

/-- The outer generated block body, extracted from the authoritative emitted
program so the common return-tail lemma does not duplicate its dead code. -/
private def func0OuterBody : Program :=
  match Project.Mergesort.func0.drop 4 with
  | .block _ _ body :: _ => body
  | _ => []

/-- The third nested block in `func0OuterBody`, whose continuation is the
successful result writeback. -/
private def func0MiddleBody : Program :=
  match func0OuterBody.drop 2 with
  | .block _ _ body :: _ => body
  | _ => []

private theorem LiveBlock_with_nonnull
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId : Nat) (ptr : UInt32)
    (layout : AllocLayout) (bytes : List UInt8) :
    LiveBlock heapId allocationId ptr layout bytes ⊢
      iprop(LiveBlock heapId allocationId ptr layout bytes ∗ ⌜ptr ≠ 0⌝) := by
  iintro Hblock
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
  isplitl [Htoken Hbytes]
  · unfold LiveBlock
    iframe Htoken Hbytes
    ipureexact hfacts
  · ipureintro
    exact hfacts.2.1

/-- Common normal-return tail after either the first allocation or a
reallocation has produced a non-null pointer. -/
private theorem twp_func0_success_tail
    [WasmSmallStepGS hlc Universal.State]
    (result oldCapacity oldPtr newCapacity newPtr finish : UInt32)
    (product : UInt64) (newBytes growBefore initialized : List UInt8)
    (heapId : GName) (newId : Nat) (finalHistory : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (hresultLength : growBefore.length = 12)
    (hresultNowrap : result.toNat + growBefore.length < UInt32.size)
    (_hnewPtr : newPtr ≠ 0)
    (hcopied : growCopied source oldCapacity newBytes ∧
      newBytes.take initialized.length = initialized)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (middleBody outerBody : Program)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) :
    iprop(
      RuntimeContext ∗
      ByteSlice result growBefore ∗
      BumpHeap heapId finish finish.toNat finalHistory ∗
      LiveBlock heapId newId newPtr
        { size := newCapacity.toNat, alignment := 1 } newBytes ∗
      Streams input output raised ∗
      (RuntimeContext -∗
        ByteSlice result (growResultBytes newPtr newCapacity) -∗
        BumpHeap heapId finish finish.toNat finalHistory -∗
        LiveBlock heapId newId newPtr
          { size := newCapacity.toNat, alignment := 1 } newBytes -∗
        ⌜growCopied source oldCapacity newBytes ∧
          newBytes.take initialized.length = initialized⌝ -∗
        Streams input output raised -∗
        ResumeWP [] callerLocals stack code arity remainder controls calls
          s E Φ)) ⊢
      WP (.running
        ⟨{ params := [.i32 result, .i32 oldCapacity, .i32 oldPtr,
              .i32 newCapacity, .i32 1, .i32 1],
            locals := [.i32 1, .i32 newPtr, .i64 product],
            values := [] },
          [.localGet 0, .localGet 7, .store32 4,
            .const 0, .localSet 6], 0, [],
          { kind := .block, paramArity := 0, resultArity := 0,
            body := middleBody,
            continuation := [.const 8, .localSet 7],
            belowStack := [] } ::
          { kind := .block, paramArity := 0, resultArity := 0,
            body := outerBody, continuation := func0FinalCode,
            belowStack := [] } :: [],
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hresult, Hbump, Hblock, Hstreams, Hcont⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  ihave Hfocus := ByteSlice_twelve_storeFocus result growBefore
    hresultLength $$ Hresult
  icases Hfocus with
    ⟨%oldTag, %oldResultPtr, %oldResultCapacity,
      Htag, Hpointer, Hcapacity, Hclose⟩
  have hresult4 : (result + 4).toNat = result.toNat + 4 := by
    apply byteOffset_toNat result 4
    rw [hresultLength] at hresultNowrap
    omega
  have hresult8 : (result + 8).toNat = result.toNat + 8 := by
    apply byteOffset_toNat result 8
    rw [hresultLength] at hresultNowrap
    omega
  have h4_1 : ((result + 4) + 1).toNat = (result + 4).toNat + 1 := by
    apply byteOffset_toNat (result + 4) 1
    rw [hresult4]
    rw [hresultLength] at hresultNowrap
    omega
  have h4_2 : ((result + 4) + 2).toNat = (result + 4).toNat + 2 := by
    apply byteOffset_toNat (result + 4) 2
    rw [hresult4]
    rw [hresultLength] at hresultNowrap
    omega
  have h4_3 : ((result + 4) + 3).toNat = (result + 4).toNat + 3 := by
    apply byteOffset_toNat (result + 4) 3
    rw [hresult4]
    rw [hresultLength] at hresultNowrap
    omega
  have h8_1 : ((result + 8) + 1).toNat = (result + 8).toNat + 1 := by
    apply byteOffset_toNat (result + 8) 1
    rw [hresult8]
    rw [hresultLength] at hresultNowrap
    omega
  have h8_2 : ((result + 8) + 2).toNat = (result + 8).toNat + 2 := by
    apply byteOffset_toNat (result + 8) 2
    rw [hresult8]
    rw [hresultLength] at hresultNowrap
    omega
  have h8_3 : ((result + 8) + 3).toNat = (result + 8).toNat + 3 := by
    apply byteOffset_toNat (result + 8) 3
    rw [hresult8]
    rw [hresultLength] at hresultNowrap
    omega
  have h0_1 : (result + 1).toNat = result.toNat + 1 := by
    apply byteOffset_toNat result 1
    rw [hresultLength] at hresultNowrap
    omega
  have h0_2 : (result + 2).toNat = result.toNat + 2 := by
    apply byteOffset_toNat result 2
    rw [hresultLength] at hresultNowrap
    omega
  have h0_3 : (result + 3).toNat = result.toNat + 3 := by
    apply byteOffset_toNat result 3
    rw [hresultLength] at hresultNowrap
    omega
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_store32 (address := result) (offset := 4) oldResultPtr
      hresult4 h4_1 h4_2 h4_3 $$ Hpointer
  iintro Hpointer
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length]
  wasm_twp_pures [twp_exitControl]
  simp only [List.take_zero, List.nil_append]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length]
  wasm_twp_pures [twp_exitControl]
  simp only [func0FinalCode, List.take_zero, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_add twp_localGet]
  have hresult8Comm : 8 + result = result + 8 := by
    ac_rfl
  ihave Hcapacity' : pointsTo_u32 0 (8 + result + 0)
      oldResultCapacity $$ [Hcapacity]
  · rw [show 8 + result + 0 = result + 8 by simp [hresult8Comm]]
    iexact Hcapacity
  iapply twp_store32 (address := 8 + result) (offset := 0)
      oldResultCapacity
      (by simp)
      (by simpa [hresult8Comm] using h8_1)
      (by simpa [hresult8Comm] using h8_2)
      (by simpa [hresult8Comm] using h8_3) $$ Hcapacity'
  iintro Hcapacity
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Htag' : pointsTo_u32 0 (result + 0) oldTag $$ [Htag]
  · rw [show result + 0 = result by simp]
    iexact Htag
  iapply twp_store32 (address := result) (offset := 0) oldTag
      (by simp) (by simpa using h0_1) (by simpa using h0_2)
      (by simpa using h0_3) $$ Htag'
  iintro Htag
  isimp only [UInt32.add_zero] at Htag
  isimp only [UInt32.add_zero, hresult8Comm] at Hcapacity
  wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  ihave Hresult := Hclose $$ Htag Hpointer Hcapacity
  isimp only [growResultBytes] at Hcont
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hcont
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  iapply Hcont $$ Hruntime Hresult Hbump Hblock %hcopied Hstreams

theorem func0_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc5 : Func5Spec (hlc := hlc))
    (hfunc8 : Func8Spec (hlc := hlc)) :
    Func0Spec (hlc := hlc) := by
  unfold Func0Spec CallContract callExpr
  intro result oldCapacity oldPtr newCapacity alignment elementSize source
    initialized growBefore heapId storedCursor frontier history input output
    raised callerLocals stack code arity remainder controls calls s E Φ
  dsimp only
  iintro ⟨Hruntime, Hresult, Hsource, Hbump, Hstreams, %hfacts, Hcont⟩
  isimp only [Representations.ByteSlice] at Hresult
  icases Hresult with ⟨%hresultNowrap, HresultBytes⟩
  ihave Hresult : Representations.ByteSlice result growBefore $$ [HresultBytes]
  · unfold Representations.ByteSlice
    iframe HresultBytes
    ipureexact hresultNowrap
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 3
      Project.Mergesort.func0Def (by decide) func0_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func0Def, Project.Mergesort.func0,
    Function.toLocals, Function.numParams]
  rcases hfacts with
    ⟨rfl, rfl, hgrowLength, hnewLower, holdNew, hnewValid⟩
  let newLayout : AllocLayout :=
    { size := newCapacity.toNat, alignment := 1 }
  have hnewMatches : newLayout.Matches newCapacity 1 := by
    unfold AllocLayout.Matches newLayout
    constructor
    · rfl
    · change (1 : UInt32).toNat = 1
      decide
  have hnewUpper : newCapacity.toNat ≤ 2147483647 := by
    simpa using hnewValid.2.2.2.2.1
  have hhigh :
      UInt64.ofNat newCapacity.toNat >>> (32 : UInt64) = 0 := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_shiftRight]
    rw [show (32 : UInt64).toNat % 64 = 32 by decide]
    norm_num [Nat.shiftRight_eq_div_pow]
    have hword : newCapacity.toNat < 2 ^ 32 := newCapacity.toBitVec.isLt
    omega
  have hwrap :
      UInt32.ofNat
          (newCapacity.toUInt64.toNat % 2 ^ 32) =
        newCapacity := by
    simp
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length]
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_extendUI32 twp_localGet
    twp_extendUI32 twp_mulI64]
  have hproduct : UInt64.ofNat (1 : UInt32).toNat *
      UInt64.ofNat newCapacity.toNat = UInt64.ofNat newCapacity.toNat := by
    rw [show (1 : UInt32).toNat = 1 by decide]
    simp
  rw [hproduct]
  wasm_twp_pures [twp_localTee]
  simp only [List.length]
  wasm_twp_pures [twp_constI64 twp_shrUI64]
  rw [show (32 : UInt64) % 64 = 32 by decide, hhigh]
  wasm_twp_pures [twp_wrapI64]
  norm_num
  wasm_twp_pures [twp_eqz]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  wasm_twp_pures [twp_block twp_localGet twp_wrapI64]
  rw [hwrap]
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_const twp_localGet twp_sub]
  have hcapacityGuard : newCapacity ≤ (2147483648 : UInt32) - 1 := by
    rw [UInt32.le_iff_toNat_le_toNat]
    exact hnewUpper
  iapply twp_leU (result := 1) (by rw [if_pos hcapacityGuard])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_block twp_block twp_block twp_block]
  cases source with
  | empty =>
      isimp only [GrowSourceOwn] at Hsource
      icases Hsource with %hsource
      rcases hsource with ⟨rfl, rfl, rfl⟩
      wasm_twp_pures [twp_localGet twp_eqz]
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      wasm_twp_pures [twp_block twp_localGet]
      have hnewNonzero : newCapacity ≠ 0 := by
        intro hzero
        have := congrArg UInt32.toNat hzero
        simp only [UInt32.toNat_zero] at this
        omega
      iapply twp_brIf hnewNonzero (by rfl)
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      have Hmark : Func4Spec (hlc := hlc) :=
        Project.Mergesort.ContractProofs.func4_correct
      unfold Func4Spec CallContract callExpr at Hmark
      simp only [List.nil_append] at Hmark
      iapply Hmark
        (callerLocals :=
          { params := [.i32 result, .i32 0, .i32 1, .i32 newCapacity,
              .i32 1, .i32 1]
            locals := [.i32 1, .i32 4, .i64 newCapacity.toUInt64]
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      · unfold ResumeWP resumeExpr
        simp only [List.nil_append]
        iintro Hruntime
        iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
        wasm_twp_pures [twp_localGet twp_localGet]
        have Halloc : Func5Spec (hlc := hlc) := hfunc5
        unfold Func5Spec CallContract callExpr at Halloc
        simp only [List.cons_append, List.nil_append] at Halloc
        iapply Halloc (size := newCapacity) (alignment := 1)
          (layout := newLayout) (heapId := heapId)
          (storedCursor := storedCursor) (frontier := frontier)
          (history := history) (input := input) (output := output)
          (raised := raised)
          (callerLocals :=
            { params := [.i32 result, .i32 0, .i32 1, .i32 newCapacity,
                .i32 1, .i32 1]
              locals := [.i32 1, .i32 4, .i64 newCapacity.toUInt64]
              values := [] })
          (stack := [])
        isplitl [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isplitl_exact Hbump
        isplitl_exact Hstreams
        isplitl []
        · ipureintro
          exact ⟨hnewMatches, hnewValid, Or.inl rfl⟩
        cases hdecision : classifyBump frontier newLayout with
        | oom =>
            have hdecision' : classifyBump frontier
                { size := newCapacity.toNat, alignment := 1 } = .oom := by
              simpa [newLayout] using hdecision
            isimp only [AllocContinuation, hdecision',
              FinishGrowContinuation] at Hcont
            isimp only [AllocContinuation, hdecision,
              FinishGrowContinuation]
            iintro Hbump Hstreams
            ihave Hsource : GrowSourceOwn heapId 0 1 [] .empty $$ []
            · unfold GrowSourceOwn
              ipureexact ⟨rfl, rfl, rfl⟩
            iapply Hcont $$ Hresult Hsource Hbump Hstreams
        | success newPtr finish =>
            have hdecision' : classifyBump frontier
                { size := newCapacity.toNat, alignment := 1 } =
                  .success newPtr finish := by
              simpa [newLayout] using hdecision
            isimp only [AllocContinuation, hdecision',
              FinishGrowContinuation] at Hcont
            isimp only [AllocContinuation, hdecision,
              FinishGrowContinuation]
            isplit
            · iintro %newBytes Hruntime Hbump Hblock Hstreams
              isimp only [ResumeWP, resumeExpr, List.nil_append,
                List.append_nil]
              wasm_twp_pures [twp_localSet]
              simp only [List.length, List.set]
              wasm_twp_pures [twp_exitControl]
              simp only [List.take_zero, List.nil_append]
              ihave HblockFacts := LiveBlock_with_nonnull heapId
                history.nextId newPtr newLayout newBytes $$ Hblock
              icases HblockFacts with ⟨Hblock, %hnewPtrNonzero⟩
              wasm_twp_pures [twp_localGet]
              iapply twp_brIf hnewPtrNonzero (by rfl)
              simp only [List.take_zero, List.nil_append]
              ihave Hnormal := BI.and_elim_l $$ Hcont
              ihave Hnormal := Hnormal $$ %newBytes
              have Htail := twp_func0_success_tail
                  (source := GrowSource.empty) (result := result)
                  (oldCapacity := 0) (oldPtr := 1)
                  (newCapacity := newCapacity) (newPtr := newPtr)
                  (finish := finish)
                  (product := newCapacity.toUInt64)
                  (newBytes := newBytes) (growBefore := growBefore)
                  (initialized := []) (heapId := heapId)
                  (newId := history.nextId)
                  (finalHistory := history.allocate newPtr newLayout)
                  (input := input) (output := output) (raised := raised)
                  (callerLocals := callerLocals) (stack := stack)
                  (code := code) (arity := arity) (remainder := remainder)
                  (controls := controls) (calls := calls)
                  (middleBody := func0MiddleBody)
                  (outerBody := func0OuterBody)
                  (s := s) (E := E) (Φ := Φ)
                  hgrowLength hresultNowrap hnewPtrNonzero (by
                    simp [growCopied])
              simp only [func0MiddleBody, func0OuterBody,
                func0FinalCode, Project.Mergesort.func0,
                List.drop, List.length_nil, List.take_zero] at Htail
              iapply Htail
              isimp only [newLayout, growHistory] at Hbump
              isimp only [newLayout, growHistory] at Hblock
              isimp only [newLayout, growHistory] at Hnormal
              isimp only [newLayout, growHistory]
              isplitl_exact Hruntime
              isplitl_exact Hresult
              isplitl_exact Hbump
              isplitl_exact Hblock
              isplitl_exact Hstreams
              · iexact Hnormal
            · iintro Hbump Hstreams
              ihave Hoom := BI.and_elim_r $$ Hcont
              ihave Hsource : GrowSourceOwn heapId 0 1 [] .empty $$ []
              · unfold GrowSourceOwn
                ipureexact ⟨rfl, rfl, rfl⟩
              iapply Hoom $$ Hresult Hsource Hbump Hstreams
  | allocated oldId allBytes spare =>
      isimp only [GrowSourceOwn] at Hsource
      icases Hsource with ⟨%hsource, Hblock⟩
      have holdPositive : 0 < oldCapacity.toNat := hsource.1
      have holdNonzero : oldCapacity ≠ 0 := by
        intro hzero
        have := congrArg UInt32.toNat hzero
        simp only [UInt32.toNat_zero] at this
        omega
      let oldLayout : AllocLayout :=
        { size := oldCapacity.toNat, alignment := 1 }
      have holdMatches : oldLayout.Matches oldCapacity 1 := by
        simp [oldLayout, AllocLayout.Matches]
      have holdValid : oldLayout.Valid := by
        change 0 < oldCapacity.toNat ∧ 0 < 1 ∧
          (∃ exponent, 1 = 2 ^ exponent) ∧ 1 ≤ 2147483648 ∧
          oldCapacity.toNat ≤ 2147483648 - 1 ∧
          oldCapacity.toNat < UInt32.size ∧ 1 < UInt32.size
        refine ⟨holdPositive, by omega, ⟨0, by norm_num⟩, by omega,
          ?_, ?_, by norm_num [UInt32.size]⟩
        · omega
        · exact oldCapacity.toBitVec.isLt
      wasm_twp_pures [twp_localGet]
      iapply twp_eqz (by rw [if_neg holdNonzero])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet twp_mul]
      rw [show oldCapacity * (1 : UInt32) = oldCapacity by bv_decide]
      wasm_twp_pures [twp_localGet twp_localGet]
      have Hrealloc : Func8Spec (hlc := hlc) := hfunc8
      unfold Func8Spec CallContract callExpr at Hrealloc
      simp only [List.cons_append, List.nil_append] at Hrealloc
      iapply Hrealloc (oldPtr := oldPtr)
        (oldSize := oldCapacity) (alignment := 1)
        (newSize := newCapacity) (oldLayout := oldLayout)
        (newLayout := newLayout) (heapId := heapId) (oldId := oldId)
        (oldBytes := allBytes) (storedCursor := storedCursor)
        (frontier := frontier) (history := history) (input := input)
        (output := output) (raised := raised)
        (callerLocals :=
          { params := [.i32 result, .i32 oldCapacity, .i32 oldPtr,
              .i32 newCapacity, .i32 1, .i32 1]
            locals := [.i32 1, .i32 4, .i64 newCapacity.toUInt64]
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      isplitl_exact Hbump
      isplitl_exact Hblock
      isplitl_exact Hstreams
      isplitl []
      · ipureintro
        exact ⟨holdMatches, hnewMatches, holdValid, hnewValid, rfl,
          holdNew⟩
      cases hdecision : classifyBump frontier newLayout with
      | oom =>
          have hdecision' : classifyBump frontier
              { size := newCapacity.toNat, alignment := 1 } = .oom := by
            simpa [newLayout] using hdecision
          isimp only [ReallocContinuation, hdecision',
            FinishGrowContinuation] at Hcont
          isimp only [ReallocContinuation, hdecision,
            FinishGrowContinuation]
          iintro Hbump Hblock Hstreams
          ihave Hblock' : LiveBlock heapId oldId oldPtr
              { size := oldCapacity.toNat, alignment := 1 } allBytes $$
              [Hblock]
          · iexact Hblock
          ihave Hsource : GrowSourceOwn heapId oldCapacity oldPtr initialized
              (.allocated oldId allBytes spare) $$ [Hblock']
          · unfold GrowSourceOwn
            isplitr
            · ipureintro
              exact hsource
            · iexact Hblock'
          iapply Hcont $$ Hresult Hsource Hbump Hstreams
      | success newPtr finish =>
          have hdecision' : classifyBump frontier
              { size := newCapacity.toNat, alignment := 1 } =
                .success newPtr finish := by
            simpa [newLayout] using hdecision
          isimp only [ReallocContinuation, hdecision',
            FinishGrowContinuation] at Hcont
          isimp only [ReallocContinuation, hdecision,
            FinishGrowContinuation]
          isplit
          · iintro %newBytes Hruntime Hbump Hblock %hcopy Hstreams
            simp only [oldLayout, newLayout] at hcopy
            rw [min_eq_left (Nat.le_of_lt holdNew)] at hcopy
            isimp only [ResumeWP, resumeExpr, List.nil_append,
              List.append_nil]
            wasm_twp_pures [twp_localSet]
            simp only [List.length, List.set]
            wasm_twp_pures [twp_br]
            simp only [List.take_zero, List.nil_append]
            ihave HblockFacts := LiveBlock_with_nonnull heapId
              history.nextId newPtr newLayout newBytes $$ Hblock
            icases HblockFacts with ⟨Hblock, %hnewPtrNonzero⟩
            wasm_twp_pures [twp_localGet]
            iapply twp_brIf hnewPtrNonzero (by rfl)
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            have hprefix : newBytes.take initialized.length = initialized := by
              have hcopyInit := congrArg
                (List.take initialized.length) hcopy
              simp only [List.take_take,
                min_eq_left hsource.2.1] at hcopyInit
              rw [hcopyInit, hsource.2.2.1]
              simp
            have hcopied : growCopied
                (.allocated oldId allBytes spare) oldCapacity newBytes ∧
                newBytes.take initialized.length = initialized := by
              constructor
              · unfold growCopied
                have hallLength : allBytes.length = oldCapacity.toNat := by
                  rw [hsource.2.2.1, List.length_append,
                    hsource.2.2.2]
                  omega
                rw [(List.take_eq_self_iff allBytes).mpr hallLength.le] at hcopy
                exact hcopy
              · exact hprefix
            ihave Hnormal := BI.and_elim_l $$ Hcont
            ihave Hnormal := Hnormal $$ %newBytes
            have Htail := twp_func0_success_tail
                (source := GrowSource.allocated oldId allBytes spare)
                (result := result) (oldCapacity := oldCapacity)
                (oldPtr := oldPtr) (newCapacity := newCapacity)
                (newPtr := newPtr) (finish := finish)
                (product := newCapacity.toUInt64)
                (newBytes := newBytes) (growBefore := growBefore)
                (initialized := initialized) (heapId := heapId)
                (newId := history.nextId)
                (finalHistory := history.reallocate oldId oldPtr oldLayout
                  newPtr newLayout)
                (input := input) (output := output) (raised := raised)
                (callerLocals := callerLocals) (stack := stack)
                (code := code) (arity := arity) (remainder := remainder)
                (controls := controls) (calls := calls)
                (middleBody := func0MiddleBody)
                (outerBody := func0OuterBody)
                (s := s) (E := E) (Φ := Φ)
                hgrowLength hresultNowrap hnewPtrNonzero hcopied
            simp only [func0MiddleBody, func0OuterBody,
              func0FinalCode, Project.Mergesort.func0,
              List.drop] at Htail
            iapply Htail
            isimp only [oldLayout, newLayout, growHistory] at Hbump
            isimp only [oldLayout, newLayout, growHistory] at Hblock
            isimp only [oldLayout, newLayout, growHistory] at Hnormal
            isimp only [oldLayout, newLayout, growHistory]
            isplitl_exact Hruntime
            isplitl_exact Hresult
            isplitl_exact Hbump
            isplitl_exact Hblock
            isplitl_exact Hstreams
            · iexact Hnormal
          · iintro Hbump Hblock Hstreams
            ihave Hoom := BI.and_elim_r $$ Hcont
            ihave Hblock' : LiveBlock heapId oldId oldPtr
                { size := oldCapacity.toNat, alignment := 1 } allBytes $$
                [Hblock]
            · iexact Hblock
            ihave Hsource : GrowSourceOwn heapId oldCapacity oldPtr initialized
                (.allocated oldId allBytes spare) $$ [Hblock']
            · unfold GrowSourceOwn
              isplitr
              · ipureintro
                exact hsource
              · iexact Hblock'
            iapply Hoom $$ Hresult Hsource Hbump Hstreams

end Project.Mergesort.Func0Proof
