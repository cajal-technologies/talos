import Project.RustHashMap.Func30Proof

/-!
# Proof of the generated `finish_grow`

This file proves local `func97` (absolute index 100) from the allocator
contracts `Func55Spec` and `Func58Spec` and the marker contract
`Func30Spec`.  The proof follows `Project.Mergesort.Func0Proof`.  The
function has no element-size multiply, so the signed guard `i32.ge_s` on
the new capacity is the only arithmetic branch.  The valid-layout
hypothesis of `Func97Spec` excludes it.
-/

namespace Project.RustHashMap.Func97Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.VecGrow
open scoped Wasm.SmallStep.Outcome

private theorem func97_index :
    Project.RustHashMap.«module».funcs[97]? =
      some Project.RustHashMap.func97Def := by rfl

/-- The signed guard holds for every capacity below `2 ^ 31`. -/
private theorem toInt32_nonneg (n : UInt32) (h : n.toNat < 2 ^ 31) :
    (0 : UInt32).toInt32 ≤ n.toInt32 := by
  rw [Int32.le_iff_toInt_le]
  change ((0 : UInt32).toBitVec).toInt ≤ (n.toBitVec).toInt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp only [UInt32.toBitVec_ofNat, BitVec.toNat_ofNat]
  have hn : n.toBitVec.toNat = n.toNat := rfl
  rw [hn]
  split <;> omega

/-- Expose a twelve-byte result slot as three writable words, with an exact
close operation for the grow result.  Wasm scalar stores need no
alignment. -/
private theorem ByteSlice_twelve_storeFocus
    [WasmSmallStepGS hlc Universal.State]
    (ptr : UInt32) (bytes : List UInt8) (hlength : bytes.length = 12) :
    Slices.ByteSlice 0 ptr bytes ⊢
      iprop(∃ oldTag oldPtr oldCapacity : UInt32,
        pointsTo_u32 0 ptr oldTag ∗
        pointsTo_u32 0 (ptr + 4) oldPtr ∗
        pointsTo_u32 0 (ptr + 8) oldCapacity ∗
        (∀ tag : UInt32, ∀ pointer : UInt32, ∀ capacity : UInt32,
          pointsTo_u32 0 ptr tag -∗
          pointsTo_u32 0 (ptr + 4) pointer -∗
          pointsTo_u32 0 (ptr + 8) capacity -∗
          Slices.ByteSlice 0 ptr
            (WordCodec.u32le.serialize [tag, pointer, capacity]))) := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%hnowrap, HrawBytes⟩
  ihave Hbytes : Slices.ByteSlice 0 ptr bytes $$ [HrawBytes]
  · unfold Slices.ByteSlice
    iframe_pureexact using [HrawBytes] => hnowrap
  let first := bytes.take 4
  let rest := bytes.drop 4
  let second := rest.take 4
  let third := rest.drop 4
  have hfirstRest : bytes = first ++ rest :=
    (List.take_append_drop 4 bytes).symm
  have hsecondThird : rest = second ++ third :=
    (List.take_append_drop 4 rest).symm
  have hfirstLength : first.length = 4 := by
    simp [first, hlength]
  have hrestLength : rest.length = 8 := by
    simp [rest, hlength]
  have hsecondLength : second.length = 4 := by
    simp [second, hrestLength]
  have hthirdLength : third.length = 4 := by
    simp [third, hrestLength]
  ihave Hsplit : Slices.ByteSlice 0 ptr (first ++ rest) $$ [Hbytes]
  · irw_exact [← hfirstRest] with Hbytes
  icases (Slices.ByteSlice_append 0 ptr first rest).mp $$ Hsplit with
    ⟨Hfirst, Hrest⟩
  have hfirstAddress : ptr + UInt32.ofNat first.length = ptr + 4 := by
    simp [hfirstLength]
  ihave HrestAt4 : Slices.ByteSlice 0 (ptr + 4) rest $$ [Hrest]
  · irw_exact [← hfirstAddress] with Hrest
  ihave Hrest' : Slices.ByteSlice 0 (ptr + 4) (second ++ third) $$ [HrestAt4]
  · irw_exact [← hsecondThird] with HrestAt4
  icases (Slices.ByteSlice_append 0 (ptr + 4) second third).mp $$ Hrest' with
    ⟨Hsecond, Hthird⟩
  have hfirstNowrap : ptr.toNat + 4 < UInt32.size := by omega
  have hptr4Nat : (ptr + 4).toNat = ptr.toNat + 4 := by
    simpa using Slices.byteOffset_toNat ptr 4 hfirstNowrap
  have hsecondNowrap : (ptr + 4).toNat + 4 < UInt32.size := by omega
  have hptr8 : (ptr + 4) + 4 = ptr + 8 := by
    simp only [UInt32.add_assoc, UInt32.reduceAdd]
  have hthirdNowrap : (ptr + 8).toNat + 4 < UInt32.size := by
    have hptr8Nat : (ptr + 8).toNat = ptr.toNat + 8 := by
      simpa using Slices.byteOffset_toNat ptr 8 (by omega)
    omega
  ihave ⟨Hfirst, HcloseFirst⟩ := Slices.ByteSlice_storeAnyWordFocus 0 ptr first
    hfirstLength hfirstNowrap $$ Hfirst
  ihave ⟨Hsecond, HcloseSecond⟩ := Slices.ByteSlice_storeAnyWordFocus 0
    (ptr + 4) second hsecondLength hsecondNowrap $$ Hsecond
  have hthirdAddress :
      ptr + 4 + UInt32.ofNat second.length = ptr + 8 := by
    simp [hsecondLength, hptr8]
  ihave Hthird' : Slices.ByteSlice 0 (ptr + 8) third $$ [Hthird]
  · irw_exact [← hthirdAddress] with Hthird
  ihave ⟨Hthird, HcloseThird⟩ := Slices.ByteSlice_storeAnyWordFocus 0
    (ptr + 8) third hthirdLength hthirdNowrap $$ Hthird'
  iexists WordCodec.decodeU32 first, WordCodec.decodeU32 second,
    WordCodec.decodeU32 third
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
  have htagLength : (WordCodec.u32le.serialize [tag]).length = 4 := by
    rw [WordCodec.u32le_serialize_length]; rfl
  have hpairLength :
      (WordCodec.u32le.serialize [tag] ++
        WordCodec.u32le.serialize [pointer]).length = 8 := by
    rw [List.length_append, WordCodec.u32le_serialize_length,
      WordCodec.u32le_serialize_length]; rfl
  ihave Hhead : Slices.ByteSlice 0 ptr
      (WordCodec.u32le.serialize [tag] ++
        WordCodec.u32le.serialize [pointer]) $$ [Htag Hpointer]
  · iapply (Slices.ByteSlice_append 0 ptr (WordCodec.u32le.serialize [tag])
      (WordCodec.u32le.serialize [pointer])).mpr
    isplitl_exact Htag
    · have hpointerAddress :
          ptr + UInt32.ofNat (WordCodec.u32le.serialize [tag]).length =
            ptr + 4 := by
        rw [htagLength]; rfl
      ihave Hpointer' : Slices.ByteSlice 0
          (ptr + UInt32.ofNat (WordCodec.u32le.serialize [tag]).length)
          (WordCodec.u32le.serialize [pointer]) $$ [Hpointer]
      · irw_exact [hpointerAddress] with Hpointer
      iexact Hpointer'
  ihave Hall : Slices.ByteSlice 0 ptr
      ((WordCodec.u32le.serialize [tag] ++
          WordCodec.u32le.serialize [pointer]) ++
        WordCodec.u32le.serialize [capacity]) $$ [Hhead Hcapacity]
  · iapply (Slices.ByteSlice_append 0 ptr
      (WordCodec.u32le.serialize [tag] ++ WordCodec.u32le.serialize [pointer])
      (WordCodec.u32le.serialize [capacity])).mpr
    isplitl_exact Hhead
    · have hcapacityAddress : ptr + UInt32.ofNat
            (WordCodec.u32le.serialize [tag] ++
              WordCodec.u32le.serialize [pointer]).length = ptr + 8 := by
        rw [hpairLength]; rfl
      ihave Hcapacity' : Slices.ByteSlice 0
          (ptr + UInt32.ofNat
            (WordCodec.u32le.serialize [tag] ++
              WordCodec.u32le.serialize [pointer]).length)
          (WordCodec.u32le.serialize [capacity]) $$ [Hcapacity]
      · irw_exact [hcapacityAddress] with Hcapacity
      iexact Hcapacity'
  rw [show WordCodec.u32le.serialize [tag, pointer, capacity] =
      (WordCodec.u32le.serialize [tag] ++
          WordCodec.u32le.serialize [pointer]) ++
        WordCodec.u32le.serialize [capacity] by
    simp [WordCodec.serialize_cons]]
  iexact Hall

/-- The instructions after the outer block: the capacity word at the
selected offset, then the tag or pointer word at the result slot. -/
private def func97FinalCode : Program :=
  [.localGet 0, .localGet 2, .add, .localGet 3, .store32 0,
    .localGet 0, .localGet 1, .store32 0]

/-- The outer block body, taken from the emitted program. -/
private def func97OuterBody : Program :=
  match Project.RustHashMap.func97 with
  | .block _ _ body :: _ => body
  | _ => []

/-- The second block of the outer body.  Its continuation stores the
offset `8` for the capacity word. -/
private def func97MiddleBody : Program :=
  match func97OuterBody.drop 1 with
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
    iframe_pureexact using [Htoken Hbytes] => hfacts
  · ipureexact hfacts.2.1

/-- The common normal-return tail after the allocator returned a non-null
pointer.  Local `1` holds the pointer.  The tail writes the pointer at
offset `4`, the capacity at offset `8`, and the tag `0` at offset `0`. -/
private theorem twp_func97_success_tail
    [WasmSmallStepGS hlc Universal.State]
    (result oldCapacity oldPtr newCapacity newPtr finish : UInt32)
    (newBytes growBefore initialized : List UInt8)
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
      Slices.ByteSlice 0 result growBefore ∗
      BumpHeap heapId finish finish.toNat finalHistory ∗
      LiveBlock heapId newId newPtr
        { size := newCapacity.toNat, alignment := 1 } newBytes ∗
      Streams input output raised ∗
      (RuntimeContext -∗
        Slices.ByteSlice 0 result (growResultBytes newPtr newCapacity) -∗
        BumpHeap heapId finish finish.toNat finalHistory -∗
        LiveBlock heapId newId newPtr
          { size := newCapacity.toNat, alignment := 1 } newBytes -∗
        ⌜growCopied source oldCapacity newBytes ∧
          newBytes.take initialized.length = initialized⌝ -∗
        Streams input output raised -∗
        ResumeWP [] callerLocals stack code arity remainder controls calls
          s E Φ)) ⊢
      WP (.running
        ⟨{ params := [.i32 result, .i32 newPtr, .i32 oldPtr,
              .i32 newCapacity],
            locals := [],
            values := [] },
          [.localGet 0, .localGet 1, .store32 4,
            .const 0, .localSet 1], 0, [],
          { kind := .block, paramArity := 0, resultArity := 0,
            body := middleBody,
            continuation := [.const 8, .localSet 2],
            belowStack := [] } ::
          { kind := .block, paramArity := 0, resultArity := 0,
            body := outerBody, continuation := func97FinalCode,
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
  ihave Hfocus := ByteSlice_twelve_storeFocus result growBefore
    hresultLength $$ Hresult
  icases Hfocus with
    ⟨%oldTag, %oldResultPtr, %oldResultCapacity,
      Htag, Hpointer, Hcapacity, Hclose⟩
  rw [hresultLength] at hresultNowrap
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
  wasm_twp_pures [twp_exitControl] using [func97FinalCode, List.take_zero,
    List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_add twp_localGet]
  have hresult8Comm : 8 + result = result + 8 := by
    ac_rfl
  ihave Hcapacity' : pointsTo_u32 0 (8 + result + 0)
      oldResultCapacity $$ [Hcapacity]
  · irw_exact [show 8 + result + 0 = result + 8 by simp [hresult8Comm]] with
      Hcapacity
  iapply twp_store32 (address := 8 + result) (offset := 0)
      oldResultCapacity
      (by simp)
      (by simpa [hresult8Comm] using h8_1)
      (by simpa [hresult8Comm] using h8_2)
      (by simpa [hresult8Comm] using h8_3) $$ Hcapacity'
  iintro Hcapacity
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Htag' : pointsTo_u32 0 (result + 0) oldTag $$ [Htag]
  · irw_exact [show result + 0 = result by simp] with Htag
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
  iclose_map_runtime Hruntime with Hmodule Henv
  iapply Hcont $$ Hruntime Hresult Hbump Hblock %hcopied Hstreams

theorem func97_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc55 : Func55Spec (hlc := hlc))
    (hfunc58 : Func58Spec (hlc := hlc)) :
    Func97Spec (hlc := hlc) := by
  unfold Func97Spec CallContract callExpr
  intro result oldCapacity oldPtr newCapacity source initialized growBefore
    heapId storedCursor frontier history input output raised callerLocals
    stack code arity remainder controls calls s E Φ
  dsimp only
  iintro ⟨Hruntime, Hresult, Hsource, Hbump, Hstreams, %hfacts, Hcont⟩
  isimp only [Slices.ByteSlice] at Hresult
  icases Hresult with ⟨%hresultNowrap, HresultBytes⟩
  ihave Hresult : Slices.ByteSlice 0 result growBefore $$ [HresultBytes]
  · unfold Slices.ByteSlice
    iframe_pureexact using [HresultBytes] => hresultNowrap
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 100
      Project.RustHashMap.func97Def (by decide) func97_index with Hmodule
  simp [Project.RustHashMap.func97Def, Project.RustHashMap.func97,
    Function.toLocals, Function.numParams]
  rcases hfacts with ⟨hgrowLength, hnewLower, holdNew, hnewValid⟩
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
  have hguard : (0 : UInt32).toInt32 ≤ newCapacity.toInt32 :=
    toInt32_nonneg newCapacity (by omega)
  wasm_twp_pures [twp_block twp_block twp_localGet twp_const]
  iapply twp_geS (result := 1) (by rw [if_pos hguard])
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
      have Hmark : Func30Spec (hlc := hlc) :=
        Project.RustHashMap.Func30Proof.func30_correct
      unfold Func30Spec CallContract callExpr at Hmark
      simp only [List.nil_append] at Hmark
      iapply Hmark
        (callerLocals :=
          { params := [.i32 result, .i32 0, .i32 1, .i32 newCapacity]
            locals := []
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      · unfold ResumeWP resumeExpr
        simp only [List.nil_append]
        iintro Hruntime
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        wasm_twp_pures [twp_localGet twp_const]
        have Halloc : Func55Spec (hlc := hlc) := hfunc55
        unfold Func55Spec CallContract callExpr at Halloc
        simp only [List.cons_append, List.nil_append] at Halloc
        iapply Halloc (size := newCapacity) (alignment := 1)
          (layout := newLayout) (heapId := heapId)
          (storedCursor := storedCursor) (frontier := frontier)
          (history := history) (input := input) (output := output)
          (raised := raised)
          (callerLocals :=
            { params := [.i32 result, .i32 0, .i32 1, .i32 newCapacity]
              locals := []
              values := [] })
          (stack := [])
        isplitl [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isplitl_exacts [Hbump Hstreams]
        isplitl_pureexact ⟨hnewMatches, hnewValid, Or.inl rfl⟩
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
              wasm_twp_localSet [List.length, List.set]
              wasm_twp_pures [twp_exitControl] using [List.take_zero,
                List.nil_append]
              ihave ⟨Hblock, %hnewPtrNonzero⟩ := LiveBlock_with_nonnull heapId
                history.nextId newPtr newLayout newBytes $$ Hblock
              wasm_twp_pures [twp_localGet]
              iapply twp_brIf hnewPtrNonzero (by rfl)
              simp only [List.take_zero, List.nil_append]
              ihave Hnormal := BI.and_elim_l $$ Hcont
              ihave Hnormal := Hnormal $$ %newBytes
              have Htail := twp_func97_success_tail
                  (source := GrowSource.empty) (result := result)
                  (oldCapacity := 0) (oldPtr := 1)
                  (newCapacity := newCapacity) (newPtr := newPtr)
                  (finish := finish)
                  (newBytes := newBytes) (growBefore := growBefore)
                  (initialized := []) (heapId := heapId)
                  (newId := history.nextId)
                  (finalHistory := history.allocate newPtr newLayout)
                  (input := input) (output := output) (raised := raised)
                  (callerLocals := callerLocals) (stack := stack)
                  (code := code) (arity := arity) (remainder := remainder)
                  (controls := controls) (calls := calls)
                  (middleBody := func97MiddleBody)
                  (outerBody := func97OuterBody)
                  (s := s) (E := E) (Φ := Φ)
                  hgrowLength hresultNowrap hnewPtrNonzero (by
                    simp [growCopied])
              simp only [func97MiddleBody, func97OuterBody,
                func97FinalCode, Project.RustHashMap.func97,
                List.drop, List.length_nil, List.take_zero] at Htail
              iapply Htail
              isimp only [newLayout, growHistory] at Hbump
              isimp only [newLayout, growHistory] at Hblock
              isimp only [newLayout, growHistory] at Hnormal
              isimp only [newLayout, growHistory]
              isplitl_exacts [Hruntime Hresult Hbump Hblock Hstreams]
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
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const
        twp_localGet]
      have Hrealloc : Func58Spec (hlc := hlc) := hfunc58
      unfold Func58Spec CallContract callExpr at Hrealloc
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
              .i32 newCapacity]
            locals := []
            values := [] })
        (stack := [])
      isplitl [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      isplitl_exacts [Hbump Hblock Hstreams]
      isplitl_pureexact ⟨holdMatches, hnewMatches, holdValid, hnewValid,
          Or.inl rfl,
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
            isplitr_pureexact hsource
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
            wasm_twp_localSet [List.length, List.set]
            wasm_twp_pures [twp_br] using [List.take_zero, List.nil_append]
            ihave ⟨Hblock, %hnewPtrNonzero⟩ := LiveBlock_with_nonnull heapId
              history.nextId newPtr newLayout newBytes $$ Hblock
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
            have Htail := twp_func97_success_tail
                (source := GrowSource.allocated oldId allBytes spare)
                (result := result) (oldCapacity := oldCapacity)
                (oldPtr := oldPtr) (newCapacity := newCapacity)
                (newPtr := newPtr) (finish := finish)
                (newBytes := newBytes) (growBefore := growBefore)
                (initialized := initialized) (heapId := heapId)
                (newId := history.nextId)
                (finalHistory := history.reallocate oldId oldPtr oldLayout
                  newPtr newLayout)
                (input := input) (output := output) (raised := raised)
                (callerLocals := callerLocals) (stack := stack)
                (code := code) (arity := arity) (remainder := remainder)
                (controls := controls) (calls := calls)
                (middleBody := func97MiddleBody)
                (outerBody := func97OuterBody)
                (s := s) (E := E) (Φ := Φ)
                hgrowLength hresultNowrap hnewPtrNonzero hcopied
            simp only [func97MiddleBody, func97OuterBody,
              func97FinalCode, Project.RustHashMap.func97,
              List.drop] at Htail
            iapply Htail
            isimp only [oldLayout, newLayout, growHistory] at Hbump
            isimp only [oldLayout, newLayout, growHistory] at Hblock
            isimp only [oldLayout, newLayout, growHistory] at Hnormal
            isimp only [oldLayout, newLayout, growHistory]
            isplitl_exacts [Hruntime Hresult Hbump Hblock Hstreams]
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
              isplitr_pureexact hsource
              · iexact Hblock'
            iapply Hoom $$ Hresult Hsource Hbump Hstreams

end Project.RustHashMap.Func97Proof
