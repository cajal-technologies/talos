import Project.Mergesort.ContractProofs

/-!
# Proof of the zeroed bump allocator contract

This module isolates the proof of generated local `func9` (absolute Wasm
function index 12).  The implementation repeats the bump-allocation sequence
and zero-fills the committed block before returning it.
-/

namespace Project.Mergesort.Func9Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

private theorem func9_index :
    Project.Mergesort.module.funcs[9]? =
      some Project.Mergesort.func9Def := by
  rfl

private abbrev func9ZeroBody : Program :=
  [.localGet 1, .eqz, .br_if 0,
    .localGet 0, .eqz, .br_if 0,
    .localGet 1, .const 0, .localGet 0, .memoryFill]

private abbrev func9ArithmeticPrefix : Program :=
  [.localGet 1, .const 0xFFFFFFFF, .add, .localTee 2,
    .const 0, .load32 allocatorCursor, .localTee 3,
    .const heapBase, .localGet 3, .select, .add, .localTee 3,
    .localGet 2, .ltU, .br_if 0,
    .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 1,
    .localGet 0, .add, .localTee 2,
    .localGet 1, .ltU, .br_if 0,
    .localGet 2, .const 0, .ltS, .br_if 0]

private abbrev func9GrowthBody : Program :=
  [.localGet 2, .const 65535, .add, .const 16, .shrU,
    .localTee 3, .memorySize, .localTee 4, .leU, .br_if 0,
    .localGet 3, .localGet 4, .sub, .memoryGrow,
    .const 0xFFFFFFFF, .eq, .br_if 1]

private abbrev func9PostArithmetic : Program :=
  [.block 0 0 func9GrowthBody,
    .const 0, .localGet 2, .store32 1049492,
    .block 0 0 func9ZeroBody, .localGet 1, .ret]

private abbrev func9Locals
    (size base finish requiredPages currentPages : UInt32)
    (values : List Value := []) : Locals :=
  { params := [.i32 size, .i32 base]
    locals := [.i32 finish, .i32 requiredPages, .i32 currentPages]
    values := values }

private theorem twp_ltS
    [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hresult : result = if lhs.toInt32 < rhs.toInt32 then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ltS :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ltS hresult)

/-- Once the cursor commit has produced a fresh block, the remaining generated
code zeroes exactly that block and returns its non-null base pointer. -/
private theorem twp_func9_zero_and_return
    [WasmSmallStepGS hlc Universal.State]
    (size base finish requiredPages currentPages : UInt32)
    (layout : AllocLayout) (heapId : GName) (allocationId : Nat)
    (bytes : List UInt8) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (functionControls controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hmatches : layout.Matches size 4) (hvalid : layout.Valid) :
    iprop(
      RuntimeContext ∗
      BumpHeap heapId finish finish.toNat history ∗
      LiveBlock heapId allocationId base layout bytes ∗
      Streams input output raised ∗
      (RuntimeContext -∗
        BumpHeap heapId finish finish.toNat history -∗
        LiveBlock heapId allocationId base layout
          (List.replicate layout.size 0) -∗
        Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func9Locals size base finish requiredPages currentPages,
          [.block 0 0 func9ZeroBody, .localGet 1, .ret], 1, [],
          functionControls,
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hbump, Hblock, Hstreams, Hcont⟩
  have hsize : size.toNat = layout.size := hmatches.1
  have hpositive : 0 < size.toNat := by
    simpa only [hsize] using hvalid.1
  have hsizeNonzero : size ≠ 0 := by
    intro hzero
    have := congrArg UInt32.toNat hzero; simp only [UInt32.toNat_zero] at this
    omega
  isimp only [LiveBlock] at Hblock
  icases Hblock with ⟨Htoken, Hslice, %hblockFacts⟩
  isimp only [Project.Mergesort.Representations.ByteSlice] at Hslice
  icases Hslice with ⟨%hnowrap, Hbytes⟩
  have hbaseNonzero : base ≠ 0 := hblockFacts.2.1
  wasm_twp_pures [twp_block] using [func9ZeroBody, func9Locals]
  wasm_twp_pures [twp_localGet]
  iapply twp_eqz (result := 0) (by simp [hbaseNonzero])
  wasm_twp_pures [twp_brIfZero twp_localGet]
  iapply twp_eqz (result := 0) (by simp [hsizeNonzero])
  wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_localGet]
  wasm_twp_bind twp_memoryFill32 bytes
      (by rw [hblockFacts.1, ← hsize])
      hpositive
      (by rw [hsize, ← hblockFacts.1];
          simpa only [UInt32.size] using hnowrap) with Hbytes => Hbytes
  ihave Hslice : Project.Mergesort.Representations.ByteSlice base
      (List.replicate layout.size 0) $$ [Hbytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    isplitl []
    · ipureintro
      simpa [List.length_replicate] using
        (show base.toNat + layout.size < UInt32.size by
          rw [← hblockFacts.1]
          exact hnowrap)
    · rw [← hblockFacts.1]
      irw_exact [← show (0 : UInt32).toUInt8 = (0 : UInt8) by decide] with Hbytes
  ihave Hblock : LiveBlock heapId allocationId base layout
      (List.replicate layout.size 0) $$ [Htoken Hslice]
  · unfold LiveBlock
    iframe_pureexact ⟨by simp, hblockFacts.2⟩
  wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
  wasm_twp_pures [twp_localGet]
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_return_from_call Hmodule [List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.cons_append,
    List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule Henv] Hbump Hblock Hstreams
  · isplitl_exact Hmodule
    · iexact Henv

/-- Once physical capacity has been established and the fresh range has been
claimed, commit the cursor and allocator metadata, then run the zeroing tail. -/
private theorem twp_func9_commit_zero_and_return
    [WasmSmallStepGS hlc Universal.State]
    (size base finish requiredPages currentPages storedCursor : UInt32)
    (layout : AllocLayout) (heapId : GName)
    (bytes : List UInt8) (frontier ownedPages : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (functionControls controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hfrontierLow : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hmatches : layout.Matches size 4) (hvalid : layout.Valid)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hbytesLength : bytes.length = layout.size)
    (hphysical : finish.toNat ≤ ownedPages * 65536) :
    iprop(
      RuntimeContext ∗
      pointsTo_u32 0 allocatorCursor storedCursor ∗
      heapFrontierOwn finish.toNat ∗
      AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗
      memoryPagesOwn ownedPages ∗
      Project.Mergesort.Representations.ByteSlice base bytes ∗
      Streams input output raised ∗
      (RuntimeContext -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout
          (List.replicate layout.size 0) -∗
        Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func9Locals size base finish requiredPages currentPages [.i32 0],
          [.localGet 2, .store32 1049492,
            .block 0 0 func9ZeroBody, .localGet 1, .ret],
          1, [], functionControls,
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcursor, Hfrontier, Hauth, Hretired, Hpages, Hbytes,
    Hstreams, Hcont⟩
  wasm_twp_pures [twp_localGet]
  ihave HcursorAt : pointsTo_u32 0 ((0 : UInt32) + 1049492)
      storedCursor $$ [Hcursor]
  · irw_exact [show (0 : UInt32) + 1049492 = allocatorCursor by decide] with Hcursor
  wasm_twp_bind twp_store32 (address := 0) (offset := 1049492) (value := finish)
      storedCursor (by decide) (by decide) (by decide) (by decide) with HcursorAt => Hcursor
  ihave Hcursor' : pointsTo_u32 0 allocatorCursor finish $$ [Hcursor]
  · irw_exact [← show (0 : UInt32) + 1049492 = allocatorCursor by decide] with Hcursor
  have halignment : layout.alignment = 4 := by
    simpa using hmatches.2.symm
  imod BumpHeap_commit heapId frontier history base finish layout bytes
      ownedPages
      hfrontierLow hwf hvalid (Or.inr halignment) hclassify hbytesLength
      hphysical $$ [Hcursor' Hfrontier Hauth Hretired Hpages Hbytes] with
      ⟨Hbump, Hblock⟩
  · iframe
  iapply twp_func9_zero_and_return size base finish requiredPages currentPages
      layout heapId history.nextId bytes (history.allocate base layout)
      input output raised callerLocals stack code arity remainder
      functionControls controls calls s E Φ hmatches hvalid
  iframe Hruntime Hbump Hblock Hstreams Hcont

/-- Claim the already-capacity-checked physical bytes, then perform the cursor
commit and generated zeroing tail. -/
private theorem twp_func9_claim_commit_zero_and_return
    [WasmSmallStepGS hlc Universal.State]
    (size base finish requiredPages currentPages storedCursor : UInt32)
    (layout : AllocLayout) (heapId : GName)
    (frontier ownedPages : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (functionControls controls : List ControlFrame) (calls : List CallFrame)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hfrontierLow : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hmatches : layout.Matches size 4) (hvalid : layout.Valid)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hbaseFresh : frontier ≤ base.toNat)
    (hallocWord : base.toNat + layout.size < UInt32.size)
    (hfinishExact : finish.toNat = base.toNat + layout.size)
    (hphysical : finish.toNat ≤ ownedPages * 65536) :
    iprop(
      RuntimeContext ∗
      pointsTo_u32 0 allocatorCursor storedCursor ∗
      heapFrontierOwn frontier ∗
      AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗
      memoryPagesOwn ownedPages ∗
      Streams input output raised ∗
      (RuntimeContext -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout
          (List.replicate layout.size 0) -∗
        Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func9Locals size base finish requiredPages currentPages,
          [.const 0, .localGet 2, .store32 1049492,
            .block 0 0 func9ZeroBody, .localGet 1, .ret],
          1, [], functionControls,
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcursor, Hfrontier, Hauth, Hretired, Hpages, Hstreams,
    Hcont⟩
  have hphysicalBase : base.toNat + layout.size ≤ ownedPages * 65536 := by
    simpa only [← hfinishExact] using hphysical
  ihave HclaimFrame : iprop(
      RuntimeContext ∗ pointsTo_u32 0 allocatorCursor storedCursor ∗
      AllocMetaAuth heapId history ∗ RetiredBytes heapId history ∗
      Streams input output raised ∗
      (RuntimeContext -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout
          (List.replicate layout.size 0) -∗
        Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls
          calls s E Φ)) $$ [Hruntime Hcursor Hauth Hretired Hstreams Hcont]
  · iframe
  iapply Project.Mergesort.ContractProofs.twp_const_alloc_freshRange_owned
      frontier ownedPages base layout.size hbaseFresh hphysicalBase hallocWord
      $$ HclaimFrame Hfrontier Hpages
  iintro %bytes %hbytes Hfrontier Hpages Hbytes HclaimFrame
  icases HclaimFrame with
    ⟨Hruntime, Hcursor, Hauth, Hretired, Hstreams, Hcont⟩
  ihave Hfrontier' : heapFrontierOwn finish.toNat $$ [Hfrontier]
  · irw_exact [hfinishExact] with Hfrontier
  iapply twp_func9_commit_zero_and_return size base finish requiredPages
      currentPages storedCursor layout heapId bytes frontier ownedPages history
      input output raised callerLocals stack code arity remainder functionControls
      controls calls s E Φ hfrontierLow hwf hmatches hvalid hclassify hbytes
      hphysical
  iframe Hruntime Hcursor Hfrontier' Hauth Hretired Hpages Hbytes Hstreams Hcont

/-- The generated allocation-failure tail delegates to the proved
`talos.oom` shim while preserving the pre-commit allocator state. -/
private theorem twp_func9_oom
    [WasmSmallStepGS hlc Universal.State]
    (size base finish requiredPages currentPages : UInt32)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) :
    iprop(
      RuntimeContext ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      (BumpHeap heapId storedCursor frontier history -∗
        Streams input output true -∗
        Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
        ⟨⟨[.i32 size, .i32 base],
            [.i32 finish, .i32 requiredPages, .i32 currentPages], []⟩,
          [.call 9, .unreachable], 1, [], [],
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hbump, Hstreams, Hcont⟩
  have Hoom := Project.Mergesort.ContractProofs.func6_correct (hlc := hlc)
      (input := input) (output := output) (raised := raised)
      (callerLocals := func9Locals size base finish requiredPages currentPages)
      (stack := []) (code := [.unreachable]) (arity := 1)
      (remainder := []) (controls := [])
      (calls :=
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ } :: calls)
      (s := s) (E := E) (Φ := Φ)
  unfold Func6Spec CallContract callExpr at Hoom
  simp only [List.nil_append] at Hoom ⊢
  iapply_splitl_exact Hoom with Hruntime
  iframe; iintro Hstreams
  iapply Hcont $$ Hbump Hstreams

/-- Generated `__rust_alloc_zeroed` satisfies its frozen contract. -/
theorem func9_correct [WasmSmallStepGS hlc Universal.State] :
    Func9Spec (hlc := hlc) := by
  unfold Func9Spec CallContract callExpr
  intro size alignment layout heapId storedCursor frontier history input output
    raised callerLocals stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hbump, Hstreams, %hlayout, Hcont⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.Mergesort.module 12
      Project.Mergesort.func9Def (by decide) func9_index with Hmodule
  simp [Project.Mergesort.func9Def, Project.Mergesort.func9,
    Function.toLocals, Function.numParams]
  have halignmentNat : alignment.toNat = 4 := by
    rw [hlayout.1.2, hlayout.2.2]
  have halignment : alignment = 4 := by
    apply UInt32.toNat_inj.mp
    simpa using halignmentNat
  subst alignment
  isimp only [BumpHeap] at Hbump
  icases Hbump with
    ⟨Hcursor, Hfrontier, Hauth, Hretired, Hheap⟩
  icases Hheap with ⟨%ownedPages, #Hpages, %hheap⟩
  rcases hheap with
    ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat, hwf,
      hfrontierPhysical⟩
  have hfrontierWord :
      (if storedCursor ≠ 0 then storedCursor else heapBase) =
        UInt32.ofNat frontier := by
    split
    · rename_i hnonzero
      apply UInt32.toNat_inj.mp
      rw [hcursorNat hnonzero,
        UInt32.toNat_ofNat_of_lt' (by
          norm_num [UInt32.size] at hfrontierSigned ⊢
          omega)]
    · rename_i hzero
      simp only [ne_eq, Decidable.not_not] at hzero
      have hfrontierEq := (hcursorZero.mp hzero).2
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_ofNat_of_lt' (by
        norm_num [UInt32.size] at hfrontierSigned ⊢
        omega)]
      exact hfrontierEq.symm
  have hsumBound : frontier + 3 < UInt32.size := by
    norm_num [UInt32.size] at hfrontierSigned ⊢
    omega
  have hsumWord : UInt32.ofNat frontier + 3 =
      UInt32.ofNat (frontier + 3) := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt'
      (by omega : frontier < UInt32.size),
      show (3 : UInt32).toNat = 3 by decide,
      UInt32.toNat_ofNat_of_lt' hsumBound]
    omega
  wasm_twp_pures [twp_block twp_localGet twp_const twp_add]
  norm_num
  wasm_twp_localTee [List.length]
  wasm_twp_pures [twp_const]
  ihave HcursorAt : pointsTo_u32 0 ((0 : UInt32) + 1049492)
      storedCursor $$ [Hcursor]
  · irw_exact [show (0 : UInt32) + 1049492 = allocatorCursor by decide] with Hcursor
  wasm_twp_bind twp_load32 (address := 0) (offset := 1049492) storedCursor
      (by decide) (by decide) (by decide) (by decide) with HcursorAt => Hcursor
  wasm_twp_localTee [List.length]
  wasm_twp_pures [twp_const twp_localGet]
  iapply twp_select
      (selected := .i32 (UInt32.ofNat frontier)) (by
        split
        · rename_i hnonzero
          rw [if_pos hnonzero] at hfrontierWord
          simpa only [if_pos hnonzero] using
            congrArg Value.i32 hfrontierWord.symm
        · rename_i hzero
          rw [if_neg hzero] at hfrontierWord
          simpa only [if_neg hzero, heapBase] using
            congrArg Value.i32 hfrontierWord.symm)
  wasm_twp_pures [twp_add] rewriting [show (4294967295 : UInt32) + 4 = 3 by decide, hsumWord]
  wasm_twp_localTee [List.length]
  wasm_twp_pures [twp_localGet]
  have hsumNotLt : ¬ UInt32.ofNat (frontier + 3) < (3 : UInt32) := by
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le_toNat,
      UInt32.toNat_ofNat_of_lt' hsumBound]
    change 3 ≤ frontier + 3
    omega
  have hsumRawNotLt : ¬ UInt32.ofNat frontier + 3 < (3 : UInt32) := by
    simpa only [hsumWord] using hsumNotLt
  iapply twp_ltU (result := 0) (by rw [if_neg hsumNotLt])
  wasm_twp_pures [twp_brIfZero]
  let base : UInt32 :=
    UInt32.ofNat (frontier + 3) &&& (0 - (4 : UInt32))
  let finishNat := base.toNat + layout.size
  let finish : UInt32 := UInt32.ofNat finishNat
  have hbaseBound : base.toNat ≤ frontier + 3 := by
    dsimp only [base]
    simpa only [UInt32.toNat_and, UInt32.toNat_ofNat_of_lt' hsumBound] using Nat.and_le_left
  have hsizeBound : layout.size ≤ 2147483644 := by
    simpa only [hlayout.2.2] using hlayout.2.1.2.2.2.2.1
  have hfinishWordBound : finishNat < UInt32.size := by
    dsimp only [finishNat]
    norm_num [UInt32.size] at hfrontierSigned hsizeBound ⊢
    omega
  have hsizeNat : size.toNat = layout.size := hlayout.1.1
  have hfinishWord : base + size = finish := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hsizeNat,
      Nat.mod_eq_of_lt hfinishWordBound]
    exact (UInt32.toNat_ofNat_of_lt' hfinishWordBound).symm
  have hfinishWord' : size + base = finish := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hsizeNat, Nat.add_comm,
      Nat.mod_eq_of_lt hfinishWordBound]
    exact (UInt32.toNat_ofNat_of_lt' hfinishWordBound).symm
  have hfinishRaw :
      size + (UInt32.ofNat (frontier + 3) &&& (-(4 : UInt32))) = finish := by
    simpa only [← show (0 : UInt32) - 4 = -(4 : UInt32) by decide] using hfinishWord'
  have hbaseLeFinish : base ≤ finish := by
    rw [UInt32.le_iff_toNat_le_toNat,
      UInt32.toNat_ofNat_of_lt' hfinishWordBound]
    dsimp only [finishNat]
    omega
  have hbaseLeFinishRaw :
      UInt32.ofNat (frontier + 3) &&& (-(4 : UInt32)) ≤ finish := by
    simpa only [← show (0 : UInt32) - 4 = -(4 : UInt32) by decide] using hbaseLeFinish
  have hfinishNatEq : finish.toNat = finishNat :=
    UInt32.toNat_ofNat_of_lt' hfinishWordBound
  wasm_twp_pures [twp_localGet twp_const twp_localGet twp_sub]
  norm_num
  iapply twp_and (lhs := UInt32.ofNat frontier + (3 : UInt32))
      (rhs := -(4 : UInt32))
  rw [hsumWord]
  wasm_twp_localTee [List.set]
  wasm_twp_pures [twp_localGet twp_add] rewriting [hfinishRaw]
  wasm_twp_localTee [List.length]
  wasm_twp_pures [twp_localGet]
  iapply twp_ltU (result := 0) (by
    rw [if_neg (UInt32.not_lt.mpr hbaseLeFinishRaw)])
  wasm_twp_pures [twp_brIfZero twp_localGet twp_const]
  by_cases hfinishFails : ¬ finishNat < 2147483648
  · have hfinishHigh : 2147483648 ≤ finishNat := by omega
    have hfinishNegative : finish.toInt32 < (0 : UInt32).toInt32 := by
      simp only [UInt32.toInt32, LT.lt, Int32.lt, Int32.toBitVec]
      rw [BitVec.slt_iff_toInt_lt]
      simp only [BitVec.toInt, Nat.reducePow]
      change (if 2 * finish.toNat < 4294967296 then
        (finish.toNat : Int) else (finish.toNat : Int) - 4294967296) < 0
      omega
    iapply twp_ltS (result := 1) (by rw [if_pos hfinishNegative])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    simp [ValueType.zero]
    have hclassify : classifyBump frontier layout = .oom := by
      unfold classifyBump
      simp only [hlayout.2.2, Nat.reduceSubDiff]
      rw [dif_pos hsumBound]
      rw [if_neg]
      intro hsuccess
      exact hfinishFails hsuccess.2
    isimp only [ZeroAllocContinuation, hclassify] at Hcont
    ihave Hbump : BumpHeap heapId storedCursor frontier history $$
        [Hcursor Hfrontier Hauth Hretired]
    · unfold BumpHeap
      ihave Hcursor' : pointsTo_u32 0 allocatorCursor storedCursor $$ [Hcursor]
      · irw_exact [allocatorCursor] with Hcursor
      iframe Hcursor' Hfrontier Hauth Hretired
      iexists ownedPages
      iframe Hpages
      ipureexact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat, hwf,
        hfrontierPhysical⟩
    iapply twp_func9_oom size
        ((UInt32.ofNat frontier + 3) &&& (-(4 : UInt32))) finish
        (UInt32.ofNat frontier + 3) 0 heapId storedCursor frontier history
        input output raised callerLocals stack code arity remainder controls
        calls s E Φ
    iframe Hbump Hstreams Hcont
    unfold RuntimeContext
    iframe Hmodule Henv
  · have hfinishSigned : finishNat < 2147483648 := by omega
    have hfinishNonnegative : ¬ finish.toInt32 < (0 : UInt32).toInt32 := by
      simp only [UInt32.toInt32, LT.lt, Int32.lt, Int32.toBitVec]
      rw [BitVec.slt_iff_toInt_lt]
      simp only [BitVec.toInt, Nat.reducePow]
      change ¬ (if 2 * finish.toNat < 4294967296 then
        (finish.toNat : Int) else (finish.toNat : Int) - 4294967296) < 0
      omega
    iapply twp_ltS (result := 0) (by rw [if_neg hfinishNonnegative])
    wasm_twp_pures [twp_brIfZero]
    have hclassify :
        classifyBump frontier layout = .success base finish := by
      unfold classifyBump
      simp only [hlayout.2.2, Nat.reduceSubDiff]
      rw [dif_pos hsumBound]
      rw [if_pos ⟨hfinishWordBound, hfinishSigned⟩]
      rfl
    isimp only [ZeroAllocContinuation, hclassify] at Hcont
    wasm_twp_pures [twp_block]
    simp [ValueType.zero]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (65535 : UInt32) finish]
    wasm_twp_pures [twp_const twp_shrU] rewriting [show (16 : UInt32) % 32 = 16 by decide]
    rw [show (finish + 65535) >>> (16 : UInt32) =
      allocatorRequiredPages finish by rfl]
    wasm_twp_localTee [List.length, List.set]
    have hfinishSignedWord : finish.toNat < 2147483648 := by
      simpa only [hfinishNatEq] using hfinishSigned
    have hrequiredCovers :=
      allocatorRequiredPages_covers finish hfinishSignedWord
    rcases classifyBump_success_reachable frontier layout base finish
        hfrontierLow hlayout.2.1 (Or.inr hlayout.2.2) hclassify with
      ⟨hbaseFresh, hbaseNonzero, hbaseAligned, hallocWord, hallocSigned,
        hfinishExact, hmeta⟩
    have hbaseRaw :
        (UInt32.ofNat frontier + 3) &&& (-(4 : UInt32)) = base := by
      rw [hsumWord]
      rfl
    rw [hbaseRaw]
    ihave HcursorAlloc : pointsTo_u32 0 allocatorCursor storedCursor $$ [Hcursor]
    · irw_exact [allocatorCursor] with Hcursor
    ihave HsizeFrame : iprop(
        hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
        pointsTo_u32 0 allocatorCursor storedCursor ∗
        heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
        RetiredBytes heapId history ∗ memoryPagesOwn ownedPages ∗
        Streams input output raised ∗
        ((RuntimeContext -∗
            BumpHeap heapId finish finish.toNat
              (history.allocate base layout) -∗
            LiveBlock heapId history.nextId base layout
              (List.replicate layout.size 0) -∗
            Streams input output raised -∗
            ResumeWP [.i32 base] callerLocals stack code arity remainder
              controls calls s E Φ) ∧
          (BumpHeap heapId storedCursor frontier history -∗
            Streams input output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) $$
        [Henv HcursorAlloc Hfrontier Hauth Hretired Hpages Hstreams Hcont]
    · iframe
      iexact Hpages
    iapply twp_memorySize_tracked Project.Mergesort.module ⟨0⟩
        $$ HsizeFrame Hmodule
    iintro %pages HsizeFrame Hmodule Hmeasured
    icases HsizeFrame with
      ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, Hpages, Hstreams, Hcont⟩
    simp only [show Project.Mergesort.module.memIs64 = false by rfl,
      sizeValue, Bool.false_eq_true, ↓reduceIte]
    wasm_twp_pures [twp_localTee]
    simp
    by_cases hfits : allocatorRequiredPages finish ≤ pages.toUInt32
    · iapply twp_leU (result := 1) (by rw [if_pos hfits])
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.nil_append]
      have hpagesWord : pages.toUInt32.toNat ≤ pages := by
        unfold Nat.toUInt32 UInt32.toNat UInt32.ofNat
        simp only [BitVec.toNat_ofNat]
        exact Nat.mod_le _ _
      have hphysical : finish.toNat ≤ pages * 65536 :=
        _root_.le_trans hrequiredCovers (Nat.mul_le_mul_right 65536
          (_root_.le_trans
            (UInt32.le_iff_toNat_le_toNat.mp hfits) hpagesWord))
      ihave Hnormal := BI.and_elim_l $$ Hcont
      iclose_runtime Hruntime with Hmodule Henv
      have Hclaim := twp_func9_claim_commit_zero_and_return size base finish
          (allocatorRequiredPages finish) pages.toUInt32 storedCursor layout
          heapId frontier pages history input output raised
          [{ kind := .block
             paramArity := 0
             resultArity := 0
             body := func9ArithmeticPrefix ++ func9PostArithmetic
             continuation := [.call 9, .unreachable]
             belowStack := [] }]
          controls calls callerLocals stack code arity remainder s E Φ
          hfrontierLow hwf hlayout.1 hlayout.2.1 hclassify hbaseFresh
          hallocWord hfinishExact hphysical
      simp only [func9Locals, func9ZeroBody, func9ArithmeticPrefix,
        func9PostArithmetic, func9GrowthBody, allocatorCursor, heapBase,
        Nat.toUInt32, List.cons_append, List.nil_append] at Hclaim
      ihave HcursorRaw : pointsTo_u32 0 (1049492 : UInt32) storedCursor $$
          [Hcursor]
      · irw_exact [show (1049492 : UInt32) = allocatorCursor by decide] with Hcursor
      iapply Hclaim
      iframe Hruntime HcursorRaw Hfrontier Hauth Hretired Hmeasured Hstreams
        Hnormal
    · iapply twp_leU (result := 0) (by rw [if_neg hfits])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_sub]
      let delta := allocatorRequiredPages finish - pages.toUInt32
      ihave HgrowFrame : iprop(
          hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
          pointsTo_u32 0 allocatorCursor storedCursor ∗
          heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
          RetiredBytes heapId history ∗ memoryPagesOwn ownedPages ∗
          Streams input output raised ∗
          ((RuntimeContext -∗
              BumpHeap heapId finish finish.toNat
                (history.allocate base layout) -∗
              LiveBlock heapId history.nextId base layout
                (List.replicate layout.size 0) -∗
              Streams input output raised -∗
              ResumeWP [.i32 base] callerLocals stack code arity remainder
                controls calls s E Φ) ∧
            (BumpHeap heapId storedCursor frontier history -∗
              Streams input output true -∗
              Φ (.trapped (.host OOM.trapMessage))))) $$
          [Henv Hcursor Hfrontier Hauth Hretired Hpages Hstreams Hcont]
      · iframe
      iapply twp_memoryGrow_tracked Project.Mergesort.module ⟨0⟩ pages
          (fun actualPages hmeasured => by
            iintro HgrowFrame Hmodule Hmeasured
            icases HgrowFrame with
              ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldPages,
                Hstreams, Hcont⟩
            wasm_twp_pures [twp_const]
            iapply twp_eq (result := 1) (by simp)
            iapply twp_brIf (by decide) (by rfl)
            simp only [List.take_zero, List.nil_append]
            ihave Hbump : BumpHeap heapId storedCursor frontier history $$
                [Hcursor Hfrontier Hauth Hretired HoldPages]
            · unfold BumpHeap
              iframe_pureexact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat,
                hwf, hfrontierPhysical⟩
            iclose_runtime Hruntime with Hmodule Henv
            ihave Hoom := BI.and_elim_r $$ Hcont
            iapply twp_func9_oom size base finish
                (allocatorRequiredPages finish) pages.toUInt32 heapId
                storedCursor frontier history input output raised callerLocals
                stack code arity remainder controls calls s E Φ
            iframe Hruntime Hbump Hstreams Hoom)
          (fun oldPages previousPages newPages hfacts hmeasured => by
            iintro HgrowFrame Hmodule HMeasured HnewPages
            icases HgrowFrame with
              ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldPages,
                Hstreams, Hcont⟩
            wasm_twp_pures [twp_const]
            by_cases hsentinel : previousPages.toUInt32 =
                (0xFFFFFFFF : UInt32)
            · iapply twp_eq (result := 1) (by simp [hsentinel])
              iapply twp_brIf (by decide) (by rfl)
              simp only [List.take_zero, List.nil_append]
              ihave Hbump : BumpHeap heapId storedCursor frontier history $$
                  [Hcursor Hfrontier Hauth Hretired HoldPages]
              · unfold BumpHeap
                iframe_pureexact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat,
                  hwf, hfrontierPhysical⟩
              iclose_runtime Hruntime with Hmodule Henv
              ihave Hoom := BI.and_elim_r $$ Hcont
              iapply twp_func9_oom size base finish
                  (allocatorRequiredPages finish) pages.toUInt32 heapId
                  storedCursor frontier history input output raised callerLocals
                  stack code arity remainder controls calls s E Φ
              iframe Hruntime Hbump Hstreams Hoom
            · iapply twp_eq (result := 0) (by simp [hsentinel])
              wasm_twp_pures [twp_brIfZero twp_exitControl] using [List.take_zero, List.nil_append]
              have hphysical : finish.toNat ≤ newPages * 65536 := by
                by_cases hpagesLow : pages < UInt32.size
                · have hpagesWord : pages.toUInt32.toNat = pages := by
                    unfold Nat.toUInt32
                    exact UInt32.toNat_ofNat_of_lt' hpagesLow
                  have hpagesLtRequired :
                      pages < (allocatorRequiredPages finish).toNat := by
                    rw [← hpagesWord]
                    exact UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hfits)
                  have hdeltaNat : delta.toNat =
                      (allocatorRequiredPages finish).toNat - pages := by
                    dsimp only [delta]
                    rw [UInt32.toNat_sub_of_le]
                    · rw [hpagesWord]
                    · rw [UInt32.le_iff_toNat_le_toNat, hpagesWord]
                      omega
                  have hrequiredLeNew :
                      (allocatorRequiredPages finish).toNat ≤ newPages := by
                    rw [hfacts.2, hdeltaNat]
                    omega
                  exact hrequiredCovers.trans
                    (Nat.mul_le_mul_right 65536 hrequiredLeNew)
                · have hpagesHigh : UInt32.size ≤ pages := by omega
                  have hfinishLeNew : finish.toNat ≤ newPages := by
                    rw [hfacts.2]
                    norm_num [UInt32.size] at hpagesHigh
                    omega
                  exact hfinishLeNew.trans (by omega)
              ihave Hnormal := BI.and_elim_l $$ Hcont
              iclose_runtime Hruntime with Hmodule Henv
              have Hclaim := twp_func9_claim_commit_zero_and_return size base
                  finish
                  (allocatorRequiredPages finish) pages.toUInt32 storedCursor
                  layout heapId frontier newPages history input output raised
                  [{ kind := .block
                     paramArity := 0
                     resultArity := 0
                     body := func9ArithmeticPrefix ++ func9PostArithmetic
                     continuation := [.call 9, .unreachable]
                     belowStack := [] }]
                  controls calls callerLocals stack code arity remainder s E Φ
                  hfrontierLow hwf hlayout.1 hlayout.2.1 hclassify hbaseFresh
                  hallocWord hfinishExact hphysical
              simp only [func9Locals, func9ZeroBody, func9ArithmeticPrefix,
                func9PostArithmetic, func9GrowthBody, allocatorCursor,
                heapBase, Nat.toUInt32, List.cons_append, List.nil_append] at Hclaim
              ihave HcursorRaw : pointsTo_u32 0 (1049492 : UInt32)
                  storedCursor $$ [Hcursor]
              · irw_exact [show (1049492 : UInt32) = allocatorCursor by decide] with Hcursor
              iapply Hclaim
              iframe Hruntime HcursorRaw Hfrontier Hauth Hretired HnewPages
                Hstreams Hnormal)
          $$ HgrowFrame Hmodule Hmeasured
end Project.Mergesort.Func9Proof
