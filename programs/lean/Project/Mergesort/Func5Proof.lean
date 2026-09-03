import Project.Mergesort.ContractProofs

/-!
# Proof of the generated bump allocator

This module proves the ordinary generated allocator against `Func5Spec`,
including its successful bump-allocation result and its precise `talos.oom`
terminal outcome when arithmetic checks or `memory.grow` fail.
-/

namespace Project.Mergesort.Func5Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

private theorem func5_index :
    Project.Mergesort.module.funcs[5]? =
      some Project.Mergesort.func5Def := by
  rfl

private abbrev func5ArithmeticPrefix : Program :=
  [.localGet 1, .const 0xFFFFFFFF, .add, .localTee 2,
    .const 0, .load32 allocatorCursor, .localTee 3,
    .const heapBase, .localGet 3, .select, .add, .localTee 3,
    .localGet 2, .ltU, .br_if 0,
    .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 2,
    .localGet 0, .add, .localTee 1,
    .localGet 2, .ltU, .br_if 0,
    .localGet 1, .const 0, .ltS, .br_if 0]

private abbrev func5GrowthTail : Program :=
  [.localGet 1, .const 65535, .add, .const 16, .shrU,
    .localTee 3, .memorySize, .localTee 0, .leU, .br_if 1,
    .localGet 3, .localGet 0, .sub, .memoryGrow,
    .const 0xFFFFFFFF, .ne, .br_if 1]

private abbrev func5InnerBody : Program :=
  func5ArithmeticPrefix ++ func5GrowthTail

private abbrev func5OuterBody : Program :=
  [.block 0 0 func5InnerBody, .call 9, .unreachable]

private abbrev func5CommitTail : Program :=
  [.const 0, .localGet 1, .store32 1049492, .localGet 2]

private abbrev func5Locals
    (first finish base requiredPages : UInt32)
    (values : List Value := []) : Locals :=
  { params := [.i32 first, .i32 finish]
    locals := [.i32 base, .i32 requiredPages]
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

/-- Commit a physically claimed range and return the fresh block unchanged. -/
private theorem twp_func5_commit_and_return
    [WasmSmallStepGS hlc Universal.State]
    (currentPages finish base requiredPages storedCursor : UInt32)
    (layout : AllocLayout) (heapId : GName)
    (bytes : List UInt8) (frontier ownedPages : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hfrontierLow : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hvalid : layout.Valid)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
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
      (∀ resultBytes : List UInt8,
        RuntimeContext -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout resultBytes -∗
        Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func5Locals currentPages finish base requiredPages [.i32 0],
          [.localGet 1, .store32 1049492, .localGet 2],
          1, [], [],
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
  imod BumpHeap_commit heapId frontier history base finish layout bytes
      ownedPages hfrontierLow hwf hvalid halignment hclassify hbytesLength
      hphysical $$ [Hcursor' Hfrontier Hauth Hretired Hpages Hbytes] with
      ⟨Hbump, Hblock⟩
  · iframe
  wasm_twp_pures [twp_localGet]
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  ispecialize Hcont $$ %bytes
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.cons_append,
    List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule Henv] Hbump Hblock Hstreams
  · isplitl_exact Hmodule
    · iexact Henv

/-- Claim the checked physical range, then commit and return it. -/
private theorem twp_func5_claim_commit_and_return
    [WasmSmallStepGS hlc Universal.State]
    (currentPages finish base requiredPages storedCursor : UInt32)
    (layout : AllocLayout) (heapId : GName)
    (frontier ownedPages : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hfrontierLow : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hvalid : layout.Valid)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
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
      (∀ resultBytes : List UInt8,
        RuntimeContext -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout resultBytes -∗
        Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func5Locals currentPages finish base requiredPages,
          func5CommitTail, 1, [], [],
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
    rw [← hfinishExact]
    exact hphysical
  ihave HclaimFrame : iprop(
      RuntimeContext ∗ pointsTo_u32 0 allocatorCursor storedCursor ∗
      AllocMetaAuth heapId history ∗ RetiredBytes heapId history ∗
      Streams input output raised ∗
      (∀ resultBytes : List UInt8,
        RuntimeContext -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout resultBytes -∗
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
  iapply twp_func5_commit_and_return currentPages finish base requiredPages
      storedCursor layout heapId bytes frontier ownedPages history input output
      raised callerLocals stack code arity remainder controls calls s E Φ
      hfrontierLow hwf hvalid halignment hclassify hbytes hphysical
  iframe Hruntime Hcursor Hfrontier' Hauth Hretired Hpages Hbytes Hstreams Hcont

/-- Delegate the generated failure tail to the proved `talos.oom` shim. -/
private theorem twp_func5_oom
    [WasmSmallStepGS hlc Universal.State]
    (first finish base requiredPages : UInt32)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (functionControls controls : List ControlFrame) (calls : List CallFrame)
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
        ⟨func5Locals first finish base requiredPages,
          [.call 9, .unreachable], 1, [], functionControls,
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
      (callerLocals := func5Locals first finish base requiredPages)
      (stack := []) (code := [.unreachable]) (arity := 1)
      (remainder := []) (controls := functionControls)
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
  iapply Hoom
  isplitl_exact Hruntime
  iframe; iintro Hstreams
  iapply Hcont $$ Hbump Hstreams

theorem func5_correct [WasmSmallStepGS hlc Universal.State] :
    Func5Spec (hlc := hlc) := by
  unfold Func5Spec CallContract callExpr
  intro size alignment layout heapId storedCursor frontier history input output
    raised callerLocals stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hbump, Hstreams, %hlayout, Hcont⟩
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.Mergesort.module 8
      Project.Mergesort.func5Def (by decide) func5_index with Hmodule
  simp [Project.Mergesort.func5Def, Project.Mergesort.func5,
    Function.toLocals, Function.numParams]
  have hvalid : layout.Valid := hlayout.2.1
  have halignmentCases : layout.alignment = 1 ∨ layout.alignment = 4 :=
    hlayout.2.2
  have hsizeNat : size.toNat = layout.size := hlayout.1.1
  have halignmentNat : alignment.toNat = layout.alignment := hlayout.1.2
  have halignmentWord : alignment = UInt32.ofNat layout.alignment := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_ofNat_of_lt' hvalid.2.2.2.2.2.2]
    exact halignmentNat
  have halignmentSmall : layout.alignment ≤ 4 := by
    rcases halignmentCases with h | h <;> omega
  have hpadSmall : layout.alignment - 1 ≤ 3 := by omega
  isimp only [BumpHeap] at Hbump
  icases Hbump with ⟨Hcursor, Hfrontier, Hauth, Hretired, Hheap⟩
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
  have hsumBound :
      frontier + (layout.alignment - 1) < UInt32.size := by
    norm_num [UInt32.size] at hfrontierSigned ⊢
    omega
  have hpadWord :
      (0xFFFFFFFF : UInt32) + alignment =
        UInt32.ofNat (layout.alignment - 1) := by
    rcases halignmentCases with h | h
    · rw [halignmentWord, h]
      decide
    · rw [halignmentWord, h]
      decide
  have hsumWord :
      UInt32.ofNat frontier + UInt32.ofNat (layout.alignment - 1) =
        UInt32.ofNat (frontier + (layout.alignment - 1)) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add,
      UInt32.toNat_ofNat_of_lt' (by
        norm_num [UInt32.size] at hfrontierSigned ⊢
        omega),
      UInt32.toNat_ofNat_of_lt' (by
        exact Nat.lt_of_le_of_lt hpadSmall (by decide)),
      UInt32.toNat_ofNat_of_lt' hsumBound,
      Nat.mod_eq_of_lt hsumBound]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_const twp_add]
  rw [hpadWord]
  wasm_twp_pures [twp_localTee]
  simp only [List.length]
  wasm_twp_pures [twp_const]
  ihave HcursorAt : pointsTo_u32 0 ((0 : UInt32) + 1049492)
      storedCursor $$ [Hcursor]
  · irw_exact [show (0 : UInt32) + 1049492 = allocatorCursor by decide] with Hcursor
  wasm_twp_bind twp_load32 (address := 0) (offset := 1049492) storedCursor
      (by decide) (by decide) (by decide) (by decide) with HcursorAt => Hcursor
  wasm_twp_pures [twp_localTee]
  simp only [List.length]
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
  wasm_twp_pures [twp_add]
  rw [hsumWord]
  wasm_twp_pures [twp_localTee]
  simp only [List.length]
  wasm_twp_pures [twp_localGet]
  have hsumNotLt :
      ¬ UInt32.ofNat (frontier + (layout.alignment - 1)) <
        UInt32.ofNat (layout.alignment - 1) := by
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le_toNat,
      UInt32.toNat_ofNat_of_lt' hsumBound,
      UInt32.toNat_ofNat_of_lt' (by
        exact Nat.lt_of_le_of_lt hpadSmall (by decide))]
    omega
  iapply twp_ltU (result := 0) (by rw [if_neg hsumNotLt])
  wasm_twp_pures [twp_brIfZero]
  let base : UInt32 :=
    UInt32.ofNat (frontier + (layout.alignment - 1)) &&&
      (0 - UInt32.ofNat layout.alignment)
  let finishNat := base.toNat + layout.size
  let finish : UInt32 := UInt32.ofNat finishNat
  have hbaseBound :
      base.toNat ≤ frontier + (layout.alignment - 1) := by
    dsimp only [base]
    rw [UInt32.toNat_and, UInt32.toNat_ofNat_of_lt' hsumBound]
    exact Nat.and_le_left
  have hfinishWordBound : finishNat < UInt32.size := by
    dsimp only [finishNat]
    have hsizeBound := hvalid.2.2.2.2.1
    norm_num [UInt32.size] at hfrontierSigned hsizeBound ⊢
    omega
  have hfinishWord : base + size = finish := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hsizeNat, Nat.mod_eq_of_lt hfinishWordBound]
    exact (UInt32.toNat_ofNat_of_lt' hfinishWordBound).symm
  have hfinishWord' : size + base = finish := by
    rw [UInt32.add_comm]
    exact hfinishWord
  have hbaseRaw :
      UInt32.ofNat (frontier + (layout.alignment - 1)) &&&
          (0 - alignment) = base := by
    rw [halignmentWord]
  have hfinishRaw :
      size +
          (UInt32.ofNat (frontier + (layout.alignment - 1)) &&&
            (0 - alignment)) = finish := by
    rw [hbaseRaw]
    exact hfinishWord'
  have hbaseLeFinish : base ≤ finish := by
    rw [UInt32.le_iff_toNat_le_toNat,
      UInt32.toNat_ofNat_of_lt' hfinishWordBound]
    dsimp only [finishNat]
    omega
  have hfinishNatEq : finish.toNat = finishNat :=
    UInt32.toNat_ofNat_of_lt' hfinishWordBound
  have hfinishWordBoundNumeric : finishNat < 4294967296 := by
    simpa [UInt32.size] using hfinishWordBound
  ihave HcursorAlloc : pointsTo_u32 0 allocatorCursor storedCursor $$ [Hcursor]
  · irw_exact [← show (0 : UInt32) + 1049492 = allocatorCursor by decide] with Hcursor
  wasm_twp_pures [twp_localGet twp_const twp_localGet twp_sub twp_and]
  rw [hbaseRaw]
  wasm_twp_pures [twp_localTee]
  simp only [List.length]
  wasm_twp_pures [twp_localGet twp_add]
  rw [hfinishWord']
  wasm_twp_pures [twp_localTee]
  simp only [List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_ltU (result := 0) (by
    rw [if_neg (UInt32.not_lt.mpr hbaseLeFinish)])
  wasm_twp_pures [twp_brIfZero twp_localGet twp_const]
  by_cases hfinishFails : ¬ finishNat < 2147483648
  · have hfinishHigh : 2147483648 ≤ finishNat := by omega
    have hfinishNegative : finish.toInt32 < (0 : UInt32).toInt32 := by
      simp only [UInt32.toInt32, LT.lt, Int32.lt, Int32.toBitVec]
      rw [BitVec.slt_iff_toInt_lt]
      simp only [BitVec.toInt, Nat.reducePow]
      change (if 2 * finish.toNat < 4294967296 then
        (finish.toNat : Int) else (finish.toNat : Int) - 4294967296) < 0
      rw [hfinishNatEq]
      omega
    iapply twp_ltS (result := 1) (by rw [if_pos hfinishNegative])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    simp [ValueType.zero]
    rw [hsumWord]
    have hclassify : classifyBump frontier layout = .oom := by
      unfold classifyBump
      rw [dif_pos hsumBound]
      simp only
      rw [if_neg]
      intro hsuccess
      exact hfinishFails hsuccess.2
    isimp only [AllocContinuation, hclassify] at Hcont
    ihave Hbump : BumpHeap heapId storedCursor frontier history $$
        [HcursorAlloc Hfrontier Hauth Hretired Hpages]
    · unfold BumpHeap
      iframe HcursorAlloc Hfrontier Hauth Hretired
      iexists ownedPages
      iframe Hpages
      ipureexact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat, hwf,
        hfrontierPhysical⟩
    ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
    · unfold RuntimeContext
      iframe Hmodule Henv
    have Hfailure := twp_func5_oom size finish base
        (UInt32.ofNat (frontier + (layout.alignment - 1))) heapId storedCursor
        frontier history input output raised callerLocals stack code arity
        remainder
        [{ kind := .block
           paramArity := 0
           resultArity := 0
           body := func5OuterBody
           continuation := func5CommitTail
           belowStack := [] }]
        controls calls s E Φ
    simp only [func5Locals, func5OuterBody, func5InnerBody,
      func5ArithmeticPrefix, func5GrowthTail, func5CommitTail,
      allocatorCursor, heapBase, List.cons_append, List.nil_append] at Hfailure
    iapply Hfailure
    iframe Hruntime Hbump Hstreams Hcont
  · have hfinishSigned : finishNat < 2147483648 := by omega
    have hfinishNonnegative : ¬ finish.toInt32 < (0 : UInt32).toInt32 := by
      simp only [UInt32.toInt32, LT.lt, Int32.lt, Int32.toBitVec]
      rw [BitVec.slt_iff_toInt_lt]
      simp only [BitVec.toInt, Nat.reducePow]
      change ¬ (if 2 * finish.toNat < 4294967296 then
        (finish.toNat : Int) else (finish.toNat : Int) - 4294967296) < 0
      rw [hfinishNatEq]
      omega
    iapply twp_ltS (result := 0) (by rw [if_neg hfinishNonnegative])
    wasm_twp_pures [twp_brIfZero]
    have hclassify :
        classifyBump frontier layout = .success base finish := by
      unfold classifyBump
      rw [dif_pos hsumBound]
      simp only
      rw [if_pos ⟨hfinishWordBound, hfinishSigned⟩]
    isimp only [AllocContinuation, hclassify] at Hcont
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [UInt32.add_comm (65535 : UInt32) finish]
    wasm_twp_pures [twp_const twp_shrU]
    rw [show (16 : UInt32) % 32 = 16 by decide]
    rw [show (finish + 65535) >>> (16 : UInt32) =
      allocatorRequiredPages finish by rfl]
    wasm_twp_pures [twp_localTee]
    simp only [List.length]
    have hfinishSignedWord : finish.toNat < 2147483648 := by
      rw [hfinishNatEq]
      exact hfinishSigned
    have hrequiredCovers :=
      allocatorRequiredPages_covers finish hfinishSignedWord
    rcases classifyBump_success_reachable frontier layout base finish
        hfrontierLow hvalid halignmentCases hclassify with
      ⟨hbaseFresh, hbaseNonzero, hbaseAligned, hallocWord, hallocSigned,
        hfinishExact, hmeta⟩
    ihave HsizeFrame : iprop(
        hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
        pointsTo_u32 0 allocatorCursor storedCursor ∗
        heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
        RetiredBytes heapId history ∗ memoryPagesOwn ownedPages ∗
        Streams input output raised ∗
        ((∀ resultBytes : List UInt8,
            RuntimeContext -∗
            BumpHeap heapId finish finish.toNat
              (history.allocate base layout) -∗
            LiveBlock heapId history.nextId base layout resultBytes -∗
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
      ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      iapply twp_func5_claim_commit_and_return pages.toUInt32 finish base
          (allocatorRequiredPages finish) storedCursor layout heapId frontier
          pages history input output raised callerLocals stack code arity
          remainder controls calls s E Φ hfrontierLow hwf hvalid
          halignmentCases hclassify hbaseFresh hallocWord hfinishExact hphysical
      iframe Hruntime Hcursor Hfrontier Hauth Hretired Hmeasured Hstreams Hnormal
    · iapply twp_leU (result := 0) (by rw [if_neg hfits])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_sub]
      let delta := allocatorRequiredPages finish - pages.toUInt32
      ihave HgrowFrame : iprop(
          hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
          pointsTo_u32 0 allocatorCursor storedCursor ∗
          heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
          RetiredBytes heapId history ∗ memoryPagesOwn ownedPages ∗
          Streams input output raised ∗
          ((∀ resultBytes : List UInt8,
              RuntimeContext -∗
              BumpHeap heapId finish finish.toNat
                (history.allocate base layout) -∗
              LiveBlock heapId history.nextId base layout resultBytes -∗
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
            iintro HgrowFrame Hmodule HMeasured
            icases HgrowFrame with
              ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldPages,
                Hstreams, Hcont⟩
            wasm_twp_pures [twp_const]
            iapply twp_ne (result := 0) (by simp)
            wasm_twp_pures [twp_brIfZero twp_exitControl]
            simp only [List.take_zero, List.nil_append]
            ihave Hbump : BumpHeap heapId storedCursor frontier history $$
                [Hcursor Hfrontier Hauth Hretired HoldPages]
            · unfold BumpHeap
              iframe
              ipureexact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat,
                hwf, hfrontierPhysical⟩
            ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
            · unfold RuntimeContext
              iframe Hmodule Henv
            ihave Hoom := BI.and_elim_r $$ Hcont
            have Hfailure := twp_func5_oom pages.toUInt32 finish base
                (allocatorRequiredPages finish) heapId storedCursor frontier
                history input output raised callerLocals stack code arity
                remainder
                [{ kind := .block
                   paramArity := 0
                   resultArity := 0
                   body := func5OuterBody
                   continuation := func5CommitTail
                   belowStack := [] }]
                controls calls s E Φ
            simp only [func5Locals, func5OuterBody, func5InnerBody,
              func5ArithmeticPrefix, func5GrowthTail, func5CommitTail,
              allocatorCursor, heapBase, Nat.toUInt32, List.cons_append,
              List.nil_append] at Hfailure
            iapply Hfailure
            iframe Hruntime Hbump Hstreams Hoom)
          (fun oldPages previousPages newPages hfacts hmeasured => by
            iintro HgrowFrame Hmodule HMeasured HnewPages
            icases HgrowFrame with
              ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldPages,
                Hstreams, Hcont⟩
            wasm_twp_pures [twp_const]
            by_cases hsentinel : previousPages.toUInt32 =
                (0xFFFFFFFF : UInt32)
            · iapply twp_ne (result := 0) (by simp [hsentinel])
              wasm_twp_pures [twp_brIfZero twp_exitControl]
              simp only [List.take_zero, List.nil_append]
              ihave Hbump : BumpHeap heapId storedCursor frontier history $$
                  [Hcursor Hfrontier Hauth Hretired HoldPages]
              · unfold BumpHeap
                iframe
                ipureexact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat,
                  hwf, hfrontierPhysical⟩
              ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
              · unfold RuntimeContext
                iframe Hmodule Henv
              ihave Hoom := BI.and_elim_r $$ Hcont
              have Hfailure := twp_func5_oom pages.toUInt32 finish base
                  (allocatorRequiredPages finish) heapId storedCursor frontier
                  history input output raised callerLocals stack code arity
                  remainder
                  [{ kind := .block
                     paramArity := 0
                     resultArity := 0
                     body := func5OuterBody
                     continuation := func5CommitTail
                     belowStack := [] }]
                  controls calls s E Φ
              simp only [func5Locals, func5OuterBody, func5InnerBody,
                func5ArithmeticPrefix, func5GrowthTail, func5CommitTail,
                allocatorCursor, heapBase, Nat.toUInt32, List.cons_append,
                List.nil_append] at Hfailure
              iapply Hfailure
              iframe Hruntime Hbump Hstreams Hoom
            · iapply twp_ne (result := 1) (by simp [hsentinel])
              iapply twp_brIf (by decide) (by rfl)
              simp only [List.take_zero, List.nil_append]
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
              ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
              · unfold RuntimeContext
                iframe Hmodule Henv
              iapply twp_func5_claim_commit_and_return pages.toUInt32 finish
                  base (allocatorRequiredPages finish) storedCursor layout
                  heapId frontier newPages history input output raised
                  callerLocals stack code arity remainder controls calls s E Φ
                  hfrontierLow hwf hvalid halignmentCases hclassify hbaseFresh
                  hallocWord hfinishExact hphysical
              iframe Hruntime Hcursor Hfrontier Hauth Hretired HnewPages
                Hstreams Hnormal)
          $$ HgrowFrame Hmodule Hmeasured

end Project.Mergesort.Func5Proof
