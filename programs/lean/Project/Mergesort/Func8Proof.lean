import Project.Mergesort.ContractProofs

/-!
# Proof of the bump reallocator contract

This module isolates the proof of generated local `func8` (absolute Wasm
function index 11).  The body repeats the bump-allocation sequence, copies the
shorter old/new prefix, and logically retires the old allocation.
-/

namespace Project.Mergesort.Func8Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

private theorem func8_index :
    Project.Mergesort.module.funcs[8]? =
      some Project.Mergesort.func8Def := by
  rfl

private abbrev func8CopyBody : Program :=
  [.localGet 2, .eqz, .br_if 0,
    .localGet 3, .localGet 1, .localGet 3, .localGet 1, .ltU,
    .select, .localTee 4, .eqz, .br_if 0,
    .localGet 2, .localGet 0, .localGet 4, .memoryCopy]

private abbrev func8Locals
    (oldPtr oldSize newPtr newSize temp requiredPages currentPages : UInt32)
    (values : List Value := []) : Locals :=
  { params := [.i32 oldPtr, .i32 oldSize, .i32 newPtr, .i32 newSize]
    locals := [.i32 temp, .i32 requiredPages, .i32 currentPages]
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

private abbrev func8ArithmeticPrefix : Program :=
  [.localGet 2, .const 0xFFFFFFFF, .add, .localTee 4,
    .const 0, .load32 allocatorCursor, .localTee 5,
    .const heapBase, .localGet 5, .select, .add, .localTee 5,
    .localGet 4, .ltU, .br_if 0,
    .localGet 5, .const 0, .localGet 2, .sub, .and, .localTee 2,
    .localGet 3, .add, .localTee 4,
    .localGet 2, .ltU, .br_if 0,
    .localGet 4, .const 0, .ltS, .br_if 0]

private abbrev func8GrowthBody : Program :=
  [.localGet 4, .const 65535, .add, .const 16, .shrU,
    .localTee 5, .memorySize, .localTee 6, .leU, .br_if 0,
    .localGet 5, .localGet 6, .sub, .memoryGrow,
    .const 0xFFFFFFFF, .eq, .br_if 1]

private abbrev func8PostArithmetic : Program :=
  [.block 0 0 func8GrowthBody,
    .const 0, .localGet 4, .store32 allocatorCursor,
    .block 0 0 func8CopyBody, .localGet 2, .ret]

private theorem func8_shape :
    Project.Mergesort.func8 =
      [.block 0 0 (func8ArithmeticPrefix ++ func8PostArithmetic),
        .call 9, .unreachable] := by
  rfl

/-- The post-commit tail copies the whole old allocation, retires it, and
returns the new pointer.  All allocation arithmetic and memory growth have
already completed before this lemma starts. -/
private theorem twp_func8_copy_and_return
    [WasmSmallStepGS hlc Universal.State]
    (oldPtr oldSize newPtr newSize : UInt32)
    (oldLayout newLayout : AllocLayout)
    (heapId : GName) (oldId : Nat)
    (oldBytes newBytes : List UInt8)
    (finish : UInt32) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (temp requiredPages currentPages : UInt32)
    (currentControls : List ControlFrame)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hlayout : oldLayout.Matches oldSize 1 ∧
      newLayout.Matches newSize 1 ∧
      oldLayout.Valid ∧ newLayout.Valid ∧
      oldLayout.alignment = 1 ∧ oldLayout.size < newLayout.size) :
    iprop(
      RuntimeContext ∗
      BumpHeap heapId finish finish.toNat
        (history.allocate newPtr newLayout) ∗
      LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
      LiveBlock heapId history.nextId newPtr newLayout newBytes ∗
      Streams input output raised ∗
      (∀ finalBytes : List UInt8,
        RuntimeContext -∗
        BumpHeap heapId finish finish.toNat
          (history.reallocate oldId oldPtr oldLayout newPtr newLayout) -∗
        LiveBlock heapId history.nextId newPtr newLayout finalBytes -∗
        ⌜finalBytes.take (min oldLayout.size newLayout.size) =
          oldBytes.take (min oldLayout.size newLayout.size)⌝ -∗
        Streams input output raised -∗
        ResumeWP [.i32 newPtr] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func8Locals oldPtr oldSize newPtr newSize temp requiredPages currentPages,
          [.block 0 0 func8CopyBody, .localGet 2, .ret], 1, [],
          currentControls,
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  have holdSize : oldSize.toNat = oldLayout.size := hlayout.1.1
  have hnewSize : newSize.toNat = newLayout.size := hlayout.2.1.1
  have holdLt : oldSize < newSize := by
    rw [UInt32.lt_iff_toNat_lt, holdSize, hnewSize]
    exact hlayout.2.2.2.2.2
  have holdPositive : 0 < oldSize.toNat := by
    rw [holdSize]
    exact hlayout.2.2.1.1
  have holdNonzero : oldSize ≠ 0 := by
    intro hzero
    have := congrArg UInt32.toNat hzero
    simp only [UInt32.toNat_zero] at this
    omega
  iintro ⟨Hruntime, Hbump, HoldBlock, HnewBlock, Hstreams, Hcont⟩
  isimp only [LiveBlock] at HoldBlock HnewBlock
  icases HoldBlock with ⟨HoldToken, HoldSlice, %holdFacts⟩
  icases HnewBlock with ⟨HnewToken, HnewSlice, %hnewFacts⟩
  have hnewNonzero : newPtr ≠ 0 := hnewFacts.2.1
  have holdLength : oldBytes.length = oldSize.toNat := by
    rw [holdSize]
    exact holdFacts.1
  have hnewLength : newBytes.length = newSize.toNat := by
    rw [hnewSize]
    exact hnewFacts.1
  have hprefixLength : (newBytes.take oldSize.toNat).length = oldSize.toNat := by
    simp [List.length_take, hnewLength]
    omega
  have htailLength : (newBytes.drop oldSize.toNat).length =
      newLayout.size - oldLayout.size := by
    simp [hnewFacts.1, holdSize]
  ihave HnewSlice' : ByteSlice newPtr
      (newBytes.take oldSize.toNat ++ newBytes.drop oldSize.toNat) $$ [HnewSlice]
  · rw [List.take_append_drop]
    iexact HnewSlice
  icases (ByteSlice_append newPtr (newBytes.take oldSize.toNat)
      (newBytes.drop oldSize.toNat)).mp $$ HnewSlice' with
    ⟨HnewPrefix, HnewTail⟩
  isimp only [Project.Mergesort.Representations.ByteSlice] at
    HoldSlice HnewPrefix
  icases HoldSlice with ⟨%holdNowrap, HoldBytes⟩
  icases HnewPrefix with ⟨%hnewPrefixNowrap, HnewPrefixBytes⟩
  iapply twp_block
  simp only [func8CopyBody, func8Locals]
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [hnewNonzero])
  iapply twp_brIfZero
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_ltU (result := 0) (by simp [UInt32.not_lt.mpr (UInt32.le_of_lt holdLt)])
  iapply twp_select (selected := .i32 oldSize) (by simp)
  iapply twp_localTee
      (locals' := func8Locals oldPtr oldSize newPtr newSize oldSize requiredPages
        currentPages
        [.i32 oldSize]) (by rfl)
  simp only [func8Locals]
  iapply twp_eqz (result := 0) (by simp [holdNonzero])
  iapply twp_brIfZero
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_memoryCopy32 (newBytes.take oldSize.toNat) oldBytes
      hprefixLength holdLength holdPositive
      (by simpa only [hprefixLength, UInt32.size] using hnewPrefixNowrap)
      (by simpa only [holdLength, UInt32.size] using holdNowrap) $$
      HoldBytes HnewPrefixBytes
  iintro HoldBytes HnewPrefixBytes
  ihave HoldSlice : Project.Mergesort.Representations.ByteSlice oldPtr oldBytes $$
      [HoldBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    iframe
    ipureintro
    exact holdNowrap
  ihave HoldBlock : LiveBlock heapId oldId oldPtr oldLayout oldBytes $$
      [HoldToken HoldSlice]
  · unfold LiveBlock
    iframe
    ipureintro
    exact holdFacts
  let finalBytes := oldBytes ++ newBytes.drop oldSize.toNat
  have hfinalLength : finalBytes.length = newLayout.size := by
    dsimp only [finalBytes]
    rw [List.length_append, holdFacts.1, htailLength]
    omega
  ihave HnewPrefix : Project.Mergesort.Representations.ByteSlice newPtr oldBytes $$
      [HnewPrefixBytes]
  · unfold Project.Mergesort.Representations.ByteSlice
    iframe
    ipureintro
    simpa only [hprefixLength, holdLength] using hnewPrefixNowrap
  ihave HnewSlice : Project.Mergesort.Representations.ByteSlice newPtr finalBytes $$
      [HnewPrefix HnewTail]
  · dsimp only [finalBytes]
    iapply (ByteSlice_append newPtr oldBytes
      (newBytes.drop oldSize.toNat)).mpr
    have hprefixLayoutLength :
        (newBytes.take oldLayout.size).length = oldLayout.size := by
      rw [← holdSize]
      exact hprefixLength
    simp only [holdSize, hprefixLayoutLength, holdFacts.1]
    iframe
  ihave HnewBlock : LiveBlock heapId history.nextId newPtr newLayout
      finalBytes $$ [HnewToken HnewSlice]
  · unfold LiveBlock
    iframe
    ipureintro
    exact ⟨hfinalLength, hnewFacts.2⟩
  imod BumpHeap_retire heapId finish finish.toNat
      (history.allocate newPtr newLayout) oldId oldPtr oldLayout oldBytes $$
      [Hbump HoldBlock] with Hbump
  · iframe
  ihave Hbump' : BumpHeap heapId finish finish.toNat
      (history.reallocate oldId oldPtr oldLayout newPtr newLayout) $$ [Hbump]
  · unfold AllocationHistory.reallocate
    iexact Hbump
  iapply twp_exitControl rfl
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iapply twp_returnFromCallExplicit $$ Hmodule
  iintro Hmodule
  simp only [List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  have hcopy : finalBytes.take (min oldLayout.size newLayout.size) =
      oldBytes.take (min oldLayout.size newLayout.size) := by
    have hmin : min oldLayout.size newLayout.size = oldLayout.size :=
      min_eq_left (Nat.le_of_lt hlayout.2.2.2.2.2)
    rw [hmin]
    dsimp only [finalBytes]
    simp only [List.take_append]
    rw [holdFacts.1]
    simp
  isimp only [ResumeWP, resumeExpr, RuntimeContext, List.cons_append,
    List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule Henv] Hbump' HnewBlock
  · isplitl [Hmodule]
    · iexact Hmodule
    · iexact Henv
  · ipureintro
    exact hcopy
  · iexact Hstreams

/-- Commit the cursor and metadata after the fresh physical range has been
claimed, then run the generated copy/return tail. -/
private theorem twp_func8_commit_copy_and_return
    [WasmSmallStepGS hlc Universal.State]
    (oldPtr oldSize newPtr newSize finish requiredPages currentPages
      storedCursor : UInt32)
    (oldLayout newLayout : AllocLayout)
    (heapId : GName) (oldId : Nat)
    (oldBytes newBytes : List UInt8)
    (frontier ownedPages : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (currentControls : List ControlFrame)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hfrontierLow : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hlayout : oldLayout.Matches oldSize 1 ∧
      newLayout.Matches newSize 1 ∧
      oldLayout.Valid ∧ newLayout.Valid ∧
      oldLayout.alignment = 1 ∧ oldLayout.size < newLayout.size)
    (hclassify : classifyBump frontier newLayout = .success newPtr finish)
    (hbytesLength : newBytes.length = newLayout.size)
    (hphysical : finish.toNat ≤ ownedPages * 65536) :
    iprop(
      RuntimeContext ∗
      pointsTo_u32 0 allocatorCursor storedCursor ∗
      heapFrontierOwn finish.toNat ∗
      AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗
      memoryPagesOwn ownedPages ∗
      ByteSlice newPtr newBytes ∗
      LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
      Streams input output raised ∗
      (∀ finalBytes : List UInt8,
        RuntimeContext -∗
        BumpHeap heapId finish finish.toNat
          (history.reallocate oldId oldPtr oldLayout newPtr newLayout) -∗
        LiveBlock heapId history.nextId newPtr newLayout finalBytes -∗
        ⌜finalBytes.take (min oldLayout.size newLayout.size) =
          oldBytes.take (min oldLayout.size newLayout.size)⌝ -∗
        Streams input output raised -∗
        ResumeWP [.i32 newPtr] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func8Locals oldPtr oldSize newPtr newSize finish requiredPages
            currentPages [.i32 0],
          [.localGet 4, .store32 allocatorCursor,
            .block 0 0 func8CopyBody, .localGet 2, .ret],
          1, [], currentControls,
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcursor, Hfrontier, Hauth, Hretired, Hpages, Hbytes,
    HoldBlock, Hstreams, Hcont⟩
  simp only [func8Locals]
  iapply twp_localGet rfl
  ihave HcursorAt : pointsTo_u32 0 ((0 : UInt32) + allocatorCursor)
      storedCursor $$ [Hcursor]
  · rw [UInt32.zero_add]
    iexact Hcursor
  iapply twp_store32 (address := 0) (offset := allocatorCursor) storedCursor
      (by decide) (by decide) (by decide) (by decide) $$ HcursorAt
  iintro Hcursor
  isimp only [UInt32.zero_add] at Hcursor
  ihave Hcursor' : pointsTo_u32 0 allocatorCursor finish $$ [Hcursor]
  · iexact Hcursor
  have hnewAlignment : newLayout.alignment = 1 := by
    simpa using hlayout.2.1.2.symm
  imod BumpHeap_commit heapId frontier history newPtr finish newLayout newBytes
      ownedPages hfrontierLow hwf hlayout.2.2.2.1 (Or.inl hnewAlignment)
      hclassify hbytesLength hphysical $$
      [Hcursor' Hfrontier Hauth Hretired Hpages Hbytes] with
      ⟨Hbump, HnewBlock⟩
  · iframe
  iapply twp_func8_copy_and_return oldPtr oldSize newPtr newSize oldLayout
      newLayout heapId oldId oldBytes newBytes finish
      history input output raised finish requiredPages currentPages
      currentControls callerLocals stack code arity remainder
      controls calls s E Φ hlayout
  iframe Hruntime Hbump HoldBlock HnewBlock Hstreams Hcont

/-- Claim the fresh bytes at a page count known to cover the classified end,
then commit and finish the reallocation. -/
private theorem twp_func8_claim_commit_copy_and_return
    [WasmSmallStepGS hlc Universal.State]
    (oldPtr oldSize newPtr newSize finish requiredPages currentPages
      storedCursor : UInt32)
    (oldLayout newLayout : AllocLayout)
    (heapId : GName) (oldId : Nat) (oldBytes : List UInt8)
    (frontier ownedPages : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {currentControls : List ControlFrame}
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hfrontierLow : heapBase.toNat ≤ frontier)
    (hwf : HistoryWellFormed frontier history)
    (hlayout : oldLayout.Matches oldSize 1 ∧
      newLayout.Matches newSize 1 ∧
      oldLayout.Valid ∧ newLayout.Valid ∧
      oldLayout.alignment = 1 ∧ oldLayout.size < newLayout.size)
    (hclassify : classifyBump frontier newLayout = .success newPtr finish)
    (hstart : frontier ≤ newPtr.toNat)
    (hendWord : newPtr.toNat + newLayout.size < UInt32.size)
    (hfinishNat : finish.toNat = newPtr.toNat + newLayout.size)
    (hphysical : finish.toNat ≤ ownedPages * 65536) :
    iprop(
      RuntimeContext ∗
      pointsTo_u32 0 allocatorCursor storedCursor ∗
      heapFrontierOwn frontier ∗
      AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗
      memoryPagesOwn ownedPages ∗
      LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
      Streams input output raised ∗
      (∀ finalBytes : List UInt8,
        RuntimeContext -∗
        BumpHeap heapId finish finish.toNat
          (history.reallocate oldId oldPtr oldLayout newPtr newLayout) -∗
        LiveBlock heapId history.nextId newPtr newLayout finalBytes -∗
        ⌜finalBytes.take (min oldLayout.size newLayout.size) =
          oldBytes.take (min oldLayout.size newLayout.size)⌝ -∗
        Streams input output raised -∗
        ResumeWP [.i32 newPtr] callerLocals stack code arity remainder controls
          calls s E Φ)) ⊢
      WP (.running
        ⟨func8Locals oldPtr oldSize newPtr newSize finish requiredPages
            currentPages,
          [.const 0, .localGet 4, .store32 allocatorCursor,
            .block 0 0 func8CopyBody, .localGet 2, .ret],
          1, [], currentControls,
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcursor, Hfrontier, Hauth, Hretired, Hpages, HoldBlock,
    Hstreams, Hcont⟩
  have hbound : newPtr.toNat + newLayout.size ≤ ownedPages * 65536 := by
    rw [← hfinishNat]
    exact hphysical
  ihave Hframe : iprop(
      RuntimeContext ∗ pointsTo_u32 0 allocatorCursor storedCursor ∗
      AllocMetaAuth heapId history ∗ RetiredBytes heapId history ∗
      LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
      Streams input output raised ∗
      (∀ finalBytes : List UInt8,
        RuntimeContext -∗
        BumpHeap heapId finish finish.toNat
          (history.reallocate oldId oldPtr oldLayout newPtr newLayout) -∗
        LiveBlock heapId history.nextId newPtr newLayout finalBytes -∗
        ⌜finalBytes.take (min oldLayout.size newLayout.size) =
          oldBytes.take (min oldLayout.size newLayout.size)⌝ -∗
        Streams input output raised -∗
        ResumeWP [.i32 newPtr] callerLocals stack code arity remainder controls
          calls s E Φ)) $$
      [Hruntime Hcursor Hauth Hretired HoldBlock Hstreams Hcont]
  · iframe
  iapply Project.Mergesort.ContractProofs.twp_const_alloc_freshRange_owned
      frontier ownedPages newPtr newLayout.size hstart hbound hendWord $$
      Hframe Hfrontier Hpages
  iintro %newBytes %hbytesLength Hfrontier Hpages Hbytes Hframe
  icases Hframe with
    ⟨Hruntime, Hcursor, Hauth, Hretired, HoldBlock, Hstreams, Hcont⟩
  ihave Hfrontier' : heapFrontierOwn finish.toNat $$ [Hfrontier]
  · rw [hfinishNat]
    iexact Hfrontier
  iapply twp_func8_commit_copy_and_return oldPtr oldSize newPtr newSize finish
      requiredPages currentPages storedCursor oldLayout newLayout heapId oldId
      oldBytes newBytes frontier ownedPages history input output raised
      currentControls callerLocals stack code arity remainder controls calls
      s E Φ
      hfrontierLow hwf hlayout hclassify hbytesLength hphysical
  iframe Hruntime Hcursor Hfrontier' Hauth Hretired Hpages Hbytes HoldBlock
    Hstreams Hcont

/-- Once either checked end computation or physical growth fails, the
generated tail delegates to the proved `talos.oom` shim.  The old allocation
and pre-commit bump state are preserved exactly. -/
private theorem twp_func8_oom
    [WasmSmallStepGS hlc Universal.State]
    (oldPtr oldSize newPtr newSize : UInt32)
    (heapId : GName) (oldId : Nat) (oldLayout : AllocLayout)
    (oldBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (temp requiredPages currentPages : UInt32)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) :
    iprop(
      RuntimeContext ∗
      BumpHeap heapId storedCursor frontier history ∗
      LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
      Streams input output raised ∗
      (BumpHeap heapId storedCursor frontier history -∗
        LiveBlock heapId oldId oldPtr oldLayout oldBytes -∗
        Streams input output true -∗
        Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
        ⟨func8Locals oldPtr oldSize newPtr newSize temp requiredPages currentPages,
          [.call 9, .unreachable], 1, [], [],
          { locals := { callerLocals with values := stack }
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hbump, Hblock, Hstreams, Hcont⟩
  have Hoom := Project.Mergesort.ContractProofs.func6_correct (hlc := hlc)
      (input := input) (output := output) (raised := raised)
      (callerLocals := func8Locals oldPtr oldSize newPtr newSize temp
        requiredPages currentPages)
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
  simp only [List.nil_append, func8Locals] at Hoom ⊢
  iapply Hoom
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hstreams]
  · iexact Hstreams
  iintro Hstreams
  iapply Hcont $$ Hbump Hblock Hstreams

/-- Generated reallocation satisfies its frozen success/OOM contract. -/
theorem func8_correct [WasmSmallStepGS hlc Universal.State] :
    Func8Spec (hlc := hlc) := by
  unfold Func8Spec CallContract callExpr
  intro oldPtr oldSize alignment newSize oldLayout newLayout heapId oldId
    oldBytes storedCursor frontier history input output raised callerLocals
    stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hbump, Hblock, Hstreams, %hlayout, Hcont⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_call Project.Mergesort.module 11
      Project.Mergesort.func8Def (by decide) func8_index $$ Hmodule
  iintro Hmodule
  simp [Project.Mergesort.func8Def, func8_shape,
    Function.toLocals, Function.numParams]
  cases hdecision : classifyBump frontier newLayout with
  | success newPtr finish =>
      isimp only [ReallocContinuation, hdecision] at Hcont
      have halignmentNat : alignment.toNat = 1 := by
        rw [hlayout.1.2, hlayout.2.2.2.2.1]
      have halignment : alignment = 1 := by
        apply UInt32.toNat_inj.mp
        simpa using halignmentNat
      have hnewAlignment : newLayout.alignment = 1 := by
        rw [← hlayout.2.1.2, halignmentNat]
      have hnewLayoutShape :
          newLayout = { size := newLayout.size, alignment := 1 } := by
        cases newLayout
        simp_all
      have hclassify' :
          classifyBump frontier { size := newLayout.size, alignment := 1 } =
            .success newPtr finish := by
        rw [← hnewLayoutShape]
        exact hdecision
      rcases classifyBump_success_align1 frontier newLayout.size newPtr finish
          hclassify' with
        ⟨hfrontierBound, hbase, hbaseNat, hendWord, hendSigned,
          hfinishNat⟩
      have hfinishPtrNat :
          finish.toNat = newPtr.toNat + newLayout.size := by
        rw [hfinishNat, hbaseNat]
      have hnewSizeNat : newSize.toNat = newLayout.size := hlayout.2.1.1
      have hfinishWord : newPtr + newSize = finish := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, hnewSizeNat]
        norm_num [UInt32.size] at hendWord ⊢
        rw [Nat.mod_eq_of_lt hendWord, hfinishNat, hbaseNat]
      have hbaseLeFinish : newPtr ≤ finish := by
        rw [UInt32.le_iff_toNat_le_toNat, hfinishNat]
        omega
      have hfinishSigned : finish.toNat < 2147483648 := by
        rw [hfinishPtrNat]
        exact hendSigned
      isimp only [BumpHeap] at Hbump
      icases Hbump with
        ⟨Hcursor, Hfrontier, Hauth, Hretired, %oldOwnedPages, HoldPages,
          %hheap⟩
      rcases hheap with
        ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat, hwf,
          hphysicalFrontier⟩
      have hfrontierWord :
          (if storedCursor ≠ 0 then storedCursor else heapBase) = newPtr := by
        rw [hbase]
        split
        · rename_i hnonzero
          apply UInt32.toNat_inj.mp
          rw [hcursorNat hnonzero,
            UInt32.toNat_ofNat_of_lt' hfrontierBound]
        · rename_i hzero
          simp only [ne_eq, Decidable.not_not] at hzero
          have hfrontierEq := (hcursorZero.mp hzero).2
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_ofNat_of_lt' hfrontierBound]
          exact hfrontierEq.symm
      iapply twp_block
      simp only [func8PostArithmetic, func8GrowthBody, func8CopyBody,
        List.drop_zero]
      subst alignment
      wasm_twp_pures [twp_localGet twp_const twp_add]
      simp only [show (0xFFFFFFFF : UInt32) + 1 = 0 by decide]
      iapply twp_localTee rfl
      simp only [List.length]
      iapply twp_const
      ihave HcursorAt : pointsTo_u32 0 (0 + allocatorCursor) storedCursor $$
          [Hcursor]
      · simp only [UInt32.zero_add]
        iframe
      iapply twp_load32 (address := 0) (offset := allocatorCursor) storedCursor
          (by decide) (by decide) (by decide) (by decide) $$ HcursorAt
      iintro Hcursor
      isimp only [UInt32.zero_add] at Hcursor
      iapply twp_localTee rfl
      simp only [List.length]
      wasm_twp_pures [twp_const twp_localGet]
      iapply twp_select (selected := .i32 newPtr) (by
        by_cases hzero : storedCursor = 0
        · simp [hzero] at hfrontierWord ⊢
          exact hfrontierWord.symm
        · simp [hzero] at hfrontierWord ⊢
          exact hfrontierWord.symm)
      iapply twp_add
      simp only [UInt32.add_zero]
      iapply twp_localTee rfl
      simp only [List.length]
      iapply twp_localGet rfl
      iapply twp_ltU (result := 0) (by simp)
      iapply twp_brIfZero
      wasm_twp_pures [twp_localGet twp_const twp_localGet twp_sub]
      simp only [show (0 : UInt32) - 1 = 0xFFFFFFFF by decide]
      iapply twp_and
      rw [show newPtr &&& (0xFFFFFFFF : UInt32) = newPtr by
        exact UInt32.and_neg_one]
      iapply twp_localTee rfl
      simp only [List.set]
      wasm_twp_pures [twp_localGet twp_add]
      rw [UInt32.add_comm newSize newPtr, hfinishWord]
      iapply twp_localTee rfl
      simp only [List.length]
      iapply twp_localGet rfl
      iapply twp_ltU (result := 0) (by
        simp [UInt32.not_lt.mpr hbaseLeFinish])
      iapply twp_brIfZero
      wasm_twp_pures [twp_localGet twp_const]
      have hfinishNonnegative :
          ¬ finish.toInt32 < (0 : UInt32).toInt32 := by
        simp only [UInt32.toInt32, LT.lt, Int32.lt, Int32.toBitVec]
        rw [BitVec.slt_iff_toInt_lt]
        simp only [BitVec.toInt, Nat.reducePow]
        change ¬ (if 2 * finish.toNat < 4294967296 then
          (finish.toNat : Int) else (finish.toNat : Int) - 4294967296) < 0
        rw [hfinishNat]
        omega
      iapply twp_ltS (result := 0) (by rw [if_neg hfinishNonnegative])
      wasm_twp_pures [twp_brIfZero twp_block twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (65535 : UInt32) finish]
      wasm_twp_pures [twp_const twp_shrU]
      rw [show (16 : UInt32) % 32 = 16 by decide]
      rw [show (finish + 65535) >>> (16 : UInt32) =
        allocatorRequiredPages finish by rfl]
      iapply twp_localTee rfl
      simp only [List.length]
      ihave HsizeFrame : iprop(
          hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
          pointsTo_u32 0 allocatorCursor storedCursor ∗
          heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
          RetiredBytes heapId history ∗ memoryPagesOwn oldOwnedPages ∗
          LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
          Streams input output raised ∗
          ((∀ newBytes : List UInt8,
              RuntimeContext -∗
              BumpHeap heapId finish finish.toNat
                (history.reallocate oldId oldPtr oldLayout newPtr newLayout) -∗
              LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
              ⌜newBytes.take (min oldLayout.size newLayout.size) =
                oldBytes.take (min oldLayout.size newLayout.size)⌝ -∗
              Streams input output raised -∗
              ResumeWP [.i32 newPtr] callerLocals stack code arity remainder
                controls calls s E Φ) ∧
            (BumpHeap heapId storedCursor frontier history -∗
              LiveBlock heapId oldId oldPtr oldLayout oldBytes -∗
              Streams input output true -∗
              Φ (.trapped (.host OOM.trapMessage))))) $$
          [Henv Hcursor Hfrontier Hauth Hretired HoldPages Hblock Hstreams
            Hcont]
      · iframe
      iapply twp_memorySize_tracked Project.Mergesort.module ⟨0⟩ $$
          HsizeFrame Hmodule
      iintro %pages HsizeFrame Hmodule Hpages
      icases HsizeFrame with
        ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldPages, Hblock,
          Hstreams, Hcont⟩
      rw [show Project.Mergesort.module.memIs64 = false by rfl]
      simp only [sizeValue_false]
      iapply twp_localTee rfl
      simp only [List.length]
      iapply twp_leU (result := if allocatorRequiredPages finish ≤
        UInt32.ofNat pages then 1 else 0) rfl
      by_cases hcapacity : allocatorRequiredPages finish ≤ UInt32.ofNat pages
      · rw [if_pos hcapacity]
        iapply twp_brIf (by decide) (by rfl)
        simp only [List.take_zero, List.nil_append, Nat.reduceAdd, Nat.reduceSub,
          List.set, List.drop_zero]
        have hphysical : finish.toNat ≤ pages * 65536 := by
          have hcover := allocatorRequiredPages_covers finish hfinishSigned
          by_cases hpages : pages < UInt32.size
          · have hpagesWord : (UInt32.ofNat pages).toNat = pages :=
              UInt32.toNat_ofNat_of_lt' hpages
            have hrequiredLe :
                (allocatorRequiredPages finish).toNat ≤ pages := by
              rw [← hpagesWord, ← UInt32.le_iff_toNat_le_toNat]
              exact hcapacity
            exact hcover.trans (Nat.mul_le_mul_right 65536 hrequiredLe)
          · have hpagesHigh : UInt32.size ≤ pages := by omega
            have hfinishLePages : finish.toNat ≤ pages := by
              norm_num [UInt32.size] at hpagesHigh
              omega
            have hpagesLeMul : pages ≤ pages * 65536 := by omega
            exact hfinishLePages.trans hpagesLeMul
        ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        ihave Hnormal := BI.and_elim_l $$ Hcont
        iapply twp_func8_claim_commit_copy_and_return oldPtr oldSize newPtr
            newSize finish (allocatorRequiredPages finish)
            (UInt32.ofNat pages) storedCursor oldLayout newLayout heapId oldId
            oldBytes frontier pages history input output raised
            callerLocals stack code arity remainder controls calls s E Φ
            hfrontierLow hwf hlayout hdecision (by omega) hendWord hfinishPtrNat
            hphysical
        iframe Hruntime Hcursor Hfrontier Hauth Hretired Hpages Hblock Hstreams
          Hnormal
      · rw [if_neg hcapacity]
        iapply twp_brIfZero
        wasm_twp_pures [twp_localGet twp_localGet twp_sub]
        let delta := allocatorRequiredPages finish - UInt32.ofNat pages
        ihave HgrowFrame : iprop(
            hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
            pointsTo_u32 0 allocatorCursor storedCursor ∗
            heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
            RetiredBytes heapId history ∗ memoryPagesOwn oldOwnedPages ∗
            LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
            Streams input output raised ∗
            ((∀ newBytes : List UInt8,
                RuntimeContext -∗
                BumpHeap heapId finish finish.toNat
                  (history.reallocate oldId oldPtr oldLayout newPtr newLayout) -∗
                LiveBlock heapId history.nextId newPtr newLayout newBytes -∗
                ⌜newBytes.take (min oldLayout.size newLayout.size) =
                  oldBytes.take (min oldLayout.size newLayout.size)⌝ -∗
                Streams input output raised -∗
                ResumeWP [.i32 newPtr] callerLocals stack code arity remainder
                  controls calls s E Φ) ∧
              (BumpHeap heapId storedCursor frontier history -∗
                LiveBlock heapId oldId oldPtr oldLayout oldBytes -∗
                Streams input output true -∗
                Φ (.trapped (.host OOM.trapMessage))))) $$
            [Henv Hcursor Hfrontier Hauth Hretired HoldPages Hblock Hstreams
              Hcont]
        · iframe
        iapply twp_memoryGrow_tracked Project.Mergesort.module ⟨0⟩ pages
            (fun actualPages hmeasured => by
              iintro HgrowFrame Hmodule Hmeasured
              icases HgrowFrame with
                ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldPages,
                  Hblock, Hstreams, Hcont⟩
              iapply twp_const
              iapply twp_eq (result := 1) (by simp)
              iapply twp_brIf (by decide) (by rfl)
              simp only [List.take_zero, List.nil_append, Nat.reduceAdd,
                Nat.reduceSub, List.set]
              ihave Hbump : BumpHeap heapId storedCursor frontier history $$
                  [Hcursor Hfrontier Hauth Hretired HoldPages]
              · unfold BumpHeap
                iframe
                ipureintro
                exact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat,
                  hwf, hphysicalFrontier⟩
              ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
              · unfold RuntimeContext
                iframe Hmodule Henv
              ihave Hoom := BI.and_elim_r $$ Hcont
              iapply twp_func8_oom oldPtr oldSize newPtr newSize heapId oldId
                  oldLayout oldBytes storedCursor frontier history input output
                  raised finish (allocatorRequiredPages finish)
                  (UInt32.ofNat pages) callerLocals stack code arity remainder
                  controls calls s E Φ
              iframe Hruntime Hbump Hblock Hstreams Hoom)
            (fun oldPages previousPages newPages hfacts hmeasured => by
              iintro HgrowFrame Hmodule Hmeasured HnewPages
              icases HgrowFrame with
                ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldPages,
                  Hblock, Hstreams, Hcont⟩
              iapply twp_const
              by_cases hsentinel : previousPages.toUInt32 =
                  (0xFFFFFFFF : UInt32)
              · iapply twp_eq (result := 1) (by simp [hsentinel])
                iapply twp_brIf (by decide) (by rfl)
                simp only [List.take_zero, List.nil_append, Nat.reduceAdd,
                  Nat.reduceSub, List.set]
                ihave Hbump : BumpHeap heapId storedCursor frontier history $$
                    [Hcursor Hfrontier Hauth Hretired HoldPages]
                · unfold BumpHeap
                  iframe
                  ipureintro
                  exact ⟨hfrontierLow, hfrontierSigned, hcursorZero,
                    hcursorNat, hwf, hphysicalFrontier⟩
                ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
                · unfold RuntimeContext
                  iframe Hmodule Henv
                ihave Hoom := BI.and_elim_r $$ Hcont
                iapply twp_func8_oom oldPtr oldSize newPtr newSize heapId oldId
                    oldLayout oldBytes storedCursor frontier history input
                    output raised finish (allocatorRequiredPages finish)
                    (UInt32.ofNat pages) callerLocals stack code arity remainder
                    controls calls s E Φ
                iframe Hruntime Hbump Hblock Hstreams Hoom
              · iapply twp_eq (result := 0) (by simp [hsentinel])
                wasm_twp_pures [twp_brIfZero twp_exitControl]
                simp only [List.take_zero, List.nil_append, Nat.reduceAdd,
                  Nat.reduceSub, List.set, List.drop_zero]
                have hphysical : finish.toNat ≤ newPages * 65536 := by
                  have hcover := allocatorRequiredPages_covers finish
                    hfinishSigned
                  by_cases hpagesLow : pages < UInt32.size
                  · have hpagesWord : (UInt32.ofNat pages).toNat = pages :=
                      UInt32.toNat_ofNat_of_lt' hpagesLow
                    have hpagesLtRequired :
                        pages < (allocatorRequiredPages finish).toNat := by
                      rw [← hpagesWord]
                      have hwordLt : UInt32.ofNat pages <
                          allocatorRequiredPages finish := by
                        exact UInt32.not_le.mp hcapacity
                      exact UInt32.lt_iff_toNat_lt.mp hwordLt
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
                    exact hcover.trans
                      (Nat.mul_le_mul_right 65536 hrequiredLeNew)
                  · have hpagesHigh : UInt32.size ≤ pages := by omega
                    have hpagesLeOld : pages ≤ oldPages := hmeasured
                    have hfinishLeNew : finish.toNat ≤ newPages := by
                      rw [hfacts.2]
                      norm_num [UInt32.size] at hpagesHigh
                      omega
                    exact hfinishLeNew.trans (by omega)
                ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
                · unfold RuntimeContext
                  iframe Hmodule Henv
                ihave Hnormal := BI.and_elim_l $$ Hcont
                iapply twp_func8_claim_commit_copy_and_return oldPtr oldSize
                    newPtr newSize finish (allocatorRequiredPages finish)
                    (UInt32.ofNat pages) storedCursor oldLayout newLayout
                    heapId oldId oldBytes frontier newPages history input output
                    raised
                    callerLocals stack code arity remainder controls calls s E
                    Φ hfrontierLow hwf hlayout hdecision (by omega) hendWord
                    hfinishPtrNat hphysical
                iframe Hruntime Hcursor Hfrontier Hauth Hretired HnewPages
                  Hblock Hstreams Hnormal)
            $$ HgrowFrame Hmodule Hpages
  | oom =>
      isimp only [ReallocContinuation, hdecision] at Hcont
      have halignmentNat : alignment.toNat = 1 := by
        rw [hlayout.1.2, hlayout.2.2.2.2.1]
      have halignment : alignment = 1 := by
        apply UInt32.toNat_inj.mp
        simpa using halignmentNat
      have hnewAlignment : newLayout.alignment = 1 := by
        rw [← hlayout.2.1.2, halignmentNat]
      have hnewSizeNat : newSize.toNat = newLayout.size := hlayout.2.1.1
      isimp only [BumpHeap] at Hbump
      icases Hbump with
        ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, Hpages, %hheap⟩
      rcases hheap with
        ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat, hwf,
          hphysicalFrontier⟩
      have hfrontierBound : frontier < UInt32.size := by
        norm_num [UInt32.size] at hfrontierSigned ⊢
        omega
      let base : UInt32 := UInt32.ofNat frontier
      have hbaseNat : base.toNat = frontier :=
        UInt32.toNat_ofNat_of_lt' hfrontierBound
      have hfrontierWord :
          (if storedCursor ≠ 0 then storedCursor else heapBase) = base := by
        split
        · rename_i hnonzero
          apply UInt32.toNat_inj.mp
          rw [hcursorNat hnonzero, hbaseNat]
        · rename_i hzero
          simp only [ne_eq, Decidable.not_not] at hzero
          have hfrontierEq := (hcursorZero.mp hzero).2
          apply UInt32.toNat_inj.mp
          rw [hbaseNat]
          exact hfrontierEq.symm
      let finishWord : UInt32 := base + newSize
      have hfinishWordNat : finishWord.toNat =
          (frontier + newLayout.size) % UInt32.size := by
        dsimp only [finishWord]
        rw [UInt32.toNat_add, hbaseNat, hnewSizeNat]
      iapply twp_block
      simp only [func8PostArithmetic, func8GrowthBody, func8CopyBody,
        List.drop_zero]
      subst alignment
      wasm_twp_pures [twp_localGet twp_const twp_add]
      simp only [show (0xFFFFFFFF : UInt32) + 1 = 0 by decide]
      iapply twp_localTee rfl
      simp only [List.length]
      iapply twp_const
      ihave HcursorAt : pointsTo_u32 0 (0 + allocatorCursor) storedCursor $$
          [Hcursor]
      · simp only [UInt32.zero_add]
        iframe
      iapply twp_load32 (address := 0) (offset := allocatorCursor) storedCursor
          (by decide) (by decide) (by decide) (by decide) $$ HcursorAt
      iintro Hcursor
      isimp only [UInt32.zero_add] at Hcursor
      iapply twp_localTee rfl
      simp only [List.length]
      wasm_twp_pures [twp_const twp_localGet]
      iapply twp_select (selected := .i32 base) (by
        by_cases hzero : storedCursor = 0
        · simp [hzero] at hfrontierWord ⊢
          exact hfrontierWord.symm
        · simp [hzero] at hfrontierWord ⊢
          exact hfrontierWord.symm)
      iapply twp_add
      simp only [UInt32.add_zero]
      iapply twp_localTee rfl
      simp only [List.length]
      iapply twp_localGet rfl
      iapply twp_ltU (result := 0) (by simp)
      iapply twp_brIfZero
      wasm_twp_pures [twp_localGet twp_const twp_localGet twp_sub]
      simp only [show (0 : UInt32) - 1 = 0xFFFFFFFF by decide]
      iapply twp_and
      rw [show base &&& (0xFFFFFFFF : UInt32) = base by
        exact UInt32.and_neg_one]
      iapply twp_localTee rfl
      simp only [List.set]
      wasm_twp_pures [twp_localGet twp_add]
      rw [UInt32.add_comm newSize base]
      rw [show base + newSize = finishWord by rfl]
      iapply twp_localTee rfl
      simp only [List.length]
      iapply twp_localGet rfl
      have hsizeUpper : newLayout.size ≤ 2147483647 := by
        simpa [hnewAlignment] using hlayout.2.2.2.1.2.2.2.2.1
      have hend : frontier + newLayout.size < UInt32.size := by
        norm_num [UInt32.size] at hfrontierSigned ⊢
        omega
      have hfinishNat : finishWord.toNat = frontier + newLayout.size := by
        rw [hfinishWordNat, Nat.mod_eq_of_lt hend]
      have hbaseLeFinish : base ≤ finishWord := by
        rw [UInt32.le_iff_toNat_le_toNat, hbaseNat, hfinishNat]
        omega
      iapply twp_ltU (result := 0) (by
        rw [if_neg (UInt32.not_lt.mpr hbaseLeFinish)])
      iapply twp_brIfZero
      wasm_twp_pures [twp_localGet twp_const]
      have hnotSigned : ¬ frontier + newLayout.size < 2147483648 := by
        intro hsigned
        have hrawBase :
            UInt32.ofNat frontier &&& (0 - UInt32.ofNat 1) = base := by
          simp [base]
        have hrawFinish :
            UInt32.ofNat (base.toNat + newLayout.size) = finishWord := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_ofNat_of_lt' (by simpa [hbaseNat] using hend),
            hfinishNat, hbaseNat]
        have hsuccess : classifyBump frontier newLayout =
            .success base finishWord := by
          unfold classifyBump
          simp only [hnewAlignment, Nat.reduceSubDiff, Nat.add_zero]
          rw [dif_pos hfrontierBound]
          rw [hrawBase]
          rw [if_pos ⟨by simpa [hbaseNat] using hend,
            by simpa [hbaseNat] using hsigned⟩]
          rw [hrawFinish]
        rw [hdecision] at hsuccess
        contradiction
      have hfinishNegative :
          finishWord.toInt32 < (0 : UInt32).toInt32 := by
        simp only [UInt32.toInt32, LT.lt, Int32.lt, Int32.toBitVec]
        rw [BitVec.slt_iff_toInt_lt]
        simp only [BitVec.toInt, Nat.reducePow]
        change (if 2 * finishWord.toNat < 4294967296 then
          (finishWord.toNat : Int)
          else (finishWord.toNat : Int) - 4294967296) < 0
        rw [if_neg (by rw [hfinishNat]; omega)]
        rw [hfinishNat]
        omega
      iapply twp_ltS (result := 1) (by rw [if_pos hfinishNegative])
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.nil_append]
      ihave Hbump : BumpHeap heapId storedCursor frontier history $$
          [Hcursor Hfrontier Hauth Hretired Hpages]
      · unfold BumpHeap
        iframe
        ipureintro
        exact ⟨hfrontierLow, hfrontierSigned, hcursorZero, hcursorNat, hwf,
          hphysicalFrontier⟩
      ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
      · unfold RuntimeContext
        iframe Hmodule Henv
      simp only [Nat.reduceAdd, Nat.reduceSub, List.set, ValueType.zero]
      iapply twp_func8_oom oldPtr oldSize base newSize heapId oldId oldLayout
          oldBytes storedCursor frontier history input output raised
          finishWord base 0 callerLocals stack code arity remainder controls
          calls s E Φ
      iframe Hruntime Hbump Hblock Hstreams Hcont

end Project.Mergesort.Func8Proof
