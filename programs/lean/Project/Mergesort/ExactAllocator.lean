import Project.Mergesort.Func5Proof
import Project.Mergesort.Func8Proof
import Project.Mergesort.Func9Proof
import CodeLib.SepLogic.SmallStepMemoryCaps

/-!
# Normal allocation and reallocation with exact physical page ownership

The compiled allocators measure and, when needed, grow the same memory whose
linear page token is threaded through their contracts. The accepted end fitting
under the actual cap determines normal return, including the growing branch.
Zeroing and copying retain the updated token through their actual byte effects.
-/

namespace Project.Mergesort.ExactAllocator

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Contracts Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

private theorem half_snapshot [WasmMemoryPagesGS Universal.State] (pages : Nat) :
    memoryPagesHalf (α := Universal.State) pages ⊢ memoryPagesOwn pages :=
  pagesAuthorityFrac_snapshot (1 : Qp).half pages

/-- Actual compiled `call 8` returns normally and retains the exact physical
page count. The fit premise concerns the accepted allocation end, not a supplied
execution or a successful `memory.grow` equation. -/
theorem twp_func5_call_exact [WasmSmallStepGS hlc Universal.State]
    (size alignment : UInt32) (layout : AllocLayout)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (base finish : UInt32) (pages cap : Nat)
    (input output : List UInt8) (raised : Bool)
    (hmatches : layout.Matches size alignment) (hvalid : layout.Valid)
    (halignment : layout.alignment = 1 ∨ layout.alignment = 4)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hpages : pages ≤ cap) (hhard : cap ≤ Module.memoryHardCap)
    (hfit : (allocatorRequiredPages finish).toNat ≤ cap)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    CallContract 8 [.i32 alignment, .i32 size]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗ memoryCapOwn 0 cap ∗ memoryPagesHalf pages ∗
        BumpHeap heapId storedCursor frontier history ∗ Streams input output raised ∗
        (∀ bytes : List UInt8,
          RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
          BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
          LiveBlock heapId history.nextId base layout bytes -∗
          Streams input output raised -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) := by
  unfold CallContract
  iintro ⟨Hruntime, Hcap, Hexact, Hbump, Hstreams, Hcont⟩
  have Hprefix := Func5Proof.twp_func5_call_to_memorySize
    size alignment layout heapId storedCursor frontier history base finish
    hmatches hvalid halignment hclassify
    (callerLocals := callerLocals) (stack := stack) (code := code) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract at Hprefix
  iapply Hprefix
  iframe Hruntime Hbump
  iintro Hruntime Hbump
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [BumpHeap] at Hbump
  icases Hbump with ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, HoldPages, %hheap⟩
  rcases hheap with ⟨hfrontierLow, _, _, _, hwf, _⟩
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  have hfinishSigned : finish.toNat < 2147483648 := by
    dsimp only at hfacts
    omega
  rcases classifyBump_success_reachable frontier layout base finish
      hfrontierLow hvalid halignment hclassify with
    ⟨hbaseFresh, _, _, hallocWord, _, hfinishExact, _⟩
  have hpagesWord : pages.toUInt32.toNat = pages :=
    UInt32.toNat_ofNat_of_lt' ((hpages.trans hhard).trans_lt (by decide))
  have hrequiredCovers := allocatorRequiredPages_covers finish hfinishSigned
  unfold Func5Proof.func5MemorySizeExpr
  ihave HsizeFrame : iprop(
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
      memoryCapOwn 0 cap ∗ pointsTo_u32 0 allocatorCursor storedCursor ∗
      heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗ Streams input output raised ∗
      (∀ bytes : List UInt8,
        RuntimeContext -∗ memoryCapOwn 0 cap -∗
        memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout bytes -∗ Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) $$
      [Henv Hcap Hcursor Hfrontier Hauth Hretired Hstreams Hcont]
  · iframe
  iapply twp_memorySize_exact Project.Mergesort.module ⟨0⟩ pages $$ HsizeFrame Hmodule Hexact
  iintro HsizeFrame Hmodule Hexact
  icases HsizeFrame with ⟨Henv, Hcap, Hcursor, Hfrontier, Hauth, Hretired, Hstreams, Hcont⟩
  simp only [show Project.Mergesort.module.memIs64 = false by rfl,
    sizeValue, Bool.false_eq_true, ↓reduceIte]
  wasm_twp_pures [twp_localTee]
  simp
  by_cases hcovered : allocatorRequiredPages finish ≤ pages.toUInt32
  · have hle : (allocatorRequiredPages finish).toNat ≤ pages := by
      simpa only [hpagesWord] using UInt32.le_iff_toNat_le_toNat.mp hcovered
    have hphysical : finish.toNat ≤ pages * 65536 :=
      hrequiredCovers.trans (Nat.mul_le_mul_right 65536 hle)
    iapply twp_leU (result := 1) (by rw [if_pos hcovered])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave #Hpages := half_snapshot pages $$ Hexact
    isimp only [Nat.max_eq_left hle] at Hcont
    iclose_runtime Hruntime with Hmodule Henv
    iapply Func5Proof.twp_func5_claim_commit_and_return
        pages.toUInt32 finish base (allocatorRequiredPages finish) storedCursor
        layout heapId frontier pages history input output raised
        callerLocals stack code arity remainder controls calls s E Φ
        hfrontierLow hwf hvalid halignment hclassify hbaseFresh hallocWord hfinishExact hphysical
    iframe Hruntime Hcursor Hfrontier Hauth Hretired Hpages Hstreams
    iintro %bytes Hruntime Hbump Hblock Hstreams
    iapply Hcont $$ %bytes Hruntime Hcap Hexact Hbump Hblock Hstreams
  · have hlt : pages < (allocatorRequiredPages finish).toNat := by
      simpa only [hpagesWord] using
        UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hcovered)
    let delta := allocatorRequiredPages finish - pages.toUInt32
    have hdelta : delta.toNat = (allocatorRequiredPages finish).toNat - pages := by
      dsimp only [delta]
      rw [UInt32.toNat_sub_of_le, hpagesWord]
      rw [UInt32.le_iff_toNat_le_toNat, hpagesWord]
      omega
    have hnew : pages + delta.toNat = (allocatorRequiredPages finish).toNat := by
      rw [hdelta]
      omega
    iapply twp_leU (result := 0) (by rw [if_neg hcovered])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_sub]
    ihave HgrowFrame : iprop(
        hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
        pointsTo_u32 0 allocatorCursor storedCursor ∗
        heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
        RetiredBytes heapId history ∗ Streams input output raised ∗
        (∀ bytes : List UInt8,
          RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
          BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
          LiveBlock heapId history.nextId base layout bytes -∗ Streams input output raised -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) $$
        [Henv Hcursor Hfrontier Hauth Hretired Hstreams Hcont]
    · iframe
    iapply twp_memoryGrow_exact (delta := delta) Project.Mergesort.module ⟨0⟩ cap pages hmode
        (by simpa only [hnew] using hfit) $$ HgrowFrame Hmodule Hcap Hexact
    iintro HgrowFrame Hmodule Hcap Hexact
    icases HgrowFrame with ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, Hstreams, Hcont⟩
    isimp only [hnew] at Hexact
    have hnotSentinel : pages.toUInt32 ≠ (0xFFFFFFFF : UInt32) :=
      capped_growth_previous_ne_failure pages (allocatorRequiredPages finish).toNat cap
        delta hnew.symm hfit hhard
    wasm_twp_pures [twp_const]
    iapply twp_ne (result := 1) (by simp [hnotSentinel])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave #Hpages := half_snapshot (allocatorRequiredPages finish).toNat $$ Hexact
    isimp only [Nat.max_eq_right (Nat.le_of_lt hlt)] at Hcont
    iclose_runtime Hruntime with Hmodule Henv
    iapply Func5Proof.twp_func5_claim_commit_and_return
        pages.toUInt32 finish base (allocatorRequiredPages finish) storedCursor
        layout heapId frontier (allocatorRequiredPages finish).toNat history input output raised
        callerLocals stack code arity remainder controls calls s E Φ
        hfrontierLow hwf hvalid halignment hclassify hbaseFresh hallocWord hfinishExact hrequiredCovers
    iframe Hruntime Hcursor Hfrontier Hauth Hretired Hpages Hstreams
    iintro %bytes Hruntime Hbump Hblock Hstreams
    iapply Hcont $$ %bytes Hruntime Hcap Hexact Hbump Hblock Hstreams

/-- Actual compiled zeroing allocation returns a zero-filled block and exact
physical page ownership when its accepted end fits under the cap. -/
theorem twp_func9_call_exact [WasmSmallStepGS hlc Universal.State]
    (size : UInt32) (layout : AllocLayout)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (base finish : UInt32) (pages cap : Nat)
    (input output : List UInt8) (raised : Bool)
    (hmatches : layout.Matches size 4) (hvalid : layout.Valid)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hpages : pages ≤ cap) (hhard : cap ≤ Module.memoryHardCap)
    (hfit : (allocatorRequiredPages finish).toNat ≤ cap)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    CallContract 12 [.i32 4, .i32 size]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗ memoryCapOwn 0 cap ∗
        memoryPagesHalf pages ∗
        BumpHeap heapId storedCursor frontier history ∗ Streams input output raised ∗
        (RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
          BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
          LiveBlock heapId history.nextId base layout (List.replicate layout.size 0) -∗
          Streams input output raised -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) := by
  unfold CallContract
  iintro ⟨Hruntime, Hcap, Hexact, Hbump, Hstreams, Hcont⟩
  have Hprefix := Func9Proof.twp_func9_call_to_memorySize
    size layout heapId storedCursor frontier history base finish hmatches hclassify
    (callerLocals := callerLocals) (stack := stack) (code := code) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract at Hprefix
  iapply Hprefix
  iframe Hruntime Hbump
  iintro Hruntime Hbump
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [BumpHeap] at Hbump
  icases Hbump with ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, HoldPages, %hheap⟩
  rcases hheap with ⟨hfrontierLow, _, _, _, hwf, _⟩
  have halignment : layout.alignment = 4 := by simpa using hmatches.2.symm
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  have hfinishSigned : finish.toNat < 2147483648 := by
    dsimp only at hfacts
    omega
  rcases classifyBump_success_reachable frontier layout base finish
      hfrontierLow hvalid (Or.inr halignment) hclassify with
    ⟨hbaseFresh, _, _, hallocWord, _, hfinishExact, _⟩
  have hpagesWord : pages.toUInt32.toNat = pages :=
    UInt32.toNat_ofNat_of_lt' ((hpages.trans hhard).trans_lt (by decide))
  have hrequiredCovers := allocatorRequiredPages_covers finish hfinishSigned
  unfold Func9Proof.func9MemorySizeExpr
  simp only [Project.Mergesort.func9]
  ihave HsizeFrame : iprop(
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
      memoryCapOwn 0 cap ∗
      pointsTo_u32 0 allocatorCursor storedCursor ∗
      heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗ Streams input output raised ∗
      (RuntimeContext -∗ memoryCapOwn 0 cap -∗
        memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
        LiveBlock heapId history.nextId base layout (List.replicate layout.size 0) -∗ Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) $$
      [Henv Hcap Hcursor Hfrontier Hauth Hretired Hstreams Hcont]
  · iframe
  iapply twp_memorySize_exact Project.Mergesort.module ⟨0⟩ pages $$ HsizeFrame Hmodule Hexact
  iintro HsizeFrame Hmodule Hexact
  icases HsizeFrame with ⟨Henv, Hcap, Hcursor, Hfrontier, Hauth, Hretired, Hstreams, Hcont⟩
  simp only [show Project.Mergesort.module.memIs64 = false by rfl,
    sizeValue, Bool.false_eq_true, ↓reduceIte]
  wasm_twp_pures [twp_localTee]
  simp
  by_cases hcovered : allocatorRequiredPages finish ≤ pages.toUInt32
  · have hle : (allocatorRequiredPages finish).toNat ≤ pages := by
      simpa only [hpagesWord] using UInt32.le_iff_toNat_le_toNat.mp hcovered
    have hphysical : finish.toNat ≤ pages * 65536 :=
      hrequiredCovers.trans (Nat.mul_le_mul_right 65536 hle)
    iapply twp_leU (result := 1) (by rw [if_pos hcovered])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave #Hpages := half_snapshot pages $$ Hexact
    isimp only [Nat.max_eq_left hle] at Hcont
    iclose_runtime Hruntime with Hmodule Henv
    have Hclaim := Project.Mergesort.Func9Proof.twp_func9_claim_commit_zero_and_return
        size base finish (allocatorRequiredPages finish) pages.toUInt32 storedCursor
        layout heapId frontier pages history input output raised
        [{ kind := .block, paramArity := 0, resultArity := 0,
           body := match Project.Mergesort.func9 with
             | .block _ _ body :: _ => body
             | _ => [],
           continuation := [.call 9, .unreachable], belowStack := [] }]
        controls calls callerLocals stack code arity remainder s E Φ
        hfrontierLow hwf hmatches hvalid hclassify hbaseFresh hallocWord hfinishExact hphysical
    simp only [Project.Mergesort.func9, allocatorCursor, Nat.toUInt32] at Hclaim
    simp only [allocatorCursor]
    iapply Hclaim
    iframe Hruntime Hcursor Hfrontier Hauth Hretired Hpages Hstreams
    iintro Hruntime Hbump Hblock Hstreams
    iapply Hcont $$ Hruntime Hcap Hexact Hbump Hblock Hstreams
  · have hlt : pages < (allocatorRequiredPages finish).toNat := by
      simpa only [hpagesWord] using
        UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hcovered)
    let delta := allocatorRequiredPages finish - pages.toUInt32
    have hdelta : delta.toNat = (allocatorRequiredPages finish).toNat - pages := by
      dsimp only [delta]
      rw [UInt32.toNat_sub_of_le, hpagesWord]
      rw [UInt32.le_iff_toNat_le_toNat, hpagesWord]
      omega
    have hnew : pages + delta.toNat = (allocatorRequiredPages finish).toNat := by
      rw [hdelta]
      omega
    iapply twp_leU (result := 0) (by rw [if_neg hcovered])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_sub]
    ihave HgrowFrame : iprop(
        hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
        pointsTo_u32 0 allocatorCursor storedCursor ∗
        heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
        RetiredBytes heapId history ∗ Streams input output raised ∗
        (RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
        BumpHeap heapId finish finish.toNat (history.allocate base layout) -∗
          LiveBlock heapId history.nextId base layout (List.replicate layout.size 0) -∗ Streams input output raised -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) $$
        [Henv Hcursor Hfrontier Hauth Hretired Hstreams Hcont]
    · iframe
    iapply twp_memoryGrow_exact (delta := delta) Project.Mergesort.module ⟨0⟩ cap pages hmode
        (by simpa only [hnew] using hfit) $$ HgrowFrame Hmodule Hcap Hexact
    iintro HgrowFrame Hmodule Hcap Hexact
    icases HgrowFrame with ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, Hstreams, Hcont⟩
    isimp only [hnew] at Hexact
    have hnotSentinel : pages.toUInt32 ≠ (0xFFFFFFFF : UInt32) :=
      capped_growth_previous_ne_failure pages (allocatorRequiredPages finish).toNat cap
        delta hnew.symm hfit hhard
    wasm_twp_pures [twp_const]
    iapply twp_eq (result := 0) (by simp [hnotSentinel])
    wasm_twp_pures [twp_brIfZero twp_exitControl] using [List.take_zero, List.nil_append]
    ihave #Hpages := half_snapshot (allocatorRequiredPages finish).toNat $$ Hexact
    isimp only [Nat.max_eq_right (Nat.le_of_lt hlt)] at Hcont
    iclose_runtime Hruntime with Hmodule Henv
    have Hclaim := Project.Mergesort.Func9Proof.twp_func9_claim_commit_zero_and_return
        size base finish (allocatorRequiredPages finish) pages.toUInt32 storedCursor
        layout heapId frontier (allocatorRequiredPages finish).toNat history input output raised
        [{ kind := .block, paramArity := 0, resultArity := 0,
           body := match Project.Mergesort.func9 with
             | .block _ _ body :: _ => body
             | _ => [],
           continuation := [.call 9, .unreachable], belowStack := [] }]
        controls calls callerLocals stack code arity remainder s E Φ
        hfrontierLow hwf hmatches hvalid hclassify hbaseFresh hallocWord hfinishExact hrequiredCovers
    simp only [Project.Mergesort.func9, allocatorCursor, Nat.toUInt32] at Hclaim
    simp only [allocatorCursor]
    iapply Hclaim
    iframe Hruntime Hcursor Hfrontier Hauth Hretired Hpages Hstreams
    iintro Hruntime Hbump Hblock Hstreams
    iapply Hcont $$ Hruntime Hcap Hexact Hbump Hblock Hstreams

/-- Actual compiled growing reallocation preserves the old byte prefix,
retires the old allocation, and returns exact physical page ownership. -/
theorem twp_func8_call_exact [WasmSmallStepGS hlc Universal.State]
    (oldPtr oldSize size : UInt32) (oldLayout layout : AllocLayout)
    (heapId : GName) (oldId : Nat) (oldBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (base finish : UInt32) (pages cap : Nat)
    (input output : List UInt8) (raised : Bool)
    (hlayout : oldLayout.Matches oldSize 1 ∧ layout.Matches size 1 ∧
      oldLayout.Valid ∧ layout.Valid ∧ oldLayout.alignment = 1 ∧
      oldLayout.size < layout.size)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hpages : pages ≤ cap) (hhard : cap ≤ Module.memoryHardCap)
    (hfit : (allocatorRequiredPages finish).toNat ≤ cap)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    CallContract 11 [.i32 size, .i32 1, .i32 oldSize, .i32 oldPtr]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗ memoryCapOwn 0 cap ∗
        memoryPagesHalf pages ∗
        BumpHeap heapId storedCursor frontier history ∗
        LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗ Streams input output raised ∗
        (∀ bytes : List UInt8, RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
          BumpHeap heapId finish finish.toNat (history.reallocate oldId oldPtr oldLayout base layout) -∗
          LiveBlock heapId history.nextId base layout bytes -∗
          ⌜bytes.take (min oldLayout.size layout.size) =
            oldBytes.take (min oldLayout.size layout.size)⌝ -∗
          Streams input output raised -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) := by
  unfold CallContract
  iintro ⟨Hruntime, Hcap, Hexact, Hbump, HoldBlock, Hstreams, Hcont⟩
  have Hprefix := Func8Proof.twp_func8_call_to_memorySize
    oldPtr oldSize size oldLayout layout heapId storedCursor frontier history base finish hlayout hclassify
    (callerLocals := callerLocals) (stack := stack) (code := code) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract at Hprefix
  iapply Hprefix
  iframe Hruntime Hbump
  iintro Hruntime Hbump
  iopen_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [BumpHeap] at Hbump
  icases Hbump with ⟨Hcursor, Hfrontier, Hauth, Hretired, %ownedPages, HoldPages, %hheap⟩
  rcases hheap with ⟨hfrontierLow, _, _, _, hwf, _⟩
  have hmatches : layout.Matches size 1 := hlayout.2.1
  have hvalid : layout.Valid := hlayout.2.2.2.1
  have halignment : layout.alignment = 1 := by simpa using hmatches.2.symm
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  have hfinishSigned : finish.toNat < 2147483648 := by
    dsimp only at hfacts
    omega
  rcases classifyBump_success_reachable frontier layout base finish
      hfrontierLow hvalid (Or.inl halignment) hclassify with
    ⟨hbaseFresh, _, _, hallocWord, _, hfinishExact, _⟩
  have hpagesWord : pages.toUInt32.toNat = pages :=
    UInt32.toNat_ofNat_of_lt' ((hpages.trans hhard).trans_lt (by decide))
  have hrequiredCovers := allocatorRequiredPages_covers finish hfinishSigned
  unfold Func8Proof.func8MemorySizeExpr
  simp only [Project.Mergesort.func8]
  ihave HsizeFrame : iprop(
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
      memoryCapOwn 0 cap ∗
      pointsTo_u32 0 allocatorCursor storedCursor ∗
      heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
      RetiredBytes heapId history ∗ LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
      Streams input output raised ∗
      (∀ bytes : List UInt8, RuntimeContext -∗ memoryCapOwn 0 cap -∗
        memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
        BumpHeap heapId finish finish.toNat
          (history.reallocate oldId oldPtr oldLayout base layout) -∗
        LiveBlock heapId history.nextId base layout bytes -∗
          ⌜bytes.take (min oldLayout.size layout.size) =
            oldBytes.take (min oldLayout.size layout.size)⌝ -∗ Streams input output raised -∗
        ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) $$
      [Henv Hcap Hcursor Hfrontier Hauth Hretired HoldBlock Hstreams Hcont]
  · iframe
  iapply twp_memorySize_exact Project.Mergesort.module ⟨0⟩ pages $$ HsizeFrame Hmodule Hexact
  iintro HsizeFrame Hmodule Hexact
  icases HsizeFrame with ⟨Henv, Hcap, Hcursor, Hfrontier, Hauth, Hretired, HoldBlock, Hstreams, Hcont⟩
  simp only [show Project.Mergesort.module.memIs64 = false by rfl,
    sizeValue, Bool.false_eq_true, ↓reduceIte]
  wasm_twp_pures [twp_localTee]
  simp
  by_cases hcovered : allocatorRequiredPages finish ≤ pages.toUInt32
  · have hle : (allocatorRequiredPages finish).toNat ≤ pages := by
      simpa only [hpagesWord] using UInt32.le_iff_toNat_le_toNat.mp hcovered
    have hphysical : finish.toNat ≤ pages * 65536 :=
      hrequiredCovers.trans (Nat.mul_le_mul_right 65536 hle)
    iapply twp_leU (result := 1) (by rw [if_pos hcovered])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave #Hpages := half_snapshot pages $$ Hexact
    isimp only [Nat.max_eq_left hle] at Hcont
    iclose_runtime Hruntime with Hmodule Henv
    let functionControls : List ControlFrame :=
      [{ kind := .block, paramArity := 0, resultArity := 0,
         body := match Project.Mergesort.func8 with
           | .block _ _ body :: _ => body
           | _ => [],
         continuation := [.call 9, .unreachable], belowStack := [] }]
    have Hclaim := Project.Mergesort.Func8Proof.twp_func8_claim_commit_copy_and_return
        oldPtr oldSize base size finish (allocatorRequiredPages finish) pages.toUInt32
        storedCursor oldLayout layout heapId oldId oldBytes frontier pages history
        input output raised
        (currentControls := functionControls)
        callerLocals stack code arity remainder controls calls s E Φ
        hfrontierLow hwf hlayout hclassify hbaseFresh hallocWord hfinishExact hphysical
    simp only [functionControls, Project.Mergesort.func8, allocatorCursor, Nat.toUInt32] at Hclaim
    simp only [allocatorCursor]
    iapply Hclaim
    iframe Hruntime Hcursor Hfrontier Hauth Hretired Hpages HoldBlock Hstreams
    iintro %bytes Hruntime Hbump Hblock %hcopy Hstreams
    iapply Hcont $$ %bytes Hruntime Hcap Hexact Hbump Hblock %hcopy Hstreams
  · have hlt : pages < (allocatorRequiredPages finish).toNat := by
      simpa only [hpagesWord] using
        UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hcovered)
    let delta := allocatorRequiredPages finish - pages.toUInt32
    have hdelta : delta.toNat = (allocatorRequiredPages finish).toNat - pages := by
      dsimp only [delta]
      rw [UInt32.toNat_sub_of_le, hpagesWord]
      rw [UInt32.le_iff_toNat_le_toNat, hpagesWord]
      omega
    have hnew : pages + delta.toNat = (allocatorRequiredPages finish).toNat := by
      rw [hdelta]
      omega
    iapply twp_leU (result := 0) (by rw [if_neg hcovered])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_sub]
    ihave HgrowFrame : iprop(
        hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
        pointsTo_u32 0 allocatorCursor storedCursor ∗
        heapFrontierOwn frontier ∗ AllocMetaAuth heapId history ∗
        RetiredBytes heapId history ∗ LiveBlock heapId oldId oldPtr oldLayout oldBytes ∗
        Streams input output raised ∗
        (∀ bytes : List UInt8, RuntimeContext -∗ memoryCapOwn 0 cap -∗
          memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
          BumpHeap heapId finish finish.toNat
            (history.reallocate oldId oldPtr oldLayout base layout) -∗
          LiveBlock heapId history.nextId base layout bytes -∗
            ⌜bytes.take (min oldLayout.size layout.size) =
              oldBytes.take (min oldLayout.size layout.size)⌝ -∗ Streams input output raised -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls calls s E Φ)) $$
        [Henv Hcursor Hfrontier Hauth Hretired HoldBlock Hstreams Hcont]
    · iframe
    iapply twp_memoryGrow_exact (delta := delta) Project.Mergesort.module ⟨0⟩ cap pages hmode
        (by simpa only [hnew] using hfit) $$ HgrowFrame Hmodule Hcap Hexact
    iintro HgrowFrame Hmodule Hcap Hexact
    icases HgrowFrame with ⟨Henv, Hcursor, Hfrontier, Hauth, Hretired, HoldBlock, Hstreams, Hcont⟩
    isimp only [hnew] at Hexact
    have hnotSentinel : pages.toUInt32 ≠ (0xFFFFFFFF : UInt32) :=
      capped_growth_previous_ne_failure pages (allocatorRequiredPages finish).toNat cap
        delta hnew.symm hfit hhard
    wasm_twp_pures [twp_const]
    iapply twp_eq (result := 0) (by simp [hnotSentinel])
    wasm_twp_pures [twp_brIfZero twp_exitControl] using [List.take_zero, List.nil_append]
    ihave #Hpages := half_snapshot (allocatorRequiredPages finish).toNat $$ Hexact
    isimp only [Nat.max_eq_right (Nat.le_of_lt hlt)] at Hcont
    iclose_runtime Hruntime with Hmodule Henv
    let functionControls : List ControlFrame :=
      [{ kind := .block, paramArity := 0, resultArity := 0,
         body := match Project.Mergesort.func8 with
           | .block _ _ body :: _ => body
           | _ => [],
         continuation := [.call 9, .unreachable], belowStack := [] }]
    have Hclaim := Project.Mergesort.Func8Proof.twp_func8_claim_commit_copy_and_return
        oldPtr oldSize base size finish (allocatorRequiredPages finish) pages.toUInt32
        storedCursor oldLayout layout heapId oldId oldBytes frontier (allocatorRequiredPages finish).toNat history
        input output raised
        (currentControls := functionControls)
        callerLocals stack code arity remainder controls calls s E Φ
        hfrontierLow hwf hlayout hclassify hbaseFresh hallocWord hfinishExact hrequiredCovers
    simp only [functionControls, Project.Mergesort.func8, allocatorCursor, Nat.toUInt32] at Hclaim
    simp only [allocatorCursor]
    iapply Hclaim
    iframe Hruntime Hcursor Hfrontier Hauth Hretired Hpages HoldBlock Hstreams
    iintro %bytes Hruntime Hbump Hblock %hcopy Hstreams
    iapply Hcont $$ %bytes Hruntime Hcap Hexact Hbump Hblock %hcopy Hstreams

end Project.Mergesort.ExactAllocator
