import Project.Mergesort.ExactReadLoop

/-!
# Values and scratch allocation with a linear physical-page bound

The closed input-size condition supplies arithmetic acceptance and capacity
room. Both generated work-array calls return the exact updated page token.
-/

namespace Project.Mergesort.ExactWorkAllocators

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Contracts Project.Mergesort.Representations
open Project.Mergesort.DriverProof Project.Mergesort.MemoryBounds
open Project.Mergesort.BoundedDriverFacts
open scoped Wasm.SmallStep.Outcome

/-- Physical capacity sufficient for all retained input and work allocations. -/
def programPageBound (original : List UInt32) : Nat :=
  max 17 ((workArraysFrontierBound (serialize original).length + 65535) / 65536)

/-- The program carries one exact page token and a closed upper bound. -/
def ProgramPages [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) : HeapIProp :=
  iprop(memoryCapOwn 0 Module.memoryHardCap ∗ ∃ pages : Nat,
    ⌜pages ≤ programPageBound original⌝ ∗ memoryPagesHalf pages)

theorem programPageBound_le_cap (original : List UInt32)
    (hfit : WorkArraysFit (serialize original).length) :
    programPageBound original ≤ Module.memoryHardCap := by
  unfold programPageBound Module.memoryHardCap
  unfold WorkArraysFit at hfit
  omega

/-- Widen the input phase's bound while retaining its linear token. -/
theorem readPages_to_programPages [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) :
    ExactReadLoop.ReadPages original ⊢ ProgramPages original := by
  have hbound : ExactReadLoop.readPageBound original ≤ programPageBound original := by
    unfold ExactReadLoop.readPageBound programPageBound workArraysFrontierBound
    omega
  iintro Hpages
  isimp only [ExactReadLoop.ReadPages] at Hpages
  icases Hpages with ⟨Hcap, %pages, %hpages, Hexact⟩
  unfold ProgramPages
  iframe Hcap
  iexists pages
  iframe_pureexact (hpages.trans hbound)

/-- The generated ceiling calculation stays inside the program bound. -/
theorem requiredPages_le_programPageBound
    (original : List UInt32) (frontier : Nat) (layout : AllocLayout)
    (base finish : UInt32)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hfinish : finish.toNat ≤ workArraysFrontierBound (serialize original).length) :
    (allocatorRequiredPages finish).toNat ≤ programPageBound original := by
  have hfacts := classifyBump_success_facts frontier layout base finish hclassify
  have hsigned : finish.toNat < 2147483648 := by
    dsimp only at hfacts
    omega
  rw [allocatorRequiredPages_toNat finish hsigned]
  unfold programPageBound
  omega

/-- Reseal the exact updated count after an accepted work-array allocation. -/
theorem programPages_after_allocation [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) (frontier : Nat) (layout : AllocLayout)
    (base finish : UInt32) (pages : Nat)
    (hpages : pages ≤ programPageBound original)
    (hclassify : classifyBump frontier layout = .success base finish)
    (hfinish : finish.toNat ≤ workArraysFrontierBound (serialize original).length) :
    iprop(memoryCapOwn 0 Module.memoryHardCap ∗
      memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat)) ⊢
      ProgramPages original := by
  iintro ⟨Hcap, Hexact⟩
  unfold ProgramPages
  iframe Hcap
  iexists max pages (allocatorRequiredPages finish).toNat
  iframe_pureexact (max_le hpages
    (requiredPages_le_programPageBound original frontier layout base finish hclassify hfinish))

theorem allocate_values
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (original : List UInt32)
    (capacity dataPtr : UInt32)
    (completed chunkBytes outputBytes shadow : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (horiginal : original ≠ [])
    (hcompleted : serialize original = completed)
    (hgeo : BoundedGeometricVecFacts (serialize original).length completed.length 0
      capacity dataPtr frontier history)
    (callerLocals : Locals)
    (hlocal7 : callerLocals.get 7 =
      some (.i32 (UInt32.ofNat completed.length)))
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := completed.length, alignment := 4 }
    iprop(ProgramPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr completed chunkBytes outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      (∀ base : UInt32, ∀ finish : UInt32, ∀ bytes : List UInt8,
          ⌜classifyBump frontier layout = .success base finish⌝ -∗
          ProgramPages original -∗
          RuntimeContext -∗
          StackPointer driverBase -∗
          StackReserve reserveBase shadow -∗
          ExportFrame heapId capacity dataPtr completed chunkBytes
            outputBytes -∗
          BumpHeap heapId finish finish.toNat
            (history.allocate base layout) -∗
          LiveBlock heapId history.nextId base layout bytes -∗
          Streams [] [] false -∗
          ResumeWP [.i32 base] callerLocals stack code arity remainder controls
            calls s E Φ)) ⊢
      WP (.running
        ⟨{ callerLocals with values := stack },
          [.call 7, .localGet 7, .const 4, .call 8] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := completed.length, alignment := 4 }
  have hboundTotal := GeometricVecFacts.completed_lt_signed
    (serialize original).length completed.length 0 capacity dataPtr frontier
    history hgeo.1 rfl
  have hbound : completed.length < 2147483648 := by simpa [hcompleted] using hboundTotal
  have halign : completed.length % 4 = 0 := by
    rw [← hcompleted, serialize_length]; omega
  have hpositive : 0 < completed.length := by
    rw [← hcompleted, serialize_length]
    have := List.length_pos_iff_ne_nil.mpr horiginal
    omega
  have hlengthWord :
      (UInt32.ofNat completed.length).toNat = completed.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size] at hbound ⊢; omega
  have hlayoutValid : layout.Valid := Project.Mergesort.Representations.align4Layout_valid_of_bounds
      completed.length hpositive hbound halign
  have hlayoutMatches :
      layout.Matches (UInt32.ofNat completed.length) 4 := by
    unfold AllocLayout.Matches layout
    simp only [hlengthWord]; decide
  have hgeoOriginal : BoundedGeometricVecFacts (serialize original).length
      (serialize original).length 0 capacity dataPtr frontier history := by
    simpa only [hcompleted] using hgeo
  obtain ⟨base, finish, scratch, scratchFinish, hclassify, _hscratch, _hscratchBound⟩ :=
    BoundedGeometricVecFacts.workArrays_classify_success
      (serialize original).length capacity dataPtr frontier history hgeoOriginal hfit
  have hclassify' : classifyBump frontier layout = .success base finish := by
    simpa only [layout, hcompleted] using hclassify
  have hfinish := BoundedDriverFacts.ScratchLineage.frontier_le
    (BoundedDriverFacts.ScratchLineage.of_values_allocation hgeoOriginal hclassify)
  have hrequired := requiredPages_le_programPageBound original frontier layout base finish
    hclassify' hfinish
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hcont⟩
  isimp only [ProgramPages] at Hpages
  icases Hpages with ⟨Hcap, %pages, %hpages, Hexact⟩
  simp only [List.cons_append, List.nil_append]
  have Hmarker := Project.Mergesort.ContractProofs.func4_correct
      (hlc := hlc) (callerLocals := callerLocals) (stack := stack)
      (code := [.localGet 7, .const 4, .call 8] ++ code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func4Spec CallContract callExpr at Hmarker
  simp only [List.cons_append, List.nil_append] at Hmarker
  iapply_frame_intro Hmarker as Hruntime
  unfold ResumeWP resumeExpr
  simp only [List.cons_append, List.nil_append]
  have hlocal7' : ({ callerLocals with values := stack } : Locals).get 7 =
      some (.i32 (UInt32.ofNat completed.length)) := by simpa using hlocal7
  iapply twp_localGet hlocal7'
  wasm_twp_pures [twp_const]
  have Halloc := ExactAllocator.twp_func5_call_exact
    (UInt32.ofNat completed.length) 4 layout heapId storedCursor frontier history
    base finish pages Module.memoryHardCap [] [] false
    hlayoutMatches hlayoutValid (Or.inr rfl) hclassify' hmode
    (hpages.trans (programPageBound_le_cap original hfit)) (Nat.le_refl _)
    (hrequired.trans (programPageBound_le_cap original hfit))
    (callerLocals := callerLocals) (stack := stack) (code := code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  iapply Halloc
  isplitl_exacts [Hruntime Hcap Hexact Hbump Hstreams]
  iintro %bytes Hruntime Hcap Hexact Hbump Hblock Hstreams
  ihave Hpages := programPages_after_allocation original frontier layout base finish pages
    hpages hclassify' hfinish $$ [Hcap Hexact]
  · iframe
  ihave Hresume := Hcont $$ %base %finish %bytes %hclassify' Hpages Hruntime Hsp
    Hreserve Hframe Hbump Hblock Hstreams
  iunfold ResumeWP
  simp only [resumeExpr, List.cons_append, List.nil_append]
  iexact Hresume

theorem allocate_scratch
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId : Nat)
    (capacity source valuesPtr : UInt32)
    (original : List UInt32)
    (chunkBytes outputBytes shadow : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (final1 final3 final6 final5 final8 aux10 : UInt32)
    (hpositive : 0 < original.length)
    (hbyteBound : 4 * original.length < 2147483648)
    (hfrontier : heapBase.toNat ≤ frontier)
    (hvaluesEnd : valuesPtr.toNat + 4 * original.length ≤ frontier)
    (hlineage : ScratchLineage original capacity source valuesPtr
      valuesId frontier history)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize original).length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let layout : AllocLayout :=
      { size := 4 * original.length, alignment := 4 }
    let callerLocals :=
      func3AppendLocals final1 final3 final6 valuesPtr source final5
        (UInt32.ofNat (4 * original.length)) final8
        (UInt32.ofNat original.length) (UInt32.ofNat (4 * original.length)) []
    iprop(ProgramPages original ∗
      RuntimeContext ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity source (serialize original) chunkBytes
        outputBytes ∗
      LiveWordBlock heapId valuesId valuesPtr original ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] [] false ∗
      (∀ scratch : UInt32, ∀ finish : UInt32,
          ⌜classifyBump frontier layout = .success scratch finish⌝ -∗
          ProgramPages original -∗
          RuntimeContext -∗
          StackPointer driverBase -∗
          StackReserve reserveBase shadow -∗
          ExportFrame heapId capacity source (serialize original) chunkBytes
            outputBytes -∗
          LiveWordBlock heapId valuesId valuesPtr original -∗
          BumpHeap heapId finish finish.toNat
            (history.allocate scratch layout) -∗
          LiveBlock heapId history.nextId scratch layout
            (List.replicate layout.size 0) -∗
          Streams [] [] false -∗
          ⌜MemRegion.Disjoint
            ⟨valuesPtr, 4 * original.length⟩
            ⟨scratch, 4 * original.length⟩⌝ -∗
          ResumeWP [.i32 scratch] callerLocals [] code arity remainder controls
            calls s E Φ)) ⊢
      WP (.running
        ⟨func3AppendLocals final1 final3 final6 valuesPtr source final5
            (UInt32.ofNat (4 * original.length)) final8
            (UInt32.ofNat original.length) aux10 [],
          [.call 7, .localGet 9, .const 2, .shl, .localTee 10,
            .const 4, .call 12] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let layout : AllocLayout :=
    { size := 4 * original.length, alignment := 4 }
  let callerLocals :=
    func3AppendLocals final1 final3 final6 valuesPtr source final5
      (UInt32.ofNat (4 * original.length)) final8
      (UInt32.ofNat original.length) (UInt32.ofNat (4 * original.length)) []
  have hwordBound : 4 * original.length < UInt32.size := by
    norm_num [UInt32.size] at hbyteBound ⊢; omega
  have hsizeWord :
      (UInt32.ofNat (4 * original.length)).toNat = 4 * original.length :=
    UInt32.toNat_ofNat_of_lt' hwordBound
  have hlayoutValid : layout.Valid := align4Layout_valid_of_bounds (4 * original.length)
      (by omega) hbyteBound (by omega)
  have hlayoutMatches :
      layout.Matches (UInt32.ofNat (4 * original.length)) 4 := by
    unfold AllocLayout.Matches layout
    simp only [hsizeWord]; decide
  obtain ⟨scratch, finish, hclassify, hfinish⟩ :=
    BoundedDriverFacts.ScratchLineage.scratch_classify_success hlineage hfit
  have hclassify' : classifyBump frontier layout = .success scratch finish := by
    simpa only [layout, serialize_length] using hclassify
  have hrequired := requiredPages_le_programPageBound original frontier layout scratch finish
    hclassify' hfinish
  have hscratchStart : frontier ≤ scratch.toNat :=
    (classifyBump_success_reachable frontier layout scratch finish
      hfrontier hlayoutValid (Or.inr rfl) hclassify').1
  have hdisjoint : MemRegion.Disjoint
      ⟨valuesPtr, 4 * original.length⟩ ⟨scratch, 4 * original.length⟩ :=
    wordRegions_disjoint_of_order valuesPtr scratch original original
      (Nat.le_trans hvaluesEnd hscratchStart)
  iintro ⟨Hpages, Hruntime, Hsp, Hreserve, Hframe, Hvalues, Hbump, Hstreams, Hcont⟩
  isimp only [ProgramPages] at Hpages
  icases Hpages with ⟨Hcap, %pages, %hpages, Hexact⟩
  simp only [List.cons_append, List.nil_append]
  have Hmarker := Project.Mergesort.ContractProofs.func4_correct
    (hlc := hlc)
    (callerLocals := func3AppendLocals final1 final3 final6 valuesPtr source
      final5 (UInt32.ofNat (4 * original.length)) final8
      (UInt32.ofNat original.length) aux10 [])
    (stack := [])
    (code := [.localGet 9, .const 2, .shl, .localTee 10,
      .const 4, .call 12] ++ code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold Func4Spec CallContract callExpr at Hmarker
  simp only [List.cons_append, List.nil_append] at Hmarker
  simp only [func3AppendLocals] at Hmarker ⊢
  iapply_frame_intro Hmarker as Hruntime
  unfold ResumeWP resumeExpr
  simp only [List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_shl]
  have hbyteOffset : UInt32.ofNat (4 * original.length) =
      4 * UInt32.ofNat original.length := by
    rw [UInt32.ofNat_mul]; rfl
  rw [MemRegion.shl2_eq_mul4, ← hbyteOffset]
  wasm_twp_localTee [List.length, List.set]
  wasm_twp_pures [twp_const]
  have Halloc := ExactAllocator.twp_func9_call_exact
    (UInt32.ofNat (4 * original.length)) layout heapId storedCursor frontier history
    scratch finish pages Module.memoryHardCap [] [] false
    hlayoutMatches hlayoutValid hclassify' hmode
    (hpages.trans (programPageBound_le_cap original hfit)) (Nat.le_refl _)
    (hrequired.trans (programPageBound_le_cap original hfit))
    (callerLocals := callerLocals) (stack := []) (code := code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  dsimp only [callerLocals] at Halloc
  simp only [func3AppendLocals] at Halloc
  iapply Halloc
  isplitl_exacts [Hruntime Hcap Hexact Hbump Hstreams]
  iintro Hruntime Hcap Hexact Hbump Hscratch Hstreams
  ihave Hpages := programPages_after_allocation original frontier layout scratch finish pages
    hpages hclassify' hfinish $$ [Hcap Hexact]
  · iframe
  ihave Hresume := Hcont $$ %scratch %finish %hclassify' Hpages Hruntime Hsp Hreserve
    Hframe Hvalues Hbump Hscratch Hstreams %hdisjoint
  iunfold ResumeWP
  simp only [resumeExpr, List.cons_append, List.nil_append]
  iexact Hresume

end Project.Mergesort.ExactWorkAllocators
