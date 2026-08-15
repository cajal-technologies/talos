import Project.Mergesort.SliceProof

/-!
# Total contracts for generated slice range helpers

The generated `Range` helper (`func7`) owns a sixteen-byte shadow-stack
frame.  `RangeTo` (`func8`) is a thin wrapper which calls it with start index
zero.  The contracts below retain ownership of the stack-pointer global and
of every word touched in that frame, making them suitable for composition
inside the recursive mergesort proof.
-/

namespace Project.Mergesort.RangeProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine

theorem pointsTo_u32_add_zero
    [WasmSmallStepGS hlc] (address value : UInt32) :
    pointsTo_u32 (address + UInt32.ofNat 0) value ⊢
      pointsTo_u32 address value := by
  rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]

private theorem pointsTo_u32_shift_three
    [WasmSmallStepGS hlc] (address data start : UInt32) :
    pointsTo_u32 address (data + (start <<< (3 % 32))) ⊢
      pointsTo_u32 address (data + (start <<< 3)) := by
  rw [show (3 % 32 : UInt32) = 3 by decide]

private theorem pointsTo_u32_zero_offset
    [WasmSmallStepGS hlc] (address data : UInt32) :
    pointsTo_u32 (address + UInt32.ofNat 0)
        (data + ((0 : UInt32) <<< (3 % 32))) ⊢
      pointsTo_u32 address data := by
  rw [show address + UInt32.ofNat 0 = address by
      rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero],
    show data + ((0 : UInt32) <<< (3 % 32)) = data by bv_decide]

private theorem pointsTo_u32_rangeTo_length
    [WasmSmallStepGS hlc] (frame stop : UInt32) :
    pointsTo_u32 ((frame + 8) + 4) (stop - (0 : UInt32)) ⊢
      pointsTo_u32 (frame + 12) stop := by
  rw [show (frame + 8) + 4 = frame + 12 by bv_decide,
    show stop - (0 : UInt32) = stop by bv_decide]

private theorem pointsTo_u32_sub_zero
    [WasmSmallStepGS hlc] (address value : UInt32) :
    pointsTo_u32 address (value - (0 : UInt32)) ⊢
      pointsTo_u32 address value := by
  rw [show value - (0 : UInt32) = value by bv_decide]

theorem twp_globalGet0
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    globalPointsTo 0 value ∗
      (globalPointsTo 0 value -∗
        WP (.running
          ⟨⟨params, localValues, value :: values⟩, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩, .globalGet 0 :: code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Htwp⟩
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hget :
      ⌜store.wasm.globals.globals[0]? = some value⌝ $$ [Hσ Hglobal]
  · imod stateInterp_global_facts store ns obs nt 0 value $$
        [$Hσ $Hglobal] with %Hget
    ipureintro
    exact Hget
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, value :: values⟩, code,
          arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.globalGet 0), rfl,
        Step.globalGet (by simpa [globalAt?] using Hget)⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.globalGet (α := α) (by
      simpa [globalAt?] using Hget)) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hglobal

theorem twp_globalSet0
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {oldValue newValue : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    globalPointsTo 0 oldValue ∗
      (globalPointsTo 0 newValue -∗
        WP (.running
          ⟨⟨params, localValues, values⟩, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, newValue :: values⟩, .globalSet 0 :: code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Htwp⟩
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hget :
      ⌜store.wasm.globals.globals[0]? = some oldValue⌝ $$ [Hσ Hglobal]
  · imod stateInterp_global_facts store ns obs nt 0 oldValue $$
        [$Hσ $Hglobal] with %Hget
    ipureintro
    exact Hget
  have hsome : (globalAt? store 0).isSome = true := by
    simp [globalAt?, Hget]
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with globals :=
            { globals := store.wasm.globals.globals.set 0 newValue } } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, values⟩, code,
          arity, remainder, controls, calls⟩,
      updatedStore, [], ⟨rfl, .instruction (.globalSet 0), rfl, by
        dsimp [updatedStore]
        exact Step.globalSet hsome⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, newValue :: values⟩,
          .globalSet 0 :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.globalSet 0))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ := by
    dsimp [updatedStore]
    exact Step.globalSet hsome
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_global_set store ns obs nt
      0 oldValue newValue $$ [$Hσ $Hglobal] with ⟨Hσ, Hglobal⟩
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hglobal

private theorem slotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 16 ≤ UInt32.size)
    (hoffset : offset ≤ 12) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private theorem resultSlotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 8 ≤ UInt32.size)
    (hoffset : offset ≤ 4) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private def rangeParams
    (resultPtr start stop dataPtr length sourceLoc : UInt32) : List Value :=
  [.i32 resultPtr, .i32 start, .i32 stop, .i32 dataPtr,
    .i32 length, .i32 sourceLoc]

private def rangeLocals
    (frame resultLength resultData : UInt32) : List Value :=
  [.i32 frame, .i32 resultLength, .i32 resultData]

/-- Call-stack-polymorphic total contract for generated `func7`, on its
non-panicking path `start ≤ stop ≤ length`. -/
theorem range_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr start stop dataPtr length sourceLoc stackTop : UInt32)
    (oldResultPtr oldResultLength oldFrame8 oldFrame12 : UInt32)
    (hstartStop : start ≤ stop) (hstopLength : stop ≤ length)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 resultPtr oldResultPtr ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      ((globalPointsTo 0 (.i32 stackTop) ∗
        pointsTo_u32 ((stackTop - 16) + 8) 1 ∗
        pointsTo_u32 ((stackTop - 16) + 12) (stop - start) ∗
        pointsTo_u32 (resultPtr + UInt32.ofNat 0)
          (dataPtr + (start <<< (3 % 32))) ∗
        pointsTo_u32 (resultPtr + 4) (stop - start)) -∗
        ∀ controls : List ControlFrame,
          WP (.running
            ⟨⟨rangeParams resultPtr start stop dataPtr length sourceLoc,
                rangeLocals (stackTop - 16) (stop - start)
                  ((start <<< (3 % 32)) + dataPtr), []⟩,
              [.ret], 0, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨rangeParams resultPtr start stop dataPtr length sourceLoc,
          rangeLocals 0 0 0, []⟩,
        func7, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 16
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    slotFacts frame 8 hframeRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    slotFacts frame 12 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    resultSlotFacts resultPtr 0 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    resultSlotFacts resultPtr 4 hresultRoom (by decide)
  have hnotStart : ¬stop < start := by
    exact not_lt_of_ge hstartStop
  iintro ⟨Hglobal, Hframe8, Hframe12, HresultPtr,
    HresultLength, Hcont⟩
  simp only [func7]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [rangeParams, rangeLocals]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU (result := 0) (by simp [hnotStart])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_store32 oldFrame12 hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldFrame8 hf80 hf81 hf82 hf83 $$ Hframe8
  iintro Hframe8
  iapply twp_localGet rfl
  iapply twp_load32 (stop - start) hf120 hf121 hf122 hf123 $$ Hframe12
  iintro Hframe12
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_leU (result := 1) (by simp [hstopLength])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) rfl
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldResultLength hr40 hr41 hr42 hr43 $$ HresultLength
  iintro HresultLength
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HresultPtr' : pointsTo_u32 (resultPtr + 0) oldResultPtr $$
      [HresultPtr]
  · rw [UInt32.add_zero]
    iexact HresultPtr
  iapply twp_store32 oldResultPtr hr0 hr1 hr2 hr3 $$ HresultPtr'
  iintro HresultPtr
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [List.set, frame, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave HresultPtrExpected :
      pointsTo_u32 (resultPtr + UInt32.ofNat 0)
        (dataPtr + (start <<< (3 % 32))) $$ [HresultPtr]
  · rw [UInt32.add_comm dataPtr]
    iexact HresultPtr
  ihave HglobalExpected : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (16 : UInt32) + (stackTop - 16) = stackTop by bv_decide]
    iexact Hglobal
  ihave Hframe8Expected :
      pointsTo_u32 ((stackTop - 16) + 8) 1 $$ [Hframe8]
  · rw [show (stackTop - 16) + 8 = frame + UInt32.ofNat 8 by rfl]
    iexact Hframe8
  ihave Hframe12Expected :
      pointsTo_u32 ((stackTop - 16) + 12) (stop - start) $$ [Hframe12]
  · rw [show (stackTop - 16) + 12 = frame + UInt32.ofNat 12 by rfl]
    iexact Hframe12
  ihave HresultLengthExpected :
      pointsTo_u32 (resultPtr + 4) (stop - start) $$ [HresultLength]
  · rw [show resultPtr + 4 = resultPtr + UInt32.ofNat 4 by rfl]
    iexact HresultLength
  ispecialize Hcont $$ [HglobalExpected Hframe8Expected Hframe12Expected
    HresultPtrExpected HresultLengthExpected]
  · iframe
  ispecialize Hcont $$ %_
  iapply Hcont

/-- Total call rule for `func7` at its generated absolute function index. -/
theorem range_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr start stop dataPtr length sourceLoc stackTop : UInt32)
    (oldResultPtr oldResultLength oldFrame8 oldFrame12 : UInt32)
    (hstartStop : start ≤ stop) (hstopLength : stop ≤ length)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldFrame12 ∗
      pointsTo_u32 resultPtr oldResultPtr ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 8) 1 -∗
        pointsTo_u32 ((stackTop - 16) + 12) (stop - start) -∗
        pointsTo_u32 (resultPtr + UInt32.ofNat 0)
          (dataPtr + (start <<< (3 % 32))) -∗
        pointsTo_u32 (resultPtr + 4) (stop - start) -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 sourceLoc, .i32 length, .i32 dataPtr, .i32 stop,
            .i32 start, .i32 resultPtr] ++ stack },
        .call 9 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hframe8, Hframe12, HresultPtr,
    HresultLength, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 9 rangeFunction
      (by decide) range_index $$ Hruntime
  iintro Hruntime
  simp [rangeFunction, func7Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  have Hbody := range_body_twp (α := α)
    resultPtr start stop dataPtr length sourceLoc stackTop
    oldResultPtr oldResultLength oldFrame8 oldFrame12
    hstartStop hstopLength hframeRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [rangeParams, rangeLocals] at Hbody
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hframe8]
  · iexact Hframe8
  isplitl [Hframe12]
  · iexact Hframe12
  isplitl [HresultPtr]
  · iexact HresultPtr
  isplitl [HresultLength]
  · iexact HresultLength
  iintro Hpost
  iintro %calleeControls
  icases Hpost with ⟨Hglobal, Hframe8, Hframe12, HresultPtr,
    HresultLength⟩
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append,
    List.drop_eq_nil_of_le (by decide : 6 ≤
      [.i32 sourceLoc, .i32 length, .i32 dataPtr, .i32 stop,
        .i32 start, .i32 resultPtr].length)]
  ihave HresultPtrPlain :
      pointsTo_u32 resultPtr (dataPtr + (start <<< (3 % 32))) $$
      [HresultPtr]
  · iapply pointsTo_u32_add_zero
    iexact HresultPtr
  ihave HresultPtrCall :
      pointsTo_u32 resultPtr (dataPtr + (start <<< 3)) $$
      [HresultPtrPlain]
  · iapply pointsTo_u32_shift_three
    iexact HresultPtrPlain
  ispecialize Hcont $$ Hruntime Hglobal Hframe8 Hframe12 HresultPtrCall
    HresultLength
  iapply Hcont

private def rangeToParams
    (resultPtr dataPtr stop length sourceLoc : UInt32) : List Value :=
  [.i32 resultPtr, .i32 stop, .i32 dataPtr, .i32 length, .i32 sourceLoc]

private def rangeToLocals
    (frame start resultData : UInt32) : List Value :=
  [.i32 frame, .i32 start, .i32 resultData]

/-- Call-stack-polymorphic total contract for generated `func8`, the
`RangeTo` wrapper.  Besides its own frame, the precondition exposes the two
words in the nested `func7` frame, so all stack memory remains explicit. -/
theorem rangeTo_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr dataPtr stop length sourceLoc stackTop : UInt32)
    (oldResultPtr oldResultLength oldOuter8 oldOuter12
      oldInner8 oldInner12 : UInt32)
    (hstopLength : stop ≤ length)
    (houterRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hinnerRoom : ((stackTop - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldOuter8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldOuter12 ∗
      pointsTo_u32 (((stackTop - 16) - 16) + 8) oldInner8 ∗
      pointsTo_u32 (((stackTop - 16) - 16) + 12) oldInner12 ∗
      pointsTo_u32 resultPtr oldResultPtr ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      ((runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 stackTop) ∗
        pointsTo_u32 ((stackTop - 16) + 8) dataPtr ∗
        pointsTo_u32 ((stackTop - 16) + 12) stop ∗
        pointsTo_u32 (((stackTop - 16) - 16) + 8) 1 ∗
        pointsTo_u32 (((stackTop - 16) - 16) + 12) stop ∗
        pointsTo_u32 resultPtr dataPtr ∗
        pointsTo_u32 (resultPtr + 4) stop) -∗
        ∀ controls : List ControlFrame,
          WP (.running
            ⟨⟨rangeToParams resultPtr dataPtr stop length sourceLoc,
                rangeToLocals (stackTop - 16) 0 dataPtr, []⟩,
              [.ret], 0, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨rangeToParams resultPtr dataPtr stop length sourceLoc,
          rangeToLocals 0 0 0, []⟩,
        func8, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let outer := stackTop - 16
  let inner := outer - 16
  obtain ⟨ho80, ho81, ho82, ho83⟩ :=
    slotFacts outer 8 houterRoom (by decide)
  obtain ⟨ho120, ho121, ho122, ho123⟩ :=
    slotFacts outer 12 houterRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3⟩ :=
    resultSlotFacts resultPtr 0 hresultRoom (by decide)
  obtain ⟨hr40, hr41, hr42, hr43⟩ :=
    resultSlotFacts resultPtr 4 hresultRoom (by decide)
  have houterResultRoom : (outer + 8).toNat + 8 ≤ UInt32.size := by
    rw [show outer + 8 = outer + UInt32.ofNat 8 by rfl]
    rw [ho80]
    omega
  iintro ⟨Hruntime, Hglobal, Houter8, Houter12, Hinner8, Hinner12,
    HresultPtr, HresultLength, Hcont⟩
  simp only [func8]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [rangeToParams, rangeToLocals, List.set, List.length_cons,
    List.length_nil, Nat.reduceSub, Nat.reduceAdd]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  have Hrange := range_call_twp (α := α)
    (outer + 8) 0 stop dataPtr length sourceLoc outer
    oldOuter8 oldOuter12 oldInner8 oldInner12
    (by simp) hstopLength hinnerRoom houterResultRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨rangeToParams resultPtr dataPtr stop length sourceLoc,
        rangeToLocals outer 0 0, []⟩)
    (stack := [])
    (code :=
      [.localGet 5, .load32 8, .localSet 7,
        .localGet 0, .localGet 5, .load32 12, .store32 4,
        .localGet 0, .localGet 7, .store32 0,
        .localGet 5, .const 16, .add, .globalSet 0, .ret])
    (arity := 0) (remainder := []) (controls := []) (calls := calls)
  simp only [rangeToParams, rangeToLocals, outer, List.append_nil] at Hrange
  simp only [List.set, List.length_cons, List.length_nil]
  rw [UInt32.add_comm 8 outer]
  iapply Hrange
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinner8]
  · rw [show (outer - 16) + 8 = ((stackTop - 16) - 16) + 8 by rfl]
    iexact Hinner8
  isplitl [Hinner12]
  · rw [show (outer - 16) + 12 = ((stackTop - 16) - 16) + 12 by rfl]
    iexact Hinner12
  isplitl [Houter8]
  · iexact Houter8
  isplitl [Houter12]
  · rw [show (outer + 8) + 4 = outer + 12 by bv_decide]
    rw [show outer + 12 = (stackTop - 16) + 12 by rfl]
    iexact Houter12
  iintro Hruntime Hglobal Hinner8 Hinner12 Houter8 Houter12
  ihave Houter8Plain : pointsTo_u32 (outer + 8) dataPtr $$ [Houter8]
  · iapply pointsTo_u32_zero_offset
    iexact Houter8
  ihave Houter12Plain : pointsTo_u32 (outer + 12) stop $$ [Houter12]
  · iapply pointsTo_u32_rangeTo_length
    iexact Houter12
  ihave Hinner12Plain :
      pointsTo_u32 (((stackTop - 16) - 16) + 12) stop $$ [Hinner12]
  · iapply pointsTo_u32_sub_zero
    iexact Hinner12
  iapply twp_localGet rfl
  iapply twp_load32 dataPtr ho80 ho81 ho82 ho83 $$ Houter8Plain
  iintro Houter8
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 stop ho120 ho121 ho122 ho123 $$ Houter12Plain
  iintro Houter12
  iapply twp_store32 oldResultLength hr40 hr41 hr42 hr43 $$ HresultLength
  iintro HresultLength
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HresultPtr0 : pointsTo_u32 (resultPtr + 0) oldResultPtr $$
      [HresultPtr]
  · rw [UInt32.add_zero]
    iexact HresultPtr
  iapply twp_store32 oldResultPtr hr0 hr1 hr2 hr3 $$ HresultPtr0
  iintro HresultPtr
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [List.set, List.length_cons, List.length_nil, Nat.reduceSub,
    Nat.reduceAdd, outer]
  ihave HresultPtrPlain : pointsTo_u32 resultPtr dataPtr $$ [HresultPtr]
  · iapply pointsTo_u32_add_zero
    iexact HresultPtr
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (16 : UInt32) + (stackTop - 16) = stackTop by bv_decide]
    iexact Hglobal
  ispecialize Hcont $$ [Hruntime HglobalTop Houter8 Houter12 Hinner8
    Hinner12Plain HresultPtrPlain HresultLength]
  · iframe
  ispecialize Hcont $$ %_
  iapply Hcont

/-- Total call rule for `func8` (`RangeTo`) at its generated absolute function
index.  The rule preserves the caller state and exposes both stack frames used
by the wrapper and its nested `func7` call. -/
theorem rangeTo_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr dataPtr stop length sourceLoc stackTop : UInt32)
    (oldResultPtr oldResultLength oldOuter8 oldOuter12
      oldInner8 oldInner12 : UInt32)
    (hstopLength : stop ≤ length)
    (houterRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hinnerRoom : ((stackTop - 16) - 16).toNat + 16 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 8 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldOuter8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldOuter12 ∗
      pointsTo_u32 (((stackTop - 16) - 16) + 8) oldInner8 ∗
      pointsTo_u32 (((stackTop - 16) - 16) + 12) oldInner12 ∗
      pointsTo_u32 resultPtr oldResultPtr ∗
      pointsTo_u32 (resultPtr + 4) oldResultLength ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 ((stackTop - 16) + 8) dataPtr -∗
        pointsTo_u32 ((stackTop - 16) + 12) stop -∗
        pointsTo_u32 (((stackTop - 16) - 16) + 8) 1 -∗
        pointsTo_u32 (((stackTop - 16) - 16) + 12) stop -∗
        pointsTo_u32 resultPtr dataPtr -∗
        pointsTo_u32 (resultPtr + 4) stop -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 sourceLoc, .i32 length, .i32 dataPtr, .i32 stop,
            .i32 resultPtr] ++ stack },
        .call 10 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Houter8, Houter12, Hinner8, Hinner12,
    HresultPtr, HresultLength, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 10 rangeToFunction
      (by decide) rangeTo_index $$ Hruntime
  iintro Hruntime
  simp [rangeToFunction, func8Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  have Hbody := rangeTo_body_twp (α := α)
    resultPtr dataPtr stop length sourceLoc stackTop
    oldResultPtr oldResultLength oldOuter8 oldOuter12 oldInner8 oldInner12
    hstopLength houterRoom hinnerRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [rangeToParams, rangeToLocals] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Houter8]
  · iexact Houter8
  isplitl [Houter12]
  · iexact Houter12
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [HresultPtr]
  · iexact HresultPtr
  isplitl [HresultLength]
  · iexact HresultLength
  iintro Hpost
  iintro %calleeControls
  icases Hpost with ⟨Hruntime, Hglobal, Houter8, Houter12, Hinner8,
    Hinner12, HresultPtr, HresultLength⟩
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append,
    List.drop_eq_nil_of_le (by decide : 5 ≤
      [.i32 resultPtr, .i32 stop, .i32 dataPtr, .i32 length,
        .i32 sourceLoc].length)]
  ispecialize Hcont $$ Hruntime Hglobal Houter8 Houter12 Hinner8 Hinner12
    HresultPtr HresultLength
  iapply Hcont

end Project.Mergesort.RangeProof
