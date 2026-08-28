import CodeLib.SepLogic.SmallStepTotalLifting

/-!
Total-WP rules missing from the public lifting layer but needed by the
byte-oriented Rust code in this challenge.  They are the total counterparts
of CodeLib's `wp_load8U` and `wp_store8`: the physical step and ghost-memory
update are identical, while the recursive continuation has no later.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
local instance instSubmissionWasmTotalIrisGS :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) :=
  instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}

/-- Resume a suspended same-instance caller when a callee falls through. -/
theorem hdtwp_returnFromCallFallthrough
    {calleeLocals callerLocals : Locals}
    {callerCode : Program}
    {calleeArity callerArity : Nat}
    {calleeRemainder callerRemainder : List Value}
    {callerControls : List ControlFrame}
    {returningInstance : ModuleInstanceId}
    {module : Module}
    {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := callerLocals
        continuation := callerCode
        resultArity := callerArity
        callerRemainder := callerRemainder
        control := callerControls
        returningInstance := returningInstance }
    let current : ThreadState α :=
      ⟨calleeLocals, [], calleeArity, calleeRemainder,
        [], caller :: calls⟩
    let next : ThreadState α :=
      ⟨{ callerLocals with
          values :=
            calleeLocals.values.take calleeArity ++ callerLocals.values },
        callerCode, callerArity, callerRemainder, callerControls, calls⟩
    runtimeModuleOwn returningInstance module -∗
    (runtimeModuleOwn returningInstance module -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hruntime Hwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  ihave %Hentry : ⌜store.runtime.entry = returningInstance⌝ $$ [Hσ HinstanceOwn]
  · imod stateInterp_currentInstance_agree store ns obs nt returningInstance $$
        [$Hσ $HinstanceOwn] with %Hentry
    ipureintro
    exact Hentry
  have hsame : returningInstance = store.runtime.entry := Hentry.symm
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨_, store, [],
      ⟨rfl, _, rfl, Step.returnFromCallFallthrough hsame⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.returnFromCallFallthrough (α := α) hsame) wasmStep
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
  · simp only [resumeCaller]
    iapply Hwp
    isplitl [HruntimeElem]
    · iexact HruntimeElem
    · iexact HinstanceOwn

/-- Total primitive rule for `i32.load8_u`. -/
theorem twp_load8U
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hpt Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts : ⌜store.wasm.mem.read8 (address + offset) = byte ∧
      (address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_facts store ns obs nt
      (address + offset) byte $$ [$Hσ $Hpt] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, by simpa [Hread] using Step.load8U hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load8U offset))
      ⟨.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using (Step.load8U (α := α) hbound)
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
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
    iexact Hpt

/-- Offset-zero form of `twp_load8U`. -/
theorem twp_load8U_addr
    {params localValues values : List Value}
    {address : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
      WP (.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues, .i32 address :: values⟩,
      .load8U 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_load8U (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (params := params)
      (localValues := localValues) (values := values) (code := code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) byte (by simp))

/-- Total primitive rule for `i32.store8`. -/
theorem twp_store8
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store8 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some oldByte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some value.toUInt8) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hpt Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %HinBounds :
      ⌜(address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_inBounds store ns obs nt
      (address + offset) oldByte $$ [$Hσ $Hpt] with %HinBounds
    ipureintro
    exact HinBounds
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write8 (address + offset) value.toUInt8 } },
      [], ⟨rfl, _, rfl, Step.store8 hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store8 offset))
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write8
                (address + offset) value.toUInt8 } }⟩ :=
    Step.store8 hbound
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_store8 store ns obs nt
      (address + offset) oldByte value.toUInt8
      (by simpa [hnowrap] using HinBounds) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
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
    iexact Hpt

/-- Offset-zero form of `twp_store8`, avoiding an `addr + 0` unification
artifact in generated code. -/
theorem twp_store8_addr
    {params localValues values : List Value}
    {address value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some oldByte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value.toUInt8) -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store8 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_store8 (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (value := value)
      (params := params) (localValues := localValues) (values := values)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) oldByte (by simp))

theorem twp_store32_addr
    {params localValues values : List Value}
    {address value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    pointsTo_u32 0 address oldWord -∗
    (pointsTo_u32 0 address value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store32 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_store32 (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (value := value)
      (params := params) (localValues := localValues) (values := values)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) oldWord (by simp)
      (by simpa using h1) (by simpa using h2) (by simpa using h3))

theorem hdtwp_eq
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .eq :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.eq hresult)

theorem hdtwp_gtU
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs > rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .gtU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.gtU hresult)

theorem hdtwp_leU
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≤ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .leU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.leU hresult)

theorem hdtwp_shrU
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs >>> (rhs % 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .shrU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shrU)

theorem twp_ltS
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs.toInt32 < rhs.toInt32 then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ltS :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ltS hresult)

theorem twp_drop
    {params localValues values : List Value}
    {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, localValues, value :: values⟩,
        .drop :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.drop)

theorem hdtwp_select
    {params localValues values : List Value}
    {first second selected : Value} {condition : UInt32}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (h : selected = if condition ≠ 0 then first else second) :
    WP (.running ⟨⟨params, localValues, selected :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 condition :: second :: first :: values⟩,
        .select :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.select h)

/-- Total rule for `memory.size`. -/
theorem hdtwp_memorySize
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (R : IProp (WasmHeapGF α))
    (Htwp : ∀ pages : Nat,
        runtimeModuleOwn instanceId runtimeModule ∗ R -∗
        WP (.running ⟨⟨params, localValues,
            sizeValue runtimeModule.memIs64 pages :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule ∗ R -∗
    WP (.running ⟨⟨params, localValues, values⟩,
        .memorySize :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro ⟨Hruntime, HR⟩
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.currentModule = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      instanceId runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running ⟨⟨params, localValues,
        sizeValue store.runtime.currentModule.memIs64 store.wasm.mem.pages :: values⟩,
      code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction .memorySize, rfl, Step.memorySize⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.memorySize wasmStep
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
  · simp only [Hmodule]
    iapply Htwp
    iframe

/-- Total rule for `memory.grow`, exposing both the successful old-page
count and the `0xffffffff` failure result to the continuation. -/
theorem hdtwp_memoryGrow
    {params localValues values : List Value}
    {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (R : IProp (WasmHeapGF α))
    (Htwp : ∀ result : UInt32,
        runtimeModuleOwn instanceId runtimeModule ∗ R -∗
        WP (.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule ∗ R -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro ⟨Hruntime, HR⟩
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 (0xFFFFFFFF : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩,
        store, [], ⟨rfl, .instruction .memoryGrow, rfl,
          Step.memoryGrowFailure hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    obtain ⟨rfl, hconfig⟩ :=
      step_deterministic (Step.memoryGrowFailure hg) wasmStep
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
      iframe
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem := memory } }, [],
        ⟨rfl, .instruction .memoryGrow, rfl, by
          simpa only [Wasm.SmallStep.setMemory_eq] using
            Step.memoryGrowSuccess hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    have expectedStep : Step
        ⟨.running ⟨⟨params, localValues, .i32 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
            .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ := by
      simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg
    obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod stateInterp_memoryGrow store ns obs nt delta
      (store.wasm.memoryCap store.runtime.currentModule 0)
      memory previousPages hg $$ Hσ with Hσ
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
      iframe

/-- Total counterpart of `wp_callHost`.  In particular, under
`MaybeStuck` its trap continuation can be used to prove termination up to a
distinguished terminal host trap. -/
theorem hdtwp_callHost
    (runtimeModule : Module) (functionIndex : Nat) (imp : ImportDecl)
    (hostFn : HostFn α)
    (himports : functionIndex < runtimeModule.imports.length)
    (himp : runtimeModule.imports[functionIndex] = imp)
    (hostEnv : HostEnv α)
    (hfuncs : hostEnv.funcs[functionIndex]? = some hostFn)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (P : IProp (WasmHeapGF α))
    (QRet : List Value → IProp (WasmHeapGF α))
    (QTrap : IProp (WasmHeapGF α))
    (QThrow : IProp (WasmHeapGF α))
    (callerId : ModuleInstanceId)
    (hRetTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        ∀ results postWasm,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Return results postWasm →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        QRet results ∗ stateInterp (GF := WasmHeapGF α)
          { store with wasm := postWasm } ns obs nt)
    (hTrapTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        ∀ postWasm msg,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Trap postWasm msg →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        QTrap ∗ stateInterp (GF := WasmHeapGF α)
          { store with wasm := postWasm } ns obs nt)
    (hThrowTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        ∀ postWasm tag xs,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Throw postWasm tag xs →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        QThrow ∗ stateInterp (GF := WasmHeapGF α)
          { store with wasm := postWasm } ns obs nt) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
        arity, remainder, controls, calls⟩
    P -∗
    runtimeModuleOwn callerId runtimeModule -∗
    hostEnvOwn callerId.id hostEnv -∗
    (∀ preWasm results postWasm
          (_h : hostFn.invoke preWasm
            (values.take imp.params.length).reverse =
            .Return results postWasm),
        QRet results ∗ runtimeModuleOwn callerId runtimeModule -∗
        WP (Expr.running
            ⟨⟨params, localValues,
                results.take imp.results.length ++
                  values.drop imp.params.length⟩,
              code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) -∗
    (∀ preWasm postWasm msg
          (_h : hostFn.invoke preWasm
            (values.take imp.params.length).reverse =
            .Trap postWasm msg),
        QTrap -∗
        WP (Expr.trapped (.host msg) : Expr α) @ s; E [{ Φ }]) -∗
    (∀ preWasm postWasm tag xs
          (_h : hostFn.invoke preWasm
            (values.take imp.params.length).reverse =
            .Throw postWasm tag xs),
        QThrow -∗
        WP (Expr.running
            ⟨⟨params, localValues, values.drop imp.params.length⟩,
              [], arity, remainder,
              [{ kind := .throwing tag xs
                 paramArity := 0
                 resultArity := 0
                 body := []
                 continuation := []
                 belowStack := [] }] ++ controls,
              calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro HP Hruntime Henv HtwpRet HtwpTrap HtwpThrow
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.currentModule = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      callerId runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  have himports' : functionIndex <
      store.runtime.currentModule.imports.length := by
    simpa only [Hmodule] using himports
  have himp' : store.runtime.currentModule.imports[functionIndex] = imp := by
    simpa only [Hmodule] using himp
  ihave %Hhost : ⌜store.runtime.currentHost = hostEnv⌝ $$
      [Hσ HinstanceOwn Henv]
  · imod stateInterp_hostEnv store ns obs nt callerId.id hostEnv $$
        [$Hσ $HinstanceOwn $Henv] with %Hhost
    ipureintro
    exact Hhost
  have hhost' : store.runtime.currentHost.funcs[functionIndex]? =
      some hostFn := by
    rw [Hhost]
    exact hfuncs
  match h : hostFn.invoke store.wasm
      (values.take imp.params.length).reverse with
  | .Return results newWasm =>
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          results.take imp.results.length ++ values.drop imp.params.length⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := newWasm }, [],
        ⟨rfl, .host functionIndex, rfl,
          Step.callHostReturn himports' himp' hhost' h⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    obtain ⟨rfl, hconfig⟩ := step_deterministic
      (Step.callHostReturn (α := α) himports' himp' hhost' h) wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod hRetTransfer store ns obs nt Hmodule results newWasm h $$
      [$HP $Hσ] with ⟨HQ, Hσ⟩
    imod Hclose
    imodintro
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    · ispecialize HtwpRet $$ %(store.wasm) %results %newWasm %h
      iapply HtwpRet
      isplitl [HQ]
      · iexact HQ
      · isplitl [HruntimeElem]
        · iexact HruntimeElem
        · iexact HinstanceOwn
  | .Trap newWasm msg =>
    iclear HinstanceOwn HruntimeElem
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.trapped (.host msg), { store with wasm := newWasm }, [],
        ⟨rfl, .host functionIndex, rfl,
          Step.callHostTrap himports' himp' hhost' h⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    obtain ⟨rfl, hconfig⟩ := step_deterministic
      (Step.callHostTrap (α := α) himports' himp' hhost' h) wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod hTrapTransfer store ns obs nt Hmodule newWasm msg h $$
      [$HP $Hσ] with ⟨HQ, Hσ⟩
    imod Hclose
    imodintro
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    · ispecialize HtwpTrap $$ %(store.wasm) %newWasm %msg %h
      iapply HtwpTrap
      iexact HQ
  | .Throw newWasm tag xs =>
    iclear HinstanceOwn HruntimeElem
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          values.drop imp.params.length⟩,
        [], arity, remainder,
        [{ kind := .throwing tag xs
           paramArity := 0
           resultArity := 0
           body := []
           continuation := []
           belowStack := [] }] ++ controls,
        calls⟩, { store with wasm := newWasm }, [],
        ⟨rfl, .host functionIndex, rfl,
          Step.callHostThrow himports' himp' hhost' h⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    obtain ⟨rfl, hconfig⟩ := step_deterministic
      (Step.callHostThrow (α := α) himports' himp' hhost' h) wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod hThrowTransfer store ns obs nt Hmodule newWasm tag xs h $$
      [$HP $Hσ] with ⟨HQ, Hσ⟩
    imod Hclose
    imodintro
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    · ispecialize HtwpThrow $$ %(store.wasm) %newWasm %tag %xs %h
      iapply HtwpThrow
      iexact HQ

/-- Missing total counterpart of the unsigned greater-than-or-equal
instruction rule. -/
theorem hdtwp_geU
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≥ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .geU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.geU hresult)

/-- Offset-zero form of `twp_store64`. -/
theorem twp_store64_addr
    {params localValues values : List Value}
    {address : UInt32} {value : UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    pointsTo_u64 0 address oldWord -∗
    (pointsTo_u64 0 address value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
        .store64 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro Hword Hcont
  ihave Hword' : pointsTo_u64 0 (address + 0) oldWord $$ [Hword]
  · rw [UInt32.add_zero]
    iexact Hword
  iapply twp_store64 (α := α) (address := address) (offset := 0)
      (value := value) oldWord (by simp)
      (by simpa using h1) (by simpa using h2) (by simpa using h3)
      (by simpa using h4) (by simpa using h5) (by simpa using h6)
      (by simpa using h7) $$ Hword'
  iintro Hword
  iapply Hcont
  rw [UInt32.add_zero]
  iexact Hword

/-- Total-correctness byte-range rule for `memory.copy` on 32-bit memories.
The separating hypotheses also establish that source and destination do not
overlap. -/
theorem hdtwp_memoryCopy32
    {params localValues values : List Value}
    {destination source len : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldDstBytes srcBytes : List UInt8)
    (hlen_dst : oldDstBytes.length = len.toNat)
    (hlen_src : srcBytes.length = len.toNat)
    (hpos : 0 < len.toNat)
    (hnowrap_dst : destination.toNat + len.toNat < UInt32.size)
    (hnowrap_src : source.toNat + len.toNat < UInt32.size) :
    pointsToBytes 0 source srcBytes -∗
    pointsToBytes 0 destination oldDstBytes -∗
    (pointsToBytes 0 source srcBytes -∗
      pointsToBytes 0 destination srcBytes -∗
      WP (Expr.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues,
        .i32 len :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro Hsrc Hdst Hwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hpbsrc : ⌜∀ i b, srcBytes[i]? = some b →
      store.wasm.mem.read8 (source + UInt32.ofNat i) = b ∧
      (source + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hsrc]
  · imod stateInterp_pointsToBytes_agree store ns obs nt
        source srcBytes $$ [$Hσ $Hsrc] with %Hpbsrc
    ipureintro
    exact Hpbsrc
  ihave %Hpbdst : ⌜∀ i b, oldDstBytes[i]? = some b →
      store.wasm.mem.read8 (destination + UInt32.ofNat i) = b ∧
      (destination + UInt32.ofNat i).toNat <
        store.wasm.mem.pages * 65536⌝ $$ [Hσ Hdst]
  · imod stateInterp_pointsToBytes_agree store ns obs nt
        destination oldDstBytes $$ [$Hσ $Hdst] with %Hpbdst
    ipureintro
    exact Hpbdst
  have hbound_src : source.toNat + len.toNat ≤
      store.wasm.mem.pages * 65536 := by
    rw [← hlen_src]
    exact pointsToBytes_facts_bound Hpbsrc (by omega)
      (by rw [hlen_src]; simpa only [UInt32.size] using hnowrap_src)
  have hbound_dst : destination.toNat + len.toNat ≤
      store.wasm.mem.pages * 65536 := by
    rw [← hlen_dst]
    exact pointsToBytes_facts_bound Hpbdst (by omega)
      (by rw [hlen_dst]; simpa only [UInt32.size] using hnowrap_dst)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with mem :=
              store.wasm.mem.copy destination.toNat source.toNat len.toNat } },
      [], ⟨rfl, .instruction .memoryCopy, rfl,
        by simpa only [setMemory_eq] using
          (Step.memoryCopy32 hbound_dst hbound_src)⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues,
        .i32 len :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryCopy)
      ⟨.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem :=
                (store.wasm.mem.copy destination.toNat source.toNat
                  oldDstBytes.length) } }⟩ := by
    rw [hlen_dst]
    simpa only [setMemory_eq] using Step.memoryCopy32 hbound_dst hbound_src
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_copy_bytes store ns obs nt
      destination source oldDstBytes srcBytes
      (hlen_src.trans hlen_dst.symm)
      (by rw [hlen_dst]; exact hbound_dst)
      (by rw [hlen_dst]; exact hnowrap_dst)
      (by rw [hlen_src]; exact hbound_src)
      (by rw [hlen_src]; exact hnowrap_src)
      $$ [$Hσ $Hsrc $Hdst] with ⟨Hσ, Hsrc, Hdst⟩
  imod Hclose
  imodintro
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Hwp $$ Hsrc Hdst

end Wasm.SmallStep
