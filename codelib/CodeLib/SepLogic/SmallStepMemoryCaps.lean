import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Physical-cap-aware total memory growth

The cap token names a slot of the instantiated physical cap table. It is
not inferred from a module declaration. The failure continuation retains the
actual arithmetic reason for failure. A prior page snapshot remains only a
lower bound; this rule does not silently promote it to an exact measurement.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

variable [WasmSmallStepGS hlc α]
variable {Terminal : Type} [view : TerminalView α Terminal]

local instance (priority := high) capTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage

local instance (priority := high) capTerminalIrisGS :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      capTerminalLanguage (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }

variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-- Observe a primary page count within its owned physical cap. The returned
snapshot remains a lower bound at later program points; it is not a lease on
the measured count. -/
theorem twp_memorySize_capped
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {P : IProp (WasmHeapGF α)}
    (runtimeModule : Module) (instanceId : ModuleInstanceId) (cap : Nat)
    (Hwp : ∀ pages : Nat, pages ≤ cap →
        P -∗ runtimeModuleOwn instanceId runtimeModule -∗
        memoryCapOwn 0 cap -∗ memoryPagesOwn pages -∗
        WP (.running ⟨⟨params, localValues,
            sizeValue runtimeModule.memIs64 pages :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    P -∗ runtimeModuleOwn instanceId runtimeModule -∗ memoryCapOwn 0 cap -∗
    WP (.running ⟨⟨params, localValues, values⟩,
        .memorySize :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  wasm_twp_begin_with iintro HP Hruntime Hcap
  wasm_runtime_module_agree obs, instanceId, runtimeModule $$ [$Hσ $Hruntime]
  ihave %hvalid : ⌜store.wasm.memoryCaps[0]? = some cap ∧
      store.wasm.mem.pages ≤ cap⌝ $$ [Hσ Hcap]
  · iapply stateInterp_memoryCap_primary store ns obs nt cap
    iframe
  icombine HP Hruntime Hcap as Hclient
  icombine Hσ Hclient as Hinput
  imod (stateInterp_memoryPages_snapshot_frame store ns obs nt
      (P := iprop(P ∗ runtimeModuleOwn instanceId runtimeModule ∗ memoryCapOwn 0 cap))) $$
      Hinput with Hout
  icases Hout with ⟨⟨Hσ, #Hpages⟩, HP, Hruntime', Hcap⟩
  ihave Hcont := Hwp store.wasm.mem.pages hvalid.2
  ispecialize Hcont $$ HP Hruntime' Hcap Hpages
  wasm_twp_step Step.memorySize =>
    wasm_twp_frame
      simp only [Hmodule]
      iexact Hcont

/-- The ordinary primary-memory instruction uses physical cap slot zero.
Both continuations retain its token and the caller's complete frame. Failure
provides a strict cap violation at the actual growth step; success provides
the exact old/new-page equation and the cap bound. -/
theorem twp_memoryGrow_capped
    [WasmMemoryPagesLegacy α]
    {params localValues values : List Value}
    {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {P : IProp (WasmHeapGF α)}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (cap measuredPages : Nat)
    (Hfailure : ∀ pages : Nat,
        measuredPages ≤ pages → pages ≤ cap → cap < pages + delta.toNat →
        P -∗ runtimeModuleOwn instanceId runtimeModule -∗
        memoryCapOwn 0 cap -∗ memoryPagesOwn measuredPages -∗
        WP (.running ⟨⟨params, localValues,
            .i32 (0xFFFFFFFF : UInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }])
    (Hsuccess : ∀ oldPages previousPages newPages : Nat,
        previousPages = oldPages ∧
          newPages = previousPages + delta.toNat ∧ newPages ≤ cap →
        measuredPages ≤ oldPages →
        P -∗ runtimeModuleOwn instanceId runtimeModule -∗
        memoryCapOwn 0 cap -∗ memoryPagesOwn measuredPages -∗
        memoryPagesOwn newPages -∗
        WP (.running ⟨⟨params, localValues,
            .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    P -∗ runtimeModuleOwn instanceId runtimeModule -∗
    memoryCapOwn 0 cap -∗ memoryPagesOwn measuredPages -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  wasm_twp_begin_with iintro HP Hruntime Hcap Hmeasured
  ihave %hcap : ⌜store.wasm.memoryCaps[0]? = some cap ∧
      store.wasm.mem.pages ≤ cap⌝ $$ [Hσ Hcap]
  · iapply stateInterp_memoryCap_primary store ns obs nt cap
    iframe
  have hphysical : store.wasm.memoryCap store.runtime.currentModule 0 = cap := by
    simp [Store.memoryCap, hcap.1]
  ihave %hle : ⌜measuredPages ≤ store.wasm.mem.pages⌝ $$ [Hσ Hmeasured]
  · imod stateInterp_memoryPages_agree store ns obs nt measuredPages $$
      [$Hσ $Hmeasured] with ⟨_, _, %hle⟩
    ipureexact hle
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    have hfailure : cap < store.wasm.mem.pages + delta.toNat := by
      have h := hg
      simp only [Mem.grow, hphysical] at h
      split at h
      · contradiction
      · omega
    ihave Hcont := Hfailure store.wasm.mem.pages hle hcap.2 hfailure
    ispecialize Hcont $$ HP Hruntime Hcap Hmeasured
    wasm_twp_step Step.memoryGrowFailure hg =>
      wasm_twp_frame
        iexact Hcont
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    have hfacts : previousPages = store.wasm.mem.pages ∧
        memory.pages = previousPages + delta.toNat ∧ memory.pages ≤ cap := by
      have h := hg
      simp only [Mem.grow, hphysical] at h
      split at h
      · rename_i hbound
        have hinj := Prod.mk.inj (Option.some.inj h)
        have hold : previousPages = store.wasm.mem.pages := hinj.2.symm
        have hnew : memory.pages = store.wasm.mem.pages + delta.toNat :=
          (congrArg (fun result : Mem => result.pages) hinj.1).symm
        exact ⟨hold, hnew.trans (by rw [hold]), hnew ▸ hbound⟩
      · contradiction
    ihave Hcont := Hsuccess store.wasm.mem.pages previousPages memory.pages hfacts hle
    ispecialize Hcont $$ HP Hruntime Hcap Hmeasured
    wasm_twp_step (by
        simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg) =>
      icombine Hσ Hcont as Hinput
      imod stateInterp_memoryGrow_tracked_frame store ns obs nt delta
          (store.wasm.memoryCap store.runtime.currentModule 0)
          memory previousPages hg rfl $$ Hinput with Hout
      icases Hout with ⟨⟨Hσ, HnewPages, %_⟩, Hcont⟩
      ispecialize Hcont $$ HnewPages
      wasm_twp_frame
        iexact Hcont

/-- Exact primary-memory size is read from a retained linear authority token.
The same token remains available to determine a later growth outcome. -/
theorem twp_memorySize_exact
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {P : IProp (WasmHeapGF α)}
    (runtimeModule : Module) (instanceId : ModuleInstanceId) (pages : Nat)
    (Hwp : P -∗ runtimeModuleOwn instanceId runtimeModule -∗
        memoryPagesHalf pages -∗
        WP (.running ⟨⟨params, localValues,
            sizeValue runtimeModule.memIs64 pages :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    P -∗ runtimeModuleOwn instanceId runtimeModule -∗ memoryPagesHalf pages -∗
    WP (.running ⟨⟨params, localValues, values⟩,
        .memorySize :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  wasm_twp_begin_with iintro HP Hruntime Hpages
  wasm_runtime_module_agree obs, instanceId, runtimeModule $$ [$Hσ $Hruntime]
  ihave %hpages : ⌜store.wasm.mem.pages = pages⌝ $$ [Hσ Hpages]
  · iapply stateInterp_memoryPages_half_agree store ns obs nt pages
    iframe
  wasm_twp_step Step.memorySize =>
    wasm_twp_frame
      simp only [Hmodule, hpages]
      iapply Hwp $$ HP Hruntime Hpages

/-- Exact ownership and the actual cap determine successful primary growth.
The instruction returns the owned old count and a linear token for the new
count. No failure continuation or guessed physical success equation is needed. -/
theorem twp_memoryGrow_exact
    {params localValues values : List Value} {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {P : IProp (WasmHeapGF α)}
    (runtimeModule : Module) (instanceId : ModuleInstanceId) (cap pages : Nat)
    (hmode : (inferInstance : WasmMemoryPagesGS α).stateFrac = (1 : Qp).half)
    (hfit : pages + delta.toNat ≤ cap)
    (Hwp : P -∗ runtimeModuleOwn instanceId runtimeModule -∗
        memoryCapOwn 0 cap -∗ memoryPagesHalf (pages + delta.toNat) -∗
        WP (.running ⟨⟨params, localValues, .i32 pages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    P -∗ runtimeModuleOwn instanceId runtimeModule -∗
    memoryCapOwn 0 cap -∗ memoryPagesHalf pages -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  wasm_twp_begin_with iintro HP Hruntime Hcap Hpages
  ihave %hcap : ⌜store.wasm.memoryCaps[0]? = some cap ∧
      store.wasm.mem.pages ≤ cap⌝ $$ [Hσ Hcap]
  · iapply stateInterp_memoryCap_primary store ns obs nt cap
    iframe
  have hphysical : store.wasm.memoryCap store.runtime.currentModule 0 = cap := by
    simp [Store.memoryCap, hcap.1]
  ihave %hpages : ⌜store.wasm.mem.pages = pages⌝ $$ [Hσ Hpages]
  · iapply stateInterp_memoryPages_half_agree store ns obs nt pages
    iframe
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    simp only [Mem.grow, hphysical, hpages, if_pos hfit] at hg
    contradiction
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    have hfacts : previousPages = pages ∧ memory.pages = pages + delta.toNat := by
      have h := hg
      simp only [Mem.grow, hphysical, hpages, if_pos hfit] at h
      have hinj := Prod.mk.inj (Option.some.inj h)
      exact ⟨hinj.2.symm, (congrArg (fun m : Mem => m.pages) hinj.1).symm⟩
    ihave Hactual : memoryPagesHalf store.wasm.mem.pages $$ [Hpages]
    · irw_exact [hpages] with Hpages
    wasm_twp_step (by
        simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg) =>
      imod stateInterp_memoryGrow_exact store ns obs nt delta
          (store.wasm.memoryCap store.runtime.currentModule 0)
          memory previousPages hmode hg rfl $$ [$Hσ $Hactual] with
        ⟨Hσ, HnewPages, _Hsnapshot⟩
      isimp only [hfacts.2] at HnewPages
      wasm_twp_frame
        simp only [hfacts.1]
        iapply Hwp $$ HP Hruntime Hcap HnewPages

/-- A request strictly above the actual cap returns the failure sentinel and
preserves the exact token. This failure rule does not update page authority. -/
theorem twp_memoryGrow_exact_failure
    {params localValues values : List Value} {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {P : IProp (WasmHeapGF α)}
    (runtimeModule : Module) (instanceId : ModuleInstanceId) (cap pages : Nat)
    (hfail : cap < pages + delta.toNat)
    (Hwp : P -∗ runtimeModuleOwn instanceId runtimeModule -∗
        memoryCapOwn 0 cap -∗ memoryPagesHalf pages -∗
        WP (.running ⟨⟨params, localValues, .i32 (0xFFFFFFFF : UInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    P -∗ runtimeModuleOwn instanceId runtimeModule -∗
    memoryCapOwn 0 cap -∗ memoryPagesHalf pages -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  wasm_twp_begin_with iintro HP Hruntime Hcap Hpages
  ihave %hcap : ⌜store.wasm.memoryCaps[0]? = some cap ∧
      store.wasm.mem.pages ≤ cap⌝ $$ [Hσ Hcap]
  · iapply stateInterp_memoryCap_primary store ns obs nt cap
    iframe
  have hphysical : store.wasm.memoryCap store.runtime.currentModule 0 = cap := by
    simp [Store.memoryCap, hcap.1]
  ihave %hpages : ⌜store.wasm.mem.pages = pages⌝ $$ [Hσ Hpages]
  · iapply stateInterp_memoryPages_half_agree store ns obs nt pages
    iframe
  have hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) = none := by
    simp only [Mem.grow, hphysical, hpages, if_neg (Nat.not_le_of_lt hfail)]
  wasm_twp_step Step.memoryGrowFailure hg =>
    wasm_twp_frame
      iapply Hwp $$ HP Hruntime Hcap Hpages

/-- A successful growth under the Wasm32 hard cap cannot return the failure
sentinel, even when the requested increment is zero. -/
theorem capped_growth_previous_ne_failure
    (previousPages newPages cap : Nat) (delta : UInt32)
    (hnew : newPages = previousPages + delta.toNat)
    (hcap : newPages ≤ cap) (hhard : cap ≤ Module.memoryHardCap) :
    previousPages.toUInt32 ≠ (0xFFFFFFFF : UInt32) := by
  have hprevious : previousPages ≤ 65536 := by
    have : Module.memoryHardCap = 65536 := rfl
    omega
  intro heq
  have hnat := congrArg UInt32.toNat heq
  rw [show previousPages.toUInt32.toNat = previousPages from
    UInt32.toNat_ofNat_of_lt' (by change previousPages < 4294967296; omega)] at hnat
  change previousPages = 4294967295 at hnat
  omega

end Wasm.SmallStep
