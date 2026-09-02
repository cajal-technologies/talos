import CodeLib

namespace Project.HexEncodeStdio.TotalHost

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private theorem hostStateOwn_agree_update {α : Type} [gs : WasmHostStateGS α]
    (actual expected newHost : α) :
    hostStateAuth actual ∗ hostStateOwn expected ==∗
      ⌜actual = expected⌝ ∗ hostStateAuth newHost ∗ hostStateOwn newHost := by
  unfold hostStateAuth hostStateOwn
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag as Hboth gives %Hvalid
  have heq : actual = expected :=
    congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO α) Hvalid)
  subst expected
  icases iOwn_op $$ Hboth with ⟨Hauth, Hfrag⟩
  imod iOwn_update_op (E := gs.hostStateElem)
      (ExclAuth.update (A := DiscreteO α)
      (a := (⟨actual⟩ : DiscreteO α))
      (b := ⟨actual⟩) (a' := ⟨newHost⟩)) $$ [Hauth Hfrag] with Hboth
  · iframe
  icases iOwn_op $$ Hboth with ⟨Hauth, Hfrag⟩
  imodintro
  isplit
  · ipureintro; rfl
  · isplitl [Hauth]
    · iexact Hauth
    · iexact Hfrag

/-- Simultaneously learn that the client host fragment describes the physical
host and update both sides.  The agreement fact is returned alongside the
updated ownership, so callers can calculate the concrete host result without
discarding the exclusive fragment. -/
theorem stateInterp_host_set_expected {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (expected newHost : α) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      hostStateOwn expected ==∗
      ⌜store.wasm.host = expected⌝ ∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with host := newHost } }
        steps observations threads ∗
      hostStateOwn newHost := by
  iintro ⟨Hstate, HP⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      %runtimeModuleσ, %hostEnvσ, Hheap, Hglobals, Hsegments, Htables,
      HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth,
      %Hfacts, Hexc⟩
  imod hostStateOwn_agree_update store.wasm.host expected newHost
      $$ [$Hstate_auth $HP] with ⟨%heq, Hstate_auth, HP⟩
  subst expected
  imodintro
  isplit
  · ipureintro; rfl
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth Hstate_auth Hexc]
  · iapply (stateInterp_eq
      { store with wasm := { store.wasm with host := newHost } }
      steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ
    iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth Hstate_auth Hexc
    ipureintro
    exact Hfacts
  · iexact HP

/-- Total lifting for a host call whose contract proves that this invocation
returns.  This is the return-only specialization needed for in-bounds stdio
calls; unlike the partial `wp_callHost`, it cannot admit a trap branch. -/
theorem twp_callHost_return {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
    (callerId : ModuleInstanceId)
    (hReturns : ∀ (store : MachineStore α),
      store.runtime.currentModule = runtimeModule →
      store.runtime.currentHost = hostEnv →
      ∃ results postWasm,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Return results postWasm)
    (hRetTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        ∀ results postWasm,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Return results postWasm →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        QRet results ∗
        stateInterp (GF := WasmHeapGF α)
          { store with wasm := postWasm } ns obs nt) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
        arity, remainder, controls, calls⟩
    P -∗
    runtimeModuleOwn callerId runtimeModule -∗
    hostEnvOwn callerId.id hostEnv -∗
    (∀ preWasm results postWasm
        (_h : hostFn.invoke preWasm (values.take imp.params.length).reverse =
          .Return results postWasm),
      QRet results ∗ runtimeModuleOwn callerId runtimeModule -∗
      WP (Expr.running
          ⟨⟨params, localValues,
              results.take imp.results.length ++ values.drop imp.params.length⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }]) -∗
    WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro HP Hruntime Henv HwpRet
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.currentModule = runtimeModule⌝ $$ [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      callerId runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  have himports' : functionIndex < store.runtime.currentModule.imports.length := by
    simpa only [Hmodule] using himports
  have himp' : store.runtime.currentModule.imports[functionIndex] = imp := by
    simpa only [Hmodule] using himp
  ihave %Hhost : ⌜store.runtime.currentHost = hostEnv⌝ $$ [Hσ HinstanceOwn Henv]
  · imod stateInterp_hostEnv store ns obs nt callerId.id hostEnv
        $$ [$Hσ $HinstanceOwn $Henv] with %Hhost
    ipureintro
    exact Hhost
  have hhost' : store.runtime.currentHost.funcs[functionIndex]? = some hostFn := by
    rw [Hhost]
    exact hfuncs
  obtain ⟨results, newWasm, hinvoke⟩ := hReturns store Hmodule Hhost
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
        Step.callHostReturn himports' himp' hhost' hinvoke⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ := step_deterministic
    (Step.callHostReturn (α := α) himports' himp' hhost' hinvoke) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod hRetTransfer store ns obs nt Hmodule results newWasm hinvoke
    $$ [$HP $Hσ] with ⟨HQ, Hσ⟩
  imod Hclose
  imodintro
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; rfl
  isplitl [Hσ]
  · iexact Hσ
  · ispecialize HwpRet $$ %(store.wasm) %results %newWasm %hinvoke
    iapply HwpRet
    isplitl [HQ]
    · iexact HQ
    · isplitl [HruntimeElem]
      · iexact HruntimeElem
      · iexact HinstanceOwn

/-- Total host-call lifting when the fact that the host returns itself depends
on the resources in `P` (most importantly, ownership proving that an I/O
buffer is in bounds).  Combining outcome discovery with the ghost transfer
avoids assuming that an arbitrary physical store is well formed. -/
theorem twp_callHost_return_fupd {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
    (callerId : ModuleInstanceId)
    (hTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        store.runtime.currentHost = hostEnv →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        ∃ results postWasm,
          ⌜hostFn.invoke store.wasm
              (values.take imp.params.length).reverse =
            .Return results postWasm⌝ ∗
          QRet results ∗
          stateInterp (GF := WasmHeapGF α)
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
      QRet results ∗ runtimeModuleOwn callerId runtimeModule ∗
        hostEnvOwn callerId.id hostEnv -∗
      WP (Expr.running
          ⟨⟨params, localValues,
              results.take imp.results.length ++ values.drop imp.params.length⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }]) -∗
    WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro HP Hruntime Henv HwpRet
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.currentModule = runtimeModule⌝ $$ [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      callerId runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  have himports' : functionIndex < store.runtime.currentModule.imports.length := by
    simpa only [Hmodule] using himports
  have himp' : store.runtime.currentModule.imports[functionIndex] = imp := by
    simpa only [Hmodule] using himp
  ihave %Hhost : ⌜store.runtime.currentHost = hostEnv⌝ $$ [Hσ HinstanceOwn Henv]
  · imod stateInterp_hostEnv store ns obs nt callerId.id hostEnv
        $$ [$Hσ $HinstanceOwn $Henv] with %Hhost
    ipureintro
    exact Hhost
  have hhost' : store.runtime.currentHost.funcs[functionIndex]? = some hostFn := by
    rw [Hhost]
    exact hfuncs
  imod hTransfer store ns obs nt Hmodule Hhost $$ [$HP $Hσ] with
    ⟨%results, %newWasm, %hinvoke, HQ, Hσ⟩
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
        Step.callHostReturn himports' himp' hhost' hinvoke⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ := step_deterministic
    (Step.callHostReturn (α := α) himports' himp' hhost' hinvoke) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; rfl
  isplitl [Hσ]
  · iexact Hσ
  · ispecialize HwpRet $$ %(store.wasm) %results %newWasm %hinvoke
    iapply HwpRet
    isplitl [HQ]
    · iexact HQ
    · isplitl [HruntimeElem HinstanceOwn]
      · isplitl [HruntimeElem]
        · iexact HruntimeElem
        · iexact HinstanceOwn
      · iexact Henv

end Project.HexEncodeStdio.TotalHost
