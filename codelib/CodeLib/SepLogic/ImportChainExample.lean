import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

@[simp] private theorem RuntimeEnv.currentModule_mk2 {α : Type} (inst1 inst2 : ModuleInstance α) :
    ({ instances := #[inst1, inst2], entry := ⟨0⟩ } : RuntimeEnv α).currentModule = inst1.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

@[simp] private theorem RuntimeEnv.currentHost_mk2 {α : Type} (inst1 inst2 : ModuleInstance α) :
    ({ instances := #[inst1, inst2], entry := ⟨0⟩ } : RuntimeEnv α).currentHost = inst1.host := by
  simp [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]

-- host fn: appends i32 argument to the host list
def logHost : HostFn (List UInt32) where
  params  := [.i32]
  results := []
  invoke  := fun wasm args =>
    match args with
    | [.i32 v] => .Return [] { wasm with host := wasm.host ++ [v] }
    | _ => .Trap wasm "bad args"

def chainHostEnv : HostEnv (List UInt32) :=
  { funcs := [logHost] }

private abbrev logImp : ImportDecl :=
  { module := "chain", name := "log", params := [.i32], results := [] }

private abbrev nopImp : ImportDecl :=
  { module := "chain", name := "nop", params := [], results := [] }

-- module A: calls nop (cross-instance) then logs v twice; index 0 = host log, index 1 = nop
def mainFn : Function where
  params  := [.i32]
  locals  := []
  results := []
  body    := [.call 1, .localGet 0, .call 0, .localGet 0, .call 0, .ret]

def chainModuleA : Module where
  imports := [logImp, nopImp]
  funcs   := [mainFn]

-- module B: pure no-op, no imports, no host
def nopFn : Function where
  params  := []
  locals  := []
  results := []
  body    := [.ret]

def chainModuleB : Module where
  imports := []
  funcs   := [nopFn]

-- instance 0 (entry): has logHost, resolvedImports[1] dispatches to chainInstB's nopFn
def chainInstA : ModuleInstance (List UInt32) where
  module          := chainModuleA
  host            := chainHostEnv
  resolvedImports := #[.wasm ⟨0⟩ 0, .wasm ⟨1⟩ 0]

-- instance 1: empty host, just nopFn
def chainInstB : ModuleInstance (List UInt32) where
  module          := chainModuleB
  host            := { funcs := [] }
  resolvedImports := #[]

@[simp] private theorem chainInstA_module : chainInstA.module = chainModuleA := rfl
@[simp] private theorem chainInstA_host : chainInstA.host = chainHostEnv := rfl

def importChainConfig (v : UInt32) (initial : List UInt32) : Config (List UInt32) :=
  { expr := .running
      { locals          := { params := [.i32 v], locals := [], values := [] }
        code            := [.call 1, .localGet 0, .call 0, .localGet 0, .call 0, .ret]
        resultArity     := 0
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime :=
          { instances := #[chainInstA, chainInstB]
            entry     := ⟨0⟩ }
        wasm :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := initial } } }

-- transfer: hostStateOwn n ∗ stateInterp → hostStateOwn (n ++ [v]) ∗ stateInterp'
private theorem logTransfer (v : UInt32) (n : List UInt32)
    [WasmSmallStepGS .hasLC (List UInt32)]
    (store : MachineStore (List UInt32)) (ns : Nat) (obs : List StepKind) (nt : Nat)
    (_ : store.runtime.currentModule = chainModuleA)
    (results : List Value) (postWasm : Store (List UInt32))
    (h : logHost.invoke store.wasm [.i32 v] = .Return results postWasm) :
    hostStateOwn n ∗
      stateInterp (GF := WasmHeapGF (List UInt32)) store ns obs nt ==∗
      hostStateOwn (n ++ [v]) ∗
      stateInterp (GF := WasmHeapGF (List UInt32))
        { store with wasm := postWasm } ns obs nt := by
  simp [logHost] at h
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2
  iintro ⟨HP, Hσ⟩
  icases (stateInterp_eq store ns obs nt).mp $$ Hσ with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, Henv, Hauth, %Hfacts⟩
  ihave %heq : ⌜store.wasm.host = n⌝ $$ [Hauth HP]
  · iapply (hostStateOwn_agree store.wasm.host n); iframe Hauth HP
  rw [heq]
  imod hostStateOwn_update n (n ++ [v]) $$ [$Hauth $HP] with ⟨Hauth', HP'⟩
  imodintro
  isplitl [HP']
  · iexact HP'
  · iapply (stateInterp_eq
        { store with wasm := { store.wasm with host := n ++ [v] } }
        ns obs nt).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ
    iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep
      HruntimeInstances HinstanceAuth Henv Hauth'
    ipureintro
    exact Hfacts

theorem importChain_partiallyMeets (v : UInt32) (initial : List UInt32) :
    PartiallyMeets (importChainConfig v initial) (fun values _ => values = []) := by
  apply wasm_smallStep_instance_host_state_partiallyMeets (α := List UInt32)
  · simp only [importChainConfig]; decide
  · intro gs
    simp only [importChainConfig, RuntimeEnv.currentModule_mk2, RuntimeEnv.currentHost_mk2,
               chainInstA_module, chainInstA_host]
    iintro ⟨Hruntime, Henv, Hhost, HruntimeInstances⟩
    simp only [runtimeModuleOwn]
    icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
    iintuitionistic HruntimeElem
    iintuitionistic Henv
    -- call 1: cross-instance to nopFn in chainInstB (instance 1)
    iapply wp_callCrossInstance ⟨0⟩ chainInstA ⟨1⟩ chainInstB #[chainInstA, chainInstB]
        1 nopImp 0 nopFn
        rfl rfl (by decide) rfl (Nat.le.refl) rfl rfl
        $$ [HinstanceOwn] HruntimeInstances
    · simp only [runtimeModuleOwn, chainInstA_module]
      inext
      isplitl []
      · iexact HruntimeElem
      · iexact HinstanceOwn
    · inext
      iintro ⟨HinstanceOwn', HruntimeInstances'⟩
      simp only [nopFn, Function.toLocals, List.map_nil]
      -- inside nopFn: body = [.ret], return immediately
      iapply wp_returnFromCallCrossInstance ⟨1⟩ chainInstB chainInstA #[chainInstA, chainInstB]
          (by decide) rfl rfl
          $$ [HinstanceOwn'] HruntimeInstances'
      · inext; iexact HinstanceOwn'
      · inext
        iintro HinstanceCaller
        simp only [List.length_nil, List.take_zero, List.drop_zero, List.nil_append]
        -- back in mainFn: [localGet 0, call 0, localGet 0, call 0, ret]
        iapply wp_localGet rfl
        inext
        -- first logHost call: rebuild runtimeModuleOwn from HruntimeElem + HinstanceCaller
        ihave Hruntime1 : runtimeModuleOwn ⟨0⟩ chainModuleA $$ [HinstanceCaller]
        · simp only [runtimeModuleOwn]
          isplitl []
          · iexact HruntimeElem
          · iexact HinstanceCaller
        iapply wp_callHost chainModuleA 0 logImp logHost
            (by decide) rfl chainHostEnv rfl
            (iprop(hostStateOwn initial))
            (fun _ => iprop(hostStateOwn (initial ++ [v])))
            iprop(False) iprop(False)
            ⟨0⟩
            (logTransfer v initial)
            (fun _ _ _ _ _ _ _ h => by simp [logHost] at h)
            (fun _ _ _ _ _ _ _ _ h => by simp [logHost] at h)
            (s := Stuckness.NotStuck) (E := ⊤)
            (params := [.i32 v]) (localValues := []) (values := [.i32 v])
            (code := [.localGet 0, .call 0, .ret])
            (arity := 0) (remainder := []) (controls := []) (calls := [])
            $$ [$Hhost] Hruntime1 Henv
        · inext
          iintro %_ %results1 %_ %h1 ⟨Hhost1, Hruntime1'⟩
          simp [logHost] at h1; obtain ⟨h1r, _⟩ := h1; subst h1r
          simp only [List.take_nil, List.length_cons, List.length_nil, Nat.zero_add,
                     List.drop_succ_cons, List.drop_zero, List.nil_append]
          -- second logHost call
          iapply wp_localGet rfl
          inext
          iapply wp_callHost chainModuleA 0 logImp logHost
              (by decide) rfl chainHostEnv rfl
              (iprop(hostStateOwn (initial ++ [v])))
              (fun _ => iprop(hostStateOwn (initial ++ [v] ++ [v])))
              iprop(False) iprop(False)
              ⟨0⟩
              (logTransfer v (initial ++ [v]))
              (fun _ _ _ _ _ _ _ h => by simp [logHost] at h)
              (fun _ _ _ _ _ _ _ _ h => by simp [logHost] at h)
              (s := Stuckness.NotStuck) (E := ⊤)
              (params := [.i32 v]) (localValues := []) (values := [.i32 v])
              (code := [.ret])
              (arity := 0) (remainder := []) (controls := []) (calls := [])
              $$ [$Hhost1] Hruntime1' Henv
          · inext
            iintro %_ %results2 %_ %h2 ⟨Hhost2, _⟩
            simp [logHost] at h2; obtain ⟨h2r, _⟩ := h2; subst h2r
            simp only [List.take_nil, List.length_cons, List.length_nil, Nat.zero_add,
                       List.drop_succ_cons, List.drop_zero, List.nil_append]
            iclear Hhost2
            iapply wp_returnFromFunction
            inext
            simp only [List.append_nil]
            iapply wp_value'
            ipureintro
            rfl
          · inext; iintro %_ %_ %_ %h _; simp [logHost] at h
          · inext; iintro %_ %_ %_ %_ %h _; simp [logHost] at h
        · inext; iintro %_ %_ %_ %h _; simp [logHost] at h
        · inext; iintro %_ %_ %_ %_ %h _; simp [logHost] at h

theorem importChain_terminates :
    TerminatesWith (importChainConfig 42 []) (fun _ _ => True) :=
  runSteps_checked_terminates (fuel := 200)
    (fun _ _ => true)
    (by native_decide)
    (fun _ _ _ => trivial)

end Wasm.SmallStep
