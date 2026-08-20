import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

-- host fn: increments wasm.host by 1, returns no values
def incrementHost : HostFn Nat where
  params  := []
  results := []
  invoke  := fun wasm _ => .Return [] { wasm with host := wasm.host + 1 }

-- host fn: returns wasm.host as i32
def readCounterHost : HostFn Nat where
  params  := []
  results := [.i32]
  invoke  := fun wasm _ => .Return [.i32 (UInt32.ofNat wasm.host)] wasm

def counterHostEnv : HostEnv Nat :=
  { funcs := [incrementHost, readCounterHost] }

private abbrev incrImp : ImportDecl :=
  { module := "counter", name := "incr", params := [], results := [] }

private abbrev readImp : ImportDecl :=
  { module := "counter", name := "read", params := [], results := [.i32] }

-- calls incr 3 times then read, returns the count
def counterFn : Function where
  params  := []
  locals  := []
  results := [.i32]
  body    := [.call 0, .call 0, .call 0, .call 1, .ret]

def counterModule : Module where
  imports := [incrImp, readImp]
  funcs   := [counterFn]

def counterRuntime : RuntimeEnv Nat :=
  { instances := #[{ module := counterModule, host := counterHostEnv }]
    entry     := ⟨0⟩ }

def counterConfig (initial : Nat) : Config Nat :=
  { expr  := .running
      { locals          := { params := [], locals := [], values := [] }
        code            := [.call 0, .call 0, .call 0, .call 1, .ret]
        resultArity     := 1
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime := counterRuntime
        wasm    :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := initial } } }

-- ghost update: hostStateOwn n ∗ stateInterp → hostStateOwn (n+1) ∗ stateInterp'
-- rw [heq] unifies ExclAuth auth and frag so hostStateOwn_update can fire
private theorem incrTransfer (n : Nat) [WasmSmallStepGS .hasLC Nat]
    (store : MachineStore Nat) (ns : Nat) (obs : List StepKind) (nt : Nat)
    (_ : store.runtime.currentModule = counterModule)
    (results : List Value) (postWasm : Store Nat)
    (h : incrementHost.invoke store.wasm [] = .Return results postWasm) :
    hostStateOwn n ∗ stateInterp (GF := WasmHeapGF Nat) store ns obs nt ==∗
      hostStateOwn (n + 1) ∗
      stateInterp (GF := WasmHeapGF Nat) { store with wasm := postWasm } ns obs nt := by
  simp [incrementHost] at h
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2
  iintro ⟨HP, Hσ⟩
  icases (stateInterp_eq store ns obs nt).mp $$ Hσ with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, Henv, Hauth, %Hfacts, Hexc⟩
  -- auth and frag: derive store.wasm.host = n; specialize_dup_context retains Hauth HP
  ihave %heq : ⌜store.wasm.host = n⌝ $$ [Hauth HP]
  · iapply (hostStateOwn_agree store.wasm.host n); iframe Hauth HP
  -- rw [heq] replaces store.wasm.host with n throughout the iris goal,
  -- making auth and frag both carry n so hostStateOwn_update applies
  rw [heq]
  imod hostStateOwn_update n (n + 1) $$ [$Hauth $HP] with ⟨Hauth', HP'⟩
  imodintro
  -- conclusion: hostStateOwn (n+1) ∗ stateInterp; hostStateOwn is LEFT
  isplitl [HP']
  · iexact HP'
  · iapply (stateInterp_eq
        { store with wasm := { store.wasm with host := n + 1 } }
        ns obs nt).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ
    iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep
      HruntimeInstances HinstanceAuth Henv Hauth' Hexc
    ipureintro
    exact Hfacts

-- read: observe host state = initial+3, return pure fact about results
private theorem readTransfer (initial : Nat) [WasmSmallStepGS .hasLC Nat]
    (store : MachineStore Nat) (ns : Nat) (obs : List StepKind) (nt : Nat)
    (_ : store.runtime.currentModule = counterModule)
    (results : List Value) (postWasm : Store Nat)
    (h : readCounterHost.invoke store.wasm [] = .Return results postWasm) :
    hostStateOwn (initial + 3) ∗
      stateInterp (GF := WasmHeapGF Nat) store ns obs nt ==∗
      ⌜results = [.i32 (UInt32.ofNat (initial + 3))]⌝ ∗
      stateInterp (GF := WasmHeapGF Nat) { store with wasm := postWasm } ns obs nt := by
  simp [readCounterHost] at h
  obtain ⟨h1, h2⟩ := h; subst h2
  iintro ⟨HP, Hσ⟩
  -- decompose stateInterp to get Hauth; read-only so reconstruct at the end
  icases (stateInterp_eq store ns obs nt).mp $$ Hσ with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, Henv, Hauth, %Hfacts, Hexc⟩
  -- derive store.wasm.host = initial + 3; retains Hauth HP (pure conclusion)
  ihave %heq : ⌜store.wasm.host = initial + 3⌝ $$ [Hauth HP]
  · iapply (hostStateOwn_agree store.wasm.host (initial + 3)); iframe Hauth HP
  imodintro
  isplitl []
  -- h1 : [.i32 (UInt32.ofNat store.wasm.host)] = results (reversed by simp)
  · ipureintro; rw [← h1, heq]
  · -- reconstruct stateInterp store (= { store with wasm := store.wasm } definitionally)
    iapply (stateInterp_eq store ns obs nt).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ
    iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep
      HruntimeInstances HinstanceAuth Henv Hauth Hexc
    ipureintro; exact Hfacts

theorem counter_partiallyMeets (initial : Nat) (_hbound : initial + 3 < 2 ^ 32) :
    PartiallyMeets (counterConfig initial)
      (fun values _ => values = [.i32 (UInt32.ofNat (initial + 3))]) := by
  apply wasm_smallStep_instance_host_state_partiallyMeets (α := Nat)
  · simp only [counterConfig, counterRuntime]; decide
  · intro gs
    simp only [counterConfig, counterRuntime,
      RuntimeEnv.currentModule_mk1, RuntimeEnv.currentHost_mk1]
    iintro ⟨Hruntime, Henv, Hhost, _HruntimeInstances⟩
    iintuitionistic Henv
    -- first increment: initial → initial+1
    iapply wp_callHost counterModule 0 incrImp incrementHost
        (by decide) rfl counterHostEnv rfl
        (iprop(hostStateOwn initial))
        (fun _ => iprop(hostStateOwn (initial + 1)))
        iprop(False) iprop(False)
        ⟨0⟩
        (incrTransfer initial)
        (fun _ _ _ _ _ _ _ h => by simp [incrementHost] at h)
        (fun _ _ _ _ _ _ _ _ h => by simp [incrementHost] at h)
        (s := Stuckness.NotStuck) (E := ⊤)
        (params := []) (localValues := []) (values := [])
        (code := [.call 0, .call 0, .call 1, .ret])
        (arity := 1) (remainder := []) (controls := []) (calls := [])
        $$ [$Hhost] Hruntime Henv
    · inext
      iintro %_ %results1 %_ %h1 ⟨Hhost1, Hruntime1⟩
      simp [incrementHost] at h1; obtain ⟨h1r, _⟩ := h1; subst h1r
      simp only [List.length_nil, List.take_zero, List.drop_zero, List.nil_append]
      -- second increment: initial+1 → initial+2
      iapply wp_callHost counterModule 0 incrImp incrementHost
          (by decide) rfl counterHostEnv rfl
          (iprop(hostStateOwn (initial + 1)))
          (fun _ => iprop(hostStateOwn (initial + 2)))
          iprop(False) iprop(False)
          ⟨0⟩
          (incrTransfer (initial + 1))
          (fun _ _ _ _ _ _ _ h => by simp [incrementHost] at h)
          (fun _ _ _ _ _ _ _ _ h => by simp [incrementHost] at h)
          (s := Stuckness.NotStuck) (E := ⊤)
          (params := []) (localValues := []) (values := [])
          (code := [.call 0, .call 1, .ret])
          (arity := 1) (remainder := []) (controls := []) (calls := [])
          $$ [$Hhost1] Hruntime1 Henv
      · inext
        iintro %_ %results2 %_ %h2 ⟨Hhost2, Hruntime2⟩
        simp [incrementHost] at h2; obtain ⟨h2r, _⟩ := h2; subst h2r
        simp only [List.length_nil, List.take_zero, List.drop_zero, List.nil_append]
        -- third increment: initial+2 → initial+3
        iapply wp_callHost counterModule 0 incrImp incrementHost
            (by decide) rfl counterHostEnv rfl
            (iprop(hostStateOwn (initial + 2)))
            (fun _ => iprop(hostStateOwn (initial + 3)))
            iprop(False) iprop(False)
            ⟨0⟩
            (incrTransfer (initial + 2))
            (fun _ _ _ _ _ _ _ h => by simp [incrementHost] at h)
            (fun _ _ _ _ _ _ _ _ h => by simp [incrementHost] at h)
            (s := Stuckness.NotStuck) (E := ⊤)
            (params := []) (localValues := []) (values := [])
            (code := [.call 1, .ret])
            (arity := 1) (remainder := []) (controls := []) (calls := [])
            $$ [$Hhost2] Hruntime2 Henv
        · inext
          iintro %_ %results3 %_ %h3 ⟨Hhost3, Hruntime3⟩
          simp [incrementHost] at h3; obtain ⟨h3r, _⟩ := h3; subst h3r
          simp only [List.length_nil, List.take_zero, List.drop_zero, List.nil_append]
          -- read: returns initial+3 as i32
          iapply wp_callHost counterModule 1 readImp readCounterHost
              (by decide) rfl counterHostEnv rfl
              (iprop(hostStateOwn (initial + 3)))
              (fun results => iprop(⌜results = [.i32 (UInt32.ofNat (initial + 3))]⌝))
              iprop(False) iprop(False)
              ⟨0⟩
              (readTransfer initial)
              (fun _ _ _ _ _ _ _ h => by simp [readCounterHost] at h)
              (fun _ _ _ _ _ _ _ _ h => by simp [readCounterHost] at h)
              (s := Stuckness.NotStuck) (E := ⊤)
              (params := []) (localValues := []) (values := [])
              (code := [.ret])
              (arity := 1) (remainder := []) (controls := []) (calls := [])
              $$ [$Hhost3] Hruntime3 Henv
          · inext
            iintro %_ %results %_ %_ ⟨HQ, _⟩
            icases HQ with %hresults
            subst hresults
            simp only [List.length_nil, List.drop_zero, List.append_nil]
            iapply wp_returnFromFunction
            inext
            simp only [List.append_nil]
            iapply wp_value'
            ipureintro
            rfl
          · inext; iintro %_ %_ %_ %h _; simp [readCounterHost] at h
          · inext; iintro %_ %_ %_ %_ %h _; simp [readCounterHost] at h
        · inext; iintro %_ %_ %_ %h _; simp [incrementHost] at h
        · inext; iintro %_ %_ %_ %_ %h _; simp [incrementHost] at h
      · inext; iintro %_ %_ %_ %h _; simp [incrementHost] at h
      · inext; iintro %_ %_ %_ %_ %h _; simp [incrementHost] at h
    · inext; iintro %_ %_ %_ %h _; simp [incrementHost] at h
    · inext; iintro %_ %_ %_ %_ %h _; simp [incrementHost] at h

theorem counter_terminates :
    TerminatesWith (counterConfig 0) (fun _ _ => True) :=
  runSteps_checked_terminates (fuel := 100)
    (fun _ _ => true)
    (by native_decide)
    (fun _ _ _ => trivial)

end Wasm.SmallStep
