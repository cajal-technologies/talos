import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

-- void function: no args, no results, immediately returns
def xFn : Function where
  params  := []
  locals  := []
  results := []
  body    := [.ret]

private abbrev xImp : ImportDecl :=
  { module := "", name := "f", params := [], results := [] }

def xModule : Module where
  funcs   := [xFn]
  imports := [xImp]

-- two identical instances; import 0 resolves to (instance 1, function 0)
def xInst : ModuleInstance Unit where
  module          := xModule
  host            := { funcs := [] }
  resolvedImports := #[.wasm ⟨1⟩ 0]

@[simp] private theorem xInst_currentModule :
    ({ instances := #[xInst, xInst], entry := ⟨0⟩ } : RuntimeEnv Unit).currentModule = xInst.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

-- Single-instance predecessor: one copy of xInst, same shape as twoModuleConfig
def oneModuleConfig : Config Unit :=
  { expr := .running
      { locals          := { params := [], locals := [], values := [] }
        code            := [.call 0]
        resultArity     := 0
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime :=
          { instances := #[xInst]
            entry     := ⟨0⟩ }
        wasm :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := () } } }

def twoModuleConfig : Config Unit :=
  { expr := .running
      { locals          := { params := [], locals := [], values := [] }
        code            := [.call 0]
        resultArity     := 0
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime :=
          { instances := #[xInst, xInst]
            entry     := ⟨0⟩ }
        wasm :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := () } } }

-- twoModuleConfig's store is oneModuleConfig's store with xInst pushed
private theorem twoModule_store_eq_push :
    twoModuleConfig.store =
      { oneModuleConfig.store with runtime :=
          { oneModuleConfig.store.runtime with
            instances := oneModuleConfig.store.runtime.instances.push xInst } } := rfl

/-- Ghost-state update: the two-instance stateInterp can be derived from a
one-instance stateInterp together with the runtimeInstancesOwn fragment via
`stateInterp_instantiate`.  This is the ghost counterpart of a successful
`SmallStep.instantiate` call that adds the second copy of `xInst`. -/
theorem twoModule_stateInterp_from_instantiate [WasmSmallStepGS .hasLC Unit] :
    stateInterp (GF := WasmHeapGF Unit) oneModuleConfig.store 0 [] 0 ∗
      runtimeInstancesOwn oneModuleConfig.store.runtime.instances ==∗
      stateInterp (GF := WasmHeapGF Unit) twoModuleConfig.store 0 [] 0 ∗
      runtimeInstancesOwn #[xInst, xInst] ∗
      runtimeModuleElem 1 xInst.module := by
  rw [twoModule_store_eq_push]
  exact stateInterp_instantiate oneModuleConfig.store 0 [] 0 xInst

/-- Cross-instance call then immediate void return: instance 0 calls import 0
(resolved to instance 1, function 0), which executes a single `.ret` and
resumes the caller. -/
theorem twoModule_partiallyMeets :
    PartiallyMeets twoModuleConfig (fun values _store => values = []) := by
  apply wasm_smallStep_runtime_instance_partiallyMeets (α := Unit)
  wasm_adequacy_intro gs =>
    simp only [twoModuleConfig, xInst_currentModule]
    iintro ⟨Hruntime, HruntimeInstances⟩
    iapply wp_callCrossInstance ⟨0⟩ xInst ⟨1⟩ xInst #[xInst, xInst] 0 xImp 0 xFn
        rfl rfl (by decide) rfl (Nat.le.refl) rfl rfl
        $$ [Hruntime] HruntimeInstances
    · inext; iexact Hruntime
    · inext
      iintro ⟨HinstanceOwn', HruntimeInstances'⟩
      simp only [xFn, Function.toLocals, List.map_nil, List.length_nil,
                 List.take_zero, List.reverse_nil, List.drop_zero]
      iapply wp_returnFromCallCrossInstance ⟨1⟩ xInst xInst #[xInst, xInst]
          (by decide) rfl rfl
          $$ [HinstanceOwn'] HruntimeInstances'
      · inext; iexact HinstanceOwn'
      · inext
        iintro ⟨_HinstanceCaller, -⟩
        simp only [List.take_zero, List.nil_append]
        wasm_wp_finish_value_rfl

end Wasm.SmallStep
