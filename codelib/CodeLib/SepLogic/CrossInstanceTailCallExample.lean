import CodeLib.SepLogic.SmallStepAdequacy

/-! # Cross-instance tail-call example

Two hand-built modules exercise `twp_returnCallCrossInstance`.

- **Module A** (instance 0, caller): one function whose body is `[.returnCall 0]`,
  which tail-calls import 0.  Import 0 is resolved to instance 1's function 0.
- **Module B** (instance 1, callee): one function whose body is `[.const 42, .ret]`,
  returning the constant 42.

The theorem `tailCallCrossInstance_partiallyMeets` proves that running the caller
function to completion always yields `[.i32 42]`, using the total-WP rule
`twp_returnCallCrossInstance` together with `wasm_smallStep_runtime_instance_partiallyMeets`.
-/

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

/-! ### Helper -/

@[simp] private theorem RuntimeEnv.currentModule_inst0_of2
    {α : Type} (i1 i2 : ModuleInstance α) :
    ({ instances := #[i1, i2], entry := ⟨0⟩ } : RuntimeEnv α).currentModule = i1.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

/-! ### Module B (callee): returns the constant 42 -/

def constFn : Function where
  results := [.i32]
  body    := [.const 42, .ret]

def modB : Module where
  funcs := [constFn]

/-! ### Module A (caller): tail-calls import 0 -/

private abbrev tailCallImp : ImportDecl :=
  { «module» := "B", name := "const42", params := [], results := [.i32] }

def tailCallFn : Function where
  results := [.i32]
  body    := [.returnCall 0]

def modA : Module where
  imports := [tailCallImp]
  funcs   := [tailCallFn]

/-! ### Instances -/

/-- Instance 0 (caller): modA, import 0 resolved to instance 1's function 0.
Its import slot aliases that function's address `0`; its own function owns
the fresh address `1`. -/
def instA : ModuleInstance Unit where
  module          := modA
  host            := { funcs := [] }
  resolvedImports := #[.wasm ⟨1⟩ 0]
  funcaddrs       := #[0, 1]

/-- Instance 1 (callee): modB, no imports; its function owns address `0`. -/
def instB : ModuleInstance Unit where
  module    := modB
  host      := { funcs := [] }
  funcaddrs := #[0]

/-- Addresses are distinct by construction, not by the identity default. -/
theorem instances_funcaddrsWellFormed :
    ({ instances := #[instA, instB], entry := ⟨0⟩ } : RuntimeEnv Unit).funcaddrsWellFormed =
      true := by
  decide +kernel

@[simp] private theorem instA_module : instA.module = modA := rfl

/-! ### Config -/

def tailCallConfig : Config Unit :=
  { expr  := .running
      { locals          := {}
        code            := [.returnCall 0]
        resultArity     := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[instA, instB], entry := ⟨0⟩ }
        wasm    :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := () } } }

/-! ### Partial-correctness theorem -/

theorem tailCallCrossInstance_partiallyMeets :
    PartiallyMeets tailCallConfig (fun values _ => values = [.i32 42]) := by
  apply wasm_smallStep_runtime_instance_partiallyMeets
  · decide
  · intro gs
    simp only [tailCallConfig, RuntimeEnv.currentModule_inst0_of2, instA_module]
    iintro ⟨Hruntime, HruntimeInstances⟩
    iapply twp.to_wp
    simp only [runtimeModuleOwn]
    icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
    iintuitionistic HruntimeElem
    iapply twp_returnCallCrossInstance ⟨0⟩ instA ⟨1⟩ instB #[instA, instB]
        0 tailCallImp 0 constFn rfl rfl (by decide) rfl Nat.le.refl rfl rfl
        $$ [HinstanceOwn] HruntimeInstances
    · -- prove runtimeModuleOwn ⟨0⟩ modA
      simp only [runtimeModuleOwn, instA_module]
      isplitl []
      · iexact HruntimeElem
      · iexact HinstanceOwn
    · -- continuation: prove the callee's WP
      iintro ⟨HinstanceOwn', HruntimeInstances'⟩
      iclear HinstanceOwn' HruntimeInstances'
      simp only [constFn, Function.toLocals, List.map_nil,
                 List.length_nil, List.take_zero, List.reverse_nil]
      iapply twp_const
      iapply twp_returnFromFunction
      simp only [List.take_succ_cons, List.take_zero, List.append_nil]
      iapply twp.value rfl
      ipureexact rfl

/-! ### Chaining: two cross-instance `call_ref`s in a row

`runtimeInstancesOwn` is an exclusive fragment, so every rule that reads it
hands it back. Here the caller takes `ref.func 0` (its import, aliasing
instance 1's `constFn`), calls it with `call_ref`, and after
`wp_returnFromCallCrossInstance` uses the returned token for a second
`ref.func` / `call_ref` round trip. -/

private abbrev constFnType : FuncType := { results := [.i32] }

def refChainFn : Function where
  results := [.i32]
  body    := [.refFunc 0, .callRef 0, .refFunc 0, .callRef 0, .add, .ret]

def refChainModA : Module where
  imports := [tailCallImp]
  types   := [constFnType]
  funcs   := [refChainFn]

def refChainInstA : ModuleInstance Unit where
  module          := refChainModA
  host            := { funcs := [] }
  resolvedImports := #[.wasm ⟨1⟩ 0]
  funcaddrs       := #[0, 1]

@[simp] private theorem refChainInstA_module : refChainInstA.module = refChainModA := rfl

theorem refChain_funcaddrsWellFormed :
    ({ instances := #[refChainInstA, instB], entry := ⟨0⟩ } : RuntimeEnv Unit).funcaddrsWellFormed =
      true := by
  decide +kernel

def refChainConfig : Config Unit :=
  { expr  := .running
      { locals          := {}
        code            := refChainFn.body
        resultArity     := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[refChainInstA, instB], entry := ⟨0⟩ }
        wasm    :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := () } } }

theorem chainedCallRef_partiallyMeets :
    PartiallyMeets refChainConfig (fun values _ => values = [.i32 84]) := by
  apply wasm_smallStep_runtime_instance_partiallyMeets
  · decide
  · intro gs
    simp only [refChainConfig, refChainFn, RuntimeEnv.currentModule_inst0_of2, refChainInstA_module]
    iintro ⟨Hruntime, HruntimeInstances⟩
    simp only [runtimeModuleOwn]
    icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
    iintuitionistic HruntimeElem
    -- round 1: `ref.func 0` then cross-instance `call_ref`
    iapply wp_refFunc refChainModA ⟨0⟩ 0 (functionIndex := 0) (instances := #[refChainInstA, instB])
        (callerInst := refChainInstA) rfl rfl $$ [HinstanceOwn] HruntimeInstances
    · inext
      simp only [runtimeModuleOwn]
      isplitl []
      · iexact HruntimeElem
      · iexact HinstanceOwn
    inext
    iintro ⟨Hruntime, HruntimeInstances⟩
    simp only [runtimeModuleOwn]
    icases Hruntime with ⟨-, HinstanceOwn⟩
    iapply wp_callRefCrossInstance ⟨0⟩ ⟨1⟩ instB #[refChainInstA, instB] 0 0 0 constFn
        rfl (by decide) rfl (by decide +kernel) (by decide)
        $$ [HinstanceOwn] HruntimeInstances
    · inext; iexact HinstanceOwn
    inext
    iintro ⟨HinstanceOwn, HruntimeInstances⟩
    simp only [constFn, Function.toLocals, List.map_nil]
    wasm_wp_pures [wp_const]
    iapply wp_returnFromCallCrossInstance ⟨1⟩ instB refChainInstA #[refChainInstA, instB]
        (by decide) rfl rfl $$ [HinstanceOwn] HruntimeInstances
    · inext; iexact HinstanceOwn
    inext
    -- the token came back: round 2 reuses it
    iintro ⟨HinstanceOwn, HruntimeInstances⟩
    iapply wp_refFunc refChainModA ⟨0⟩ 0 (functionIndex := 0) (instances := #[refChainInstA, instB])
        (callerInst := refChainInstA) rfl rfl $$ [HinstanceOwn] HruntimeInstances
    · inext
      simp only [runtimeModuleOwn]
      isplitl []
      · iexact HruntimeElem
      · iexact HinstanceOwn
    inext
    iintro ⟨Hruntime, HruntimeInstances⟩
    simp only [runtimeModuleOwn]
    icases Hruntime with ⟨-, HinstanceOwn⟩
    iapply wp_callRefCrossInstance ⟨0⟩ ⟨1⟩ instB #[refChainInstA, instB] 0 0 0 constFn
        rfl (by decide) rfl (by decide +kernel) (by decide)
        $$ [HinstanceOwn] HruntimeInstances
    · inext; iexact HinstanceOwn
    inext
    iintro ⟨HinstanceOwn, HruntimeInstances⟩
    simp only [constFn, Function.toLocals, List.map_nil]
    wasm_wp_pures [wp_const]
    iapply wp_returnFromCallCrossInstance ⟨1⟩ instB refChainInstA #[refChainInstA, instB]
        (by decide) rfl rfl $$ [HinstanceOwn] HruntimeInstances
    · inext; iexact HinstanceOwn
    inext
    iintro ⟨-, -⟩
    try simp only [Function.numParams, List.length_cons, List.length_nil, Nat.zero_add,
      List.take, List.drop, List.nil_append, List.cons_append]
    wasm_wp_pures [wp_add]
    wasm_wp_return_value
    ipureexact rfl

end Wasm.SmallStep
