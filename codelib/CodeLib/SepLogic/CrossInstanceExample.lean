import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

-- library module (B): exports add, no imports
def addLibFn : Function where
  params  := [.i32, .i32]
  locals  := []
  results := [.i32]
  body    := [.localGet 1, .localGet 0, .add, .ret]

def moduleB : Module where
  funcs   := [addLibFn]
  imports := []

def instanceB : ModuleInstance Unit where
  module          := moduleB
  host            := { funcs := [] }
  resolvedImports := #[]

-- caller module (A): imports add from B, no local functions
private abbrev addFromB : ImportDecl :=
  { module := "B", name := "add", params := [.i32, .i32], results := [.i32] }

def moduleA : Module where
  funcs   := []
  imports := [addFromB]

def instanceA : ModuleInstance Unit where
  module          := moduleA
  host            := { funcs := [] }
  resolvedImports := #[.wasm ⟨0⟩ 0]

@[simp] private theorem crossInstance_currentModule :
    ({ instances := #[instanceB, instanceA], entry := ⟨1⟩ } : RuntimeEnv Unit).currentModule =
        instanceA.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

-- entry = instance 1 (moduleA); values [b, a] ready for cross-instance call to instance 0
def crossInstanceConfig (a b : UInt32) : Config Unit :=
  { expr := .running
      { locals          := { params := [], locals := [], values := [.i32 b, .i32 a] }
        code            := [.call 0]
        resultArity     := 1
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime :=
          { instances := #[instanceB, instanceA]
            entry     := ⟨1⟩ }
        wasm :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := () } } }

theorem crossInstance_partiallyMeets (a b : UInt32) :
    PartiallyMeets (crossInstanceConfig a b) (fun values _ => values = [.i32 (a + b)]) := by
  apply wasm_smallStep_runtime_instance_partiallyMeets (α := Unit)
  · simp only [crossInstanceConfig]; decide
  · intro gs
    simp only [crossInstanceConfig, crossInstance_currentModule]
    iintro ⟨Hruntime, HruntimeInstances⟩
    iapply wp_callCrossInstance ⟨1⟩ instanceA ⟨0⟩ instanceB #[instanceB, instanceA]
        0 addFromB 0 addLibFn
        rfl rfl (by decide) rfl (Nat.le.refl) rfl rfl
        $$ [Hruntime] HruntimeInstances
    · inext; iexact Hruntime
    · inext
      iintro ⟨HinstanceOwn', HruntimeInstances'⟩
      simp only [addLibFn, Function.toLocals, List.map_nil]
      iapply wp_localGet rfl
      inext
      iapply wp_localGet rfl
      inext
      iapply wp_add
      inext
      iapply wp_returnFromCallCrossInstance ⟨0⟩ instanceB instanceA #[instanceB, instanceA]
          (by decide) rfl rfl
          $$ [HinstanceOwn'] HruntimeInstances'
      · inext; iexact HinstanceOwn'
      · inext
        iintro _HinstanceCaller
        iapply wp_finish
        inext
        iapply wp_value'
        ipureintro
        rfl

theorem crossInstance_terminates :
    TerminatesWith (crossInstanceConfig 3 5) (fun _ _ => True) :=
  runSteps_checked_terminates (fuel := 30)
    (fun _ _ => true)
    (by native_decide)
    (fun _ _ _ => trivial)

theorem crossInstance_result :
    TerminatesWith (crossInstanceConfig 3 5)
      (fun values _ => values = [.i32 8]) :=
  TerminatesWith.of_termination_and_partial crossInstance_terminates
    (crossInstance_partiallyMeets 3 5)

end Wasm.SmallStep
