import CodeLib.SepLogic.SmallStepAdequacy

/-! # Shared-memory cross-instance example

**Modeling caveat.** This example exercises the deliberate *shared-store*
model of `Wasm.SmallStep.RuntimeEnv`: all instances execute against one
physical `MachineStore.wasm` pool, so module W's `store8` lands in the very
memory module R reads back. Real Wasm instantiation gives each instance its
own address space; the theorem below is therefore a statement about the
shared-store semantics, not one that transfers to a spec-conforming engine
where the two modules would own disjoint memories. See the doc comments on
`ModuleInstance` and `RuntimeEnv` in `Interpreter/Wasm/SmallStep.lean`. -/

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

-- module B (writer): writes a byte to address 0
def writeFn : Function where
  params  := [.i32]
  locals  := []
  results := []
  body    := [.const 0, .localGet 0, .store8 0, .ret]

def moduleW : Module where
  funcs   := [writeFn]
  imports := []

def instanceW : ModuleInstance Unit where
  module          := moduleW
  host            := { funcs := [] }
  resolvedImports := #[]

-- module A (reader): imports write from B, calls it, reads back
private abbrev writeImport : ImportDecl :=
  { module := "W", name := "write", params := [.i32], results := [] }

def moduleR : Module where
  funcs   := []
  imports := [writeImport]

def instanceR : ModuleInstance Unit where
  module          := moduleR
  host            := { funcs := [] }
  resolvedImports := #[.wasm ⟨0⟩ 0]

@[simp] private theorem sharedMem_currentModule :
    ({ instances := #[instanceW, instanceR], entry := ⟨1⟩ } : RuntimeEnv Unit).currentModule =
        instanceR.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

-- entry = instance 1 (moduleR); v on top ready for cross-instance write
def sharedMemConfig (v : UInt8) : Config Unit :=
  { expr := .running
      { locals          := { params := [], locals := [], values := [.i32 v.toUInt32] }
        code            := [.call 0, .const 0, .load8U 0, .ret]
        resultArity     := 1
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime :=
          { instances := #[instanceW, instanceR]
            entry     := ⟨1⟩ }
        wasm :=
          { globals := { globals := [] }
            mem     := Mem.empty 1
            host    := () } } }

def sharedMemHeap : WasmHeapMap (Option UInt8) :=
  insert ∅ (⟨0, 0⟩ : MemoryKey) (some (0 : UInt8))

private theorem sharedMemHeap_agrees (v : UInt8) :
    heapAgreesWithMem sharedMemHeap (storeResolve (sharedMemConfig v).store) := by
  intro key value hget
  simp only [sharedMemHeap] at hget
  by_cases h : key = ⟨0, 0⟩
  · subst h
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst hget
    exact ⟨Mem.empty 1,
      by simp [storeResolve, sharedMemConfig],
      by simp [Mem.read8, Mem.empty]⟩
  · rw [get?_insert_ne (Ne.symm h), get?_empty] at hget
    contradiction

private theorem sharedMemHeap_inBounds (v : UInt8) :
    heapAddressesInBounds sharedMemHeap (storeResolve (sharedMemConfig v).store) := by
  intro key hne
  simp only [sharedMemHeap] at hne
  by_cases h : key = ⟨0, 0⟩
  · subst h
    refine ⟨Mem.empty 1, by simp [storeResolve, sharedMemConfig], ?_⟩
    simp [Mem.empty]
  · rw [get?_insert_ne (Ne.symm h), get?_empty] at hne
    simp at hne

private theorem sharedMemHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ sharedMemHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 0⟩ (DFrac.own 1) (some 0) := by
  unfold sharedMemHeap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : MemoryKey))).to_eq]
  rw [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

theorem sharedMem_partiallyMeets (v : UInt8) :
    PartiallyMeets (sharedMemConfig v)
      (fun values _ => values = [.i32 v.toUInt32]) := by
  apply wasm_smallStep_heap_runtime_instances_partiallyMeets
      (α := Unit) (σ := sharedMemHeap)
      (φ := fun values => values = [.i32 v.toUInt32])
  · exact sharedMemHeap_agrees v
  · exact sharedMemHeap_inBounds v
  · simp only [sharedMemConfig]; decide
  · intro gs
    simp only [sharedMemConfig, sharedMem_currentModule]
    iintro ⟨Hpoints, Hruntime, HruntimeInstances⟩
    ihave Hpt := sharedMemHeap_pointsTo $$ Hpoints
    -- cross-instance call to writeFn in instanceW
    iapply wp_callCrossInstance ⟨1⟩ instanceR ⟨0⟩ instanceW #[instanceW, instanceR]
        0 writeImport 0 writeFn
        rfl rfl (by decide) rfl (Nat.le.refl) rfl rfl
        $$ [Hruntime] HruntimeInstances
    · inext; iexact Hruntime
    · inext
      iintro ⟨HinstanceOwn', HruntimeInstances'⟩
      simp only [writeFn, Function.toLocals, List.map_nil]
      -- inside writeFn: [.const 0, .localGet 0, .store8 0, .ret]
      iapply wp_const
      inext
      iapply wp_localGet rfl
      inext
      ihave HptLater :
          ▷ pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
            ⟨0, 0 + 0⟩ (DFrac.own 1) (some 0) $$ [Hpt]
      · inext
        rw [UInt32.add_zero]
        iexact Hpt
      iapply wp_store8 (0 : UInt8) rfl $$ HptLater
      inext
      iintro Hpt'
      -- return from writeFn to instanceR
      iapply wp_returnFromCallCrossInstance ⟨0⟩ instanceW instanceR #[instanceW, instanceR]
          (by decide) rfl rfl
          $$ [HinstanceOwn'] HruntimeInstances'
      · inext; iexact HinstanceOwn'
      · inext
        iintro _HinstanceCaller
        -- back in instanceR: [.const 0, .load8U 0, .ret]
        iapply wp_const
        inext
        ihave HptLater2 :
            ▷ pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
              ⟨0, 0 + 0⟩ (DFrac.own 1) (some v.toUInt32.toUInt8) $$ [Hpt']
        · inext
          iexact Hpt'
        iapply wp_load8U v.toUInt32.toUInt8 rfl $$ HptLater2
        inext
        iintro _Hpt_back
        iapply wp_returnFromFunction
        inext
        iapply wp_value'
        ipureintro
        simp [List.take]

theorem sharedMem_terminates :
    TerminatesWith (sharedMemConfig 0) (fun _ _ => True) :=
  runSteps_checked_terminates (fuel := 100)
    (fun _ _ => true)
    (by native_decide)
    (fun _ _ _ => trivial)

end Wasm.SmallStep
