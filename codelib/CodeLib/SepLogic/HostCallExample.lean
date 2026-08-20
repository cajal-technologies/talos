import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

-- host import: takes (addr : i32, val : i32), writes val.toUInt8 to memory[addr]
def writeByteHost : HostFn Unit where
  params  := [.i32, .i32]
  results := []
  invoke  := fun wasmStore args =>
    match args with
    | [.i32 addr, .i32 val] =>
      .Return [] { wasmStore with mem := wasmStore.mem.write8 addr val.toUInt8 }
    | _ => .Trap wasmStore "writeByteHost: bad args"

private abbrev writeByteImp : ImportDecl :=
  { module := "", name := "writeByte", params := [.i32, .i32], results := [] }

def writeByteModule : Module where
  funcs   := []
  imports := [writeByteImp]

def writeByteRuntime : RuntimeEnv Unit :=
  { instances := #[{ module := writeByteModule, host := { funcs := [writeByteHost] } }]
    entry := ⟨0⟩ }

def writeByteInitStore : Store Unit where
  globals := { globals := [] }
  mem     := Mem.empty 1
  host    := ()

-- stack [.i32 42, .i32 0]: val=42 on top, addr=0 below
-- (values.take 2).reverse = [.i32 0, .i32 42] -> addr=0, val=42
def writeByteConfig : Config Unit :=
  { expr := .running
      { locals := { values := [.i32 42, .i32 0] }
        code := [.call 0], resultArity := 0, callerRemainder := [] }
    store := { runtime := writeByteRuntime, wasm := writeByteInitStore } }

theorem writeByte_partiallyMeets :
    PartiallyMeets writeByteConfig (fun values (store : MachineStore Unit) =>
        values = [] ∧ store.wasm.mem.read8 0 = 42) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := insert ∅ ⟨0, 0⟩ (some (0 : UInt8)))
    (globalσ := (∅ : WasmGlobalMap Value))
  · intro addr v hget
    by_cases h : addr = ⟨0, 0⟩
    · subst h
      rw [get?_insert_eq rfl] at hget
      have hv := Option.some.inj (Option.some.inj hget)
      subst hv
      exact ⟨_, rfl, by decide⟩
    · rw [get?_insert_ne (Ne.symm h), get?_empty] at hget
      contradiction
  · intro addr hget
    by_cases h : addr = ⟨0, 0⟩
    · subst h
      exact ⟨_, rfl, by decide⟩
    · rw [get?_insert_ne (Ne.symm h), get?_empty] at hget
      contradiction
  · exact globalHeapAgrees_empty _
  · decide
  · intro gs
    simp only [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : MemoryKey))).to_eq,
               BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
    iintro ⟨Hpt, _Hglobals, Hruntime, Henv⟩
    simp only [writeByteConfig, writeByteRuntime, RuntimeEnv.currentModule_mk1,
               RuntimeEnv.currentHost_mk1]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
            ⟨0, 0⟩ (DFrac.own 1) (some (42 : UInt8))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read8 0 = 42⌝) := by
      intro values
      iintro ⟨%hvalues, Hbyte⟩ %store %_observations Hstate
      imod stateInterp_pointsTo_read8 store 0 [] 0 0 (42 : UInt8)
          $$ [$Hstate $Hbyte] with %hread
      ipureintro
      exact ⟨hvalues, hread⟩
    iapply (wp_mono hpost)
    iapply wp_callHost writeByteModule 0 writeByteImp writeByteHost
        (by simp [writeByteModule]) rfl { funcs := [writeByteHost] } rfl
        (iprop(pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          ⟨0, 0⟩ (DFrac.own 1) (some (0 : UInt8))))
        (fun _ => iprop(pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          ⟨0, 0⟩ (DFrac.own 1) (some (42 : UInt8))))
        (iprop(False))
        (iprop(False))
        ⟨0⟩
        -- ghost write: pointsTo 0 (some 0) ∗ stateInterp ==∗ pointsTo 0 (some 42) ∗ stateInterp'
        (fun store ns obs nt _ results postWasm h => by
          simp [writeByteHost] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          iintro ⟨Hpt, Hσ⟩
          ihave %HinBounds :
              ⌜(0 : UInt32).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
          · imod stateInterp_pointsTo_inBounds store ns obs nt 0 (0 : UInt8)
                $$ [$Hσ $Hpt] with %HinBounds
            ipureintro
            exact HinBounds
          imod stateInterp_store8 store ns obs nt (0 : UInt32) (0 : UInt8) (42 : UInt8)
              (by exact HinBounds) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
          imodintro
          isplitl [Hpt]
          · iexact Hpt
          · iexact Hσ)
        -- trap: impossible with args [.i32 0, .i32 42]
        (fun _ _ _ _ _ _ _ h => by simp [writeByteHost] at h)
        -- throw: impossible
        (fun _ _ _ _ _ _ _ _ h => by simp [writeByteHost] at h)
        (s := Stuckness.NotStuck) (E := ⊤)
        (params := []) (localValues := []) (values := [.i32 42, .i32 0])
        (code := []) (arity := 0) (remainder := []) (controls := []) (calls := [])
        $$ [$Hpt] Hruntime Henv
    -- return: QRet [] = pointsTo 0 (some 42); close Φ_simple
    · inext
      iintro %preWasm %results %postWasm %h ⟨HQ, _⟩
      simp only [List.take_zero, List.nil_append, List.length_cons,
                 List.length_nil, List.drop]
      iapply wp_finish
      inext
      iapply wp_value'
      isplitr [HQ]
      · ipureintro
        rfl
      · iexact HQ
    -- trap: refuted by simp
    · inext
      iintro %preWasm %postWasm %msg %h _HQ
      simp [writeByteHost] at h
    -- throw: refuted by simp
    · inext
      iintro %preWasm %postWasm %tag %xs %h _HQ
      simp [writeByteHost] at h

theorem writeByte_terminates :
    TerminatesWith writeByteConfig (fun _ _ => True) :=
  runSteps_checked_terminates (fuel := 20)
    (fun _ _ => true)
    (by native_decide)
    (fun _ _ _ => trivial)

theorem writeByte_result :
    TerminatesWith writeByteConfig (fun values (store : MachineStore Unit) =>
        values = [] ∧ store.wasm.mem.read8 0 = 42) :=
  TerminatesWith.of_termination_and_partial writeByte_terminates writeByte_partiallyMeets

end Wasm.SmallStep
