import Interpreter.Wasm.SmallStep
import Std.Tactic.BVDecide

/-! ## Example: memory replace

    `replace(new : i32) → i32` reads the `i32` at memory offset zero,
    writes `new`, and returns the old value. Unlike the closed memory
    examples, its main contract is symbolic over an arbitrary one-page-or-
    larger store.
-/

namespace Wasm
open SmallStep

def replaceBody : Program := [
  .const 0,
  .load32 0,
  .localSet 1,
  .const 0,
  .localGet 0,
  .store32 0,
  .localGet 1
]

def replaceModule : Module :=
  { funcs := [{ params := [.i32], locals := [.i32], body := replaceBody, results := [.i32] }]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := [42, 0, 0, 0] }] } }

theorem replaceModule_init_mem :
    (replaceModule.initialStore (α := Unit)).mem.read32 0 = 42 := by
  native_decide

def replaceStore (st : Store Unit) : MachineStore Unit :=
  { runtime := { instances := #[{ module := replaceModule, host := {} }], entry := ⟨0⟩ }
    wasm := st }

def replaceConfig (st : Store Unit) (new : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 new], locals := [.i32 0] }
        code := replaceBody
        resultArity := 1
        callerRemainder := [] }
    store := replaceStore st }

def replaceFinalStore (st : Store Unit) (new : UInt32) : MachineStore Unit :=
  { replaceStore st with
    wasm := { st with mem := st.mem.write32 0 new } }

/-- The instruction-granular relational trace of `replace`. -/
def replaceTrace : List StepKind := [
  .instruction (.const 0),
  .instruction (.load32 0),
  .instruction (.localSet 1),
  .instruction (.const 0),
  .instruction (.localGet 0),
  .instruction (.store32 0),
  .instruction (.localGet 1),
  .administrative .finish
]

theorem replace_steps (st : Store Unit) (new old : UInt32)
    (hpages : 1 ≤ st.mem.pages) (hmem : st.mem.read32 0 = old) :
    Steps (replaceConfig st new) replaceTrace
      ⟨.done [.i32 old], replaceFinalStore st new⟩ := by
  rw [← hmem]
  have hbound : 4 ≤ st.mem.pages * 65536 := by omega
  refine .cons .const ?_
  refine .cons (.load32 ?_) ?_
  · simpa [replaceStore] using hbound
  refine .cons (.localSet (by rfl)) ?_
  refine .cons .const ?_
  refine .cons (.localGet (by rfl)) ?_
  refine .cons (.store32 ?_) ?_
  · simpa [replaceStore] using hbound
  refine .cons (.localGet (by rfl)) ?_
  exact .cons .finish (.refl _)

/-- The exact finite trace, retaining the original reusable preconditions. -/
theorem replace_runs (st : Store Unit) (new old : UInt32)
    (hpages : 1 ≤ st.mem.pages) (hmem : st.mem.read32 0 = old) :
    (runSteps 8 (replaceConfig st new)).result =
      .success [.i32 old] (replaceFinalStore st new) := by
  simpa [replaceTrace] using
    SmallStep.runSteps_eq_success_of_steps
      (replace_steps st new old hpages hmem)

theorem replace_spec (st : Store Unit) (new old : UInt32)
    (hpages : 1 ≤ st.mem.pages) (hmem : st.mem.read32 0 = old) :
    TerminatesWith (replaceConfig st new) (fun values store =>
      values = [.i32 old] ∧
      store.wasm.mem.read32 0 = new) := by
  apply runSteps_success_terminates (replace_runs st new old hpages hmem)
  constructor
  · rfl
  simp [replaceFinalStore, replaceStore, Mem.read32, Mem.write32]
  bv_decide

theorem replace_partial (st : Store Unit) (new old : UInt32)
    (hpages : 1 ≤ st.mem.pages) (hmem : st.mem.read32 0 = old) :
    PartiallyMeets (replaceConfig st new) (fun values store =>
      values = [.i32 old] ∧
      store.wasm.mem.read32 0 = new) := by
  apply runSteps_success_partiallyMeets (replace_runs st new old hpages hmem)
  constructor
  · rfl
  simp [replaceFinalStore, replaceStore, Mem.read32, Mem.write32]
  bv_decide

end Wasm
