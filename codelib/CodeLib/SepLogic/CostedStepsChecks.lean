import CodeLib.SepLogic.CostedSteps
import CodeLib.SepLogic.CostedStepsStdIO
import CodeLib.SepLogic.CostedLoop

/-! Kernel-checked operation checks for the state-sensitive byte-work metric.
These are small semantic fixtures, not executions of the compiled sorter. -/

namespace Wasm.SmallStep.CostedStepsChecks

private def testModule : Module :=
  { funcs := [], memory := some { pagesMin := 1, pagesMax := some 2 } }

private def initialStore : MachineStore Unit :=
  { runtime := { instances := #[{ module := testModule, host := {} }], entry := ⟨0⟩ }
    wasm := { testModule.initialStore with
      mem := (Mem.empty 1).write8 0 171 } }

private def copiedStore : MachineStore Unit :=
  { initialStore with wasm := { initialStore.wasm with
      mem := initialStore.wasm.mem.copy 128 0 64 } }

private def grownStore : MachineStore Unit :=
  { copiedStore with wasm := { copiedStore.wasm with
      mem := { copiedStore.wasm.mem with pages := 2 } } }

private def initial : Config Unit :=
  ⟨.running ⟨⟨[], [], [.i32 64, .i32 0, .i32 128, .i32 1]⟩,
    [.memoryCopy, .memoryGrow], 1, [], [], []⟩, initialStore⟩

private def copied : Config Unit :=
  ⟨.running ⟨⟨[], [], [.i32 1]⟩, [.memoryGrow], 1, [], [], []⟩, copiedStore⟩

private def grown : Config Unit :=
  ⟨.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩, grownStore⟩

private def noHostBytes : Config Unit → Nat → Config Unit → Nat := fun _ _ _ => 0

/-- One 64-byte copy, one 64KiB growth, and one finish step compose to 65603
work units. The unchanged semantic trace still has exactly three steps. -/
theorem copy_grow_finish_cost :
    CostedSteps (byteWork noHostBytes) initial
      [.instruction .memoryCopy, .instruction .memoryGrow, .administrative .finish]
      ⟨.done [.i32 1], grownStore⟩ 65603 := by
  have copy : CostedSteps (byteWork noHostBytes) initial
      [.instruction .memoryCopy] copied 65 := by
    exact memoryCopy32_costed initialStore [] [] [.i32 1] [.memoryGrow]
      1 [] [] [] 128 0 64 (by decide) (by decide) noHostBytes
  have grow : CostedSteps (byteWork noHostBytes) copied
      [.instruction .memoryGrow] grown 65537 := by
    exact memoryGrow32_costed copiedStore [] [] [] [] 1 [] [] [] 1
      (by decide) noHostBytes
  have finish : CostedSteps (byteWork noHostBytes) grown
      [.administrative .finish] ⟨.done [.i32 1], grownStore⟩ 1 := by
    exact CostedSteps.single Step.finish
  exact copy.trans (grow.trans finish)

set_option maxRecDepth 2000 in
/-- The same trace executes in the existing runner and retains copied bytes. -/
theorem copy_grow_finish_result :
    (runSteps 3 initial).result = .success [.i32 1] grownStore ∧
    grownStore.wasm.mem.pages = 2 ∧
    grownStore.wasm.mem.read8 128 = 171 := by
  exact ⟨runSteps_eq_success_of_steps copy_grow_finish_cost.erase, rfl, rfl⟩

/-- Zero-length bulk operations still consume one progress unit. -/
theorem empty_copy_cost :
    byteWork noHostBytes
      ⟨.running ⟨⟨[], [], [.i32 0, .i32 0, .i32 0]⟩,
        [.memoryCopy], 0, [], [], []⟩, initialStore⟩
      (.instruction .memoryCopy) copied = 1 := rfl

/-- A failed growth has no added byte capacity, but does consume a step. -/
theorem failed_growth_cost :
    CostedSteps (byteWork noHostBytes)
      ⟨.running ⟨⟨[], [], [.i32 1]⟩, [.memoryGrow], 1, [], [], []⟩, grownStore⟩
      [.instruction .memoryGrow]
      ⟨.running ⟨⟨[], [], [.i32 0xFFFFFFFF]⟩, [], 1, [], [], []⟩, grownStore⟩
      1 := by
  exact CostedSteps.single (Step.memoryGrowFailure rfl)

#print axioms CostedSteps.erase
#print axioms CostedSteps.single
#print axioms CostedSteps.trans
#print axioms CostedSteps.length_le
#print axioms CostedSteps.amount_unique
#print axioms CostedSteps.potential_bound
#print axioms CostedSteps.to_languageNSteps
#print axioms Steps.with_cost
#print axioms TerminatesWithOutcome.with_cost
#print axioms TerminatesWithOutcome.with_cost_bound
#print axioms memoryCopy32_costed
#print axioms memoryGrow32_costed
#print axioms byteWork_positive
#print axioms copy_grow_finish_cost
#print axioms copy_grow_finish_result
#print axioms empty_copy_cost
#print axioms failed_growth_cost

end Wasm.SmallStep.CostedStepsChecks

namespace Wasm.SmallStep.CostedStdIOChecks

private def testModule : Module :=
  { funcs := []
    imports := [StdIO.imports[1], StdIO.imports[0]]
    memory := some { pagesMin := 1 } }

private def initialStore : MachineStore Universal.State :=
  { runtime :=
      { instances := #[{ module := testModule, host := Universal.envFor testModule }]
        entry := ⟨0⟩ }
    wasm := { testModule.initialStore (α := Universal.State) with
      host := Universal.State.ofInput [11, 22, 33] } }

private def readStore : MachineStore Universal.State :=
  { initialStore with wasm := CostedStdIO.readStore initialStore.wasm 255 3 }

private def finalStore : MachineStore Universal.State :=
  { readStore with wasm := CostedStdIO.writeStore readStore.wasm 3 3 }

private def initial : Config Universal.State :=
  ⟨.running ⟨⟨[], [], [.i32 3, .i32 255, .i32 3]⟩,
    [.call 1, .call 0], 0, [], [], []⟩, initialStore⟩

private def afterRead : Config Universal.State :=
  ⟨.running ⟨⟨[], [], [.i32 3, .i32 3]⟩, [.call 0], 0, [], [], []⟩, readStore⟩

private def afterWrite : Config Universal.State :=
  ⟨.running ⟨⟨[], [], []⟩, [], 0, [], [], []⟩, finalStore⟩

set_option maxRecDepth 2000 in
/-- A 255-byte request with only three bytes available charges three transfer
bytes. Read then write costs nine including all three semantic steps, even
with the two imports in the opposite order to the standard registry. -/
theorem read_write_finish_cost :
    CostedSteps CostedStdIO.work initial
      [.host 1, .host 0, .administrative .finish] ⟨.done [], finalStore⟩ 9 := by
  have read : CostedSteps CostedStdIO.work initial [.host 1] afterRead 4 := by
    exact CostedStdIO.read_call_costed initialStore 1 [] [] [.i32 3]
      [.call 0] 0 [] [] [] 255 3 (by decide) rfl
      (CostedStdIO.readHost_resolves testModule 1 (by decide) rfl) (by decide)
  have write : CostedSteps CostedStdIO.work afterRead [.host 0] afterWrite 4 := by
    exact CostedStdIO.write_call_costed readStore 0 [] [] []
      [] 0 [] [] [] 3 3 (by decide) rfl
      (CostedStdIO.writeHost_resolves testModule 0 (by decide) rfl) (by decide)
  have finish : CostedSteps CostedStdIO.work afterWrite [.administrative .finish]
      ⟨.done [], finalStore⟩ 1 := CostedSteps.single Step.finish
  exact read.trans (write.trans finish)

set_option maxRecDepth 2000 in
/-- The charged trace is the exact existing-runner execution and host output. -/
theorem read_write_finish_result :
    (runSteps 3 initial).result = .success [] finalStore ∧
    finalStore.wasm.host.stdio.input = [] ∧
    finalStore.wasm.host.stdio.output = [11, 22, 33] := by
  exact ⟨runSteps_eq_success_of_steps read_write_finish_cost.erase, rfl, rfl⟩

#print axioms CostedStdIO.readHost_resolves
#print axioms CostedStdIO.writeHost_resolves
#print axioms CostedStdIO.readHost_invoke
#print axioms CostedStdIO.writeHost_invoke
#print axioms CostedStdIO.read_charge
#print axioms CostedStdIO.write_charge
#print axioms CostedStdIO.read_call_costed
#print axioms CostedStdIO.write_call_costed
#print axioms read_write_finish_cost
#print axioms read_write_finish_result

end Wasm.SmallStep.CostedStdIOChecks

/-! Axiom checks for the loop-composition rule and its GCD consumer. -/

#print axioms Wasm.SmallStep.costed_loop_of_variant
#print axioms Wasm.SmallStep.CostedSteps.meets_post
#print axioms Wasm.SmallStep.Steps.with_unit_cost
#print axioms Wasm.Examples.Gcd.Cost.gcd_work_bound
#print axioms Wasm.Examples.Gcd.Cost.zero_case_exact
#print axioms Wasm.Examples.Gcd.Cost.two_iterations_exact
#print axioms Wasm.Examples.Gcd.Cost.two_iterations_runner
