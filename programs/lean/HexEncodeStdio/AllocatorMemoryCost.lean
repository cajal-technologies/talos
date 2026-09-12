import HexEncodeStdio.AllocatorOperational
import CodeLib.SepLogic.CostedStepsStdIO

set_option maxRecDepth 100000

/-!
# Memory and work of the compiled hex allocator

These results consume the shared trace-cost and prefix-memory rules for actual
hex allocator calls. The successful branches reuse the existing instruction
proofs, now retaining exact trace lengths and admissible labels. Growth still
requires its concrete success equation; no input-budget or whole-export
success theorem is inferred here.
-/

namespace Project.HexEncodeStdio.AllocatorMemoryCost

open Wasm Wasm.SmallStep Project.HexStdio

abbrev callConfig (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (size align : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
    .call 15 :: code, arity, remainder, controls, calls⟩, store⟩

abbrev returnConfig (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (pointer : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨params, localValues, .i32 pointer :: stack⟩,
    code, arity, remainder, controls, calls⟩, store⟩

/-- An accepted allocation already covered by physical memory costs exactly
49 transitions and preserves pages at every actual prefix through return. -/
theorem allocator_no_grow_memory_work
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (size align oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump +
      ((0xffffffff : UInt32) + align) < (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish size align oldBump < allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish size align oldBump).toInt32 < UInt32.toInt32 0)
    (henough : allocatorRequiredPages size align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages) :
    ∃ trace, trace.length = 49 ∧
      CostedSteps CostedStdIO.work
        (callConfig store params localValues stack code arity remainder controls calls size align)
        trace
        (returnConfig (allocatorBumpStore store (allocatorFinish size align oldBump))
          params localValues stack code arity remainder controls calls
          (allocatorPtr oldBump align)) 49 ∧
      ∀ prefixTrace middle,
        Steps (callConfig store params localValues stack code arity remainder controls calls
          size align) prefixTrace middle → prefixTrace.length ≤ 49 →
        middle.store.wasm.mem.pages = store.wasm.mem.pages := by
  obtain ⟨trace, length, labels, execution⟩ := allocator_no_grow_steps_trace
    store params localValues stack code arity remainder controls calls
    size align oldBump hmod hread hbound hfirst hsecond hnegative henough
  refine ⟨trace, length, ?_, ?_⟩
  · have pages : (allocatorBumpStore store (allocatorFinish size align oldBump)).wasm.mem.pages =
        store.wasm.mem.pages := rfl
    simpa only [length, pages, Nat.sub_self, Nat.mul_zero, Nat.add_zero,
      CostedStdIO.work, callConfig, returnConfig, List.cons_append, List.nil_append] using
      execution.growth_byteWork labels CostedStdIO.hostBytes
  · intro prefixTrace middle first bound
    have pages := execution.primary_pages_at_prefix first
      (by simpa only [length] using bound)
      (fun kind member => (labels kind member).primary)
    exact Nat.le_antisymm pages.2 pages.1

/-- The actual successful-growth call costs its 56 transitions plus every
newly added physical byte. Every actual prefix through caller resumption lies
between the initial and final page counts. The success equation is explicit. -/
theorem allocator_grow_memory_work
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (size align oldBump : UInt32) (memory : Mem) (previousPages : Nat)
    (hmod : store.runtime.currentModule = «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hboundGrown : 1053960 + 4 ≤ memory.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump +
      ((0xffffffff : UInt32) + align) < (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish size align oldBump < allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish size align oldBump).toInt32 < UInt32.toInt32 0)
    (hneed : ¬ allocatorRequiredPages size align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages)
    (hgrow : store.wasm.mem.grow
      (allocatorRequiredPages size align oldBump - UInt32.ofNat store.wasm.mem.pages)
      (store.wasm.memoryCap store.runtime.currentModule 0) = some (memory, previousPages))
    (hresult : previousPages.toUInt32 ≠ (0xffffffff : UInt32)) :
    ∃ trace, trace.length = 56 ∧
      CostedSteps CostedStdIO.work
        (callConfig store params localValues stack code arity remainder controls calls size align)
        trace
        (returnConfig (allocatorBumpStore (allocatorGrownStore store memory)
          (allocatorFinish size align oldBump))
          params localValues stack code arity remainder controls calls
          (allocatorPtr oldBump align))
        (56 + 65536 * (memory.pages - store.wasm.mem.pages)) ∧
      ∀ prefixTrace middle,
        Steps (callConfig store params localValues stack code arity remainder controls calls
          size align) prefixTrace middle → prefixTrace.length ≤ 56 →
        store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
          middle.store.wasm.mem.pages ≤ memory.pages := by
  obtain ⟨trace, length, labels, execution⟩ := allocator_grow_success_steps_trace
    store params localValues stack code arity remainder controls calls
    size align oldBump memory previousPages hmod hread hbound hboundGrown
    hfirst hsecond hnegative hneed hgrow hresult
  refine ⟨trace, length, ?_, ?_⟩
  · have pages : (allocatorBumpStore (allocatorGrownStore store memory)
        (allocatorFinish size align oldBump)).wasm.mem.pages = memory.pages := rfl
    simpa only [length, pages, CostedStdIO.work, callConfig, returnConfig,
      List.cons_append, List.nil_append] using
      execution.growth_byteWork labels CostedStdIO.hostBytes
  · intro prefixTrace middle first bound
    exact execution.primary_pages_at_prefix first
      (by simpa only [length] using bound)
      (fun kind member => (labels kind member).primary)

/-- The module's actual initialized memory and Universal host, before any
input is read. The test enters the allocator directly at its absolute index. -/
def boundaryStore : MachineStore Universal.State :=
  { runtime :=
      { instances := #[{ module := «module», host := Universal.envFor «module» }]
        entry := ⟨0⟩ }
    wasm := { («module».initialStore : Store Universal.State) with
      host := Universal.State.ofInput [] } }

def boundaryCall : Config Universal.State :=
  callConfig boundaryStore [] [] [] [.drop, .const 1, .memoryGrow]
    0 [] [] [] 65536 1

def boundaryReturn : Config Universal.State :=
  returnConfig
    (allocatorBumpStore (allocatorGrownStore boundaryStore
      { boundaryStore.wasm.mem with pages := 18 }) 1119536)
    [] [] [] [.drop, .const 1, .memoryGrow] 0 [] [] [] 1054000

/-- A real growth request instantiates the generic theorem: a fresh 65,536-byte
block at the initial bump grows from 17 to 18 pages and charges 65,592 work. -/
theorem boundary_call_memory_work :
    ∃ trace, trace.length = 56 ∧
      CostedSteps CostedStdIO.work boundaryCall trace boundaryReturn 65592 ∧
      ∀ prefixTrace middle, Steps boundaryCall prefixTrace middle → prefixTrace.length ≤ 56 →
        17 ≤ middle.store.wasm.mem.pages ∧ middle.store.wasm.mem.pages ≤ 18 := by
  exact allocator_grow_memory_work boundaryStore [] [] [] [.drop, .const 1, .memoryGrow]
    0 [] [] [] 65536 1 0 { boundaryStore.wasm.mem with pages := 18 } 17
    rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl (by decide)

/-- The generic certificate's precise endpoint is the executable 56-step
endpoint. Three later caller transitions grow to 19 pages, outside its bound. -/
theorem boundary_runner :
    (runSteps 56 boundaryCall).result = .outOfFuel boundaryReturn ∧
    (runSteps 59 boundaryCall).result.finalConfig?.map
      (fun final => final.store.wasm.mem.pages) = some 19 := by
  obtain ⟨trace, length, execution, _⟩ := boundary_call_memory_work
  constructor
  · simpa only [length, boundaryReturn, returnConfig] using
      runSteps_finalConfig_of_steps execution.erase
  · rfl

end Project.HexEncodeStdio.AllocatorMemoryCost
