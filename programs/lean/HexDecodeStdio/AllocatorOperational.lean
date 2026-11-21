import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.AllocatorSteps

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- Complete one-call allocator case split.  The two successful alternatives
record whether the concrete memory was unchanged or grew; every other branch
is the distinguished OOM trap. -/
theorem allocator_call_outcome
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (size align oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295) :
    ((¬(allocatorFinish size align oldBump).toInt32 < UInt32.toInt32 0) ∧
      ((allocatorRequiredPages size align oldBump ≤
          UInt32.ofNat store.wasm.mem.pages) ∧ Reaches
        ⟨.running
          ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
            [.call 15] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        ⟨.running
          ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
            code, arity, remainder, controls, calls⟩,
          allocatorBumpStore store (allocatorFinish size align oldBump)⟩ ∨
      ∃ memory previousPages,
        store.wasm.mem.grow
            (allocatorRequiredPages size align oldBump -
              UInt32.ofNat store.wasm.mem.pages)
            (store.wasm.memoryCap store.runtime.currentModule 0) =
              some (memory, previousPages) ∧
        Reaches
          ⟨.running
            ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
              [.call 15] ++ code, arity, remainder, controls, calls⟩,
            store⟩
          ⟨.running
            ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
              code, arity, remainder, controls, calls⟩,
          allocatorBumpStore (allocatorGrownStore store memory)
              (allocatorFinish size align oldBump)⟩)) ∨
      TrapsWith
        ⟨.running
          ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
            [.call 15] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  by_cases hfirst : allocatorBase oldBump +
      ((0xffffffff : UInt32) + align) < (0xffffffff : UInt32) + align
  · right
    apply allocator_first_overflow_traps store params localValues stack code
      arity remainder controls calls size align oldBump hmod henv hread hbound
    simpa only [allocatorBase] using hfirst
  by_cases hsecond : allocatorFinish size align oldBump <
      allocatorPtr oldBump align
  · right
    apply allocator_size_overflow_traps store params localValues stack code
      arity remainder controls calls size align oldBump hmod henv hread hbound
    · simpa only [allocatorBase] using hfirst
    · simpa only [allocatorBase, allocatorPtr, allocatorFinish] using hsecond
  by_cases hnegative :
      (allocatorFinish size align oldBump).toInt32 < UInt32.toInt32 0
  · right
    apply allocator_signed_limit_traps store params localValues stack code
      arity remainder controls calls size align oldBump hmod henv hread hbound
    · simpa only [allocatorBase] using hfirst
    · simpa only [allocatorBase, allocatorPtr, allocatorFinish] using hsecond
    · simpa only [allocatorBase, allocatorPtr, allocatorFinish] using hnegative
  by_cases henough : allocatorRequiredPages size align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages
  · left
    refine ⟨hnegative, Or.inl ?_⟩
    exact ⟨henough, allocator_no_grow_steps store params localValues stack code
      arity remainder controls calls size align oldBump hmod hread hbound
      hfirst hsecond hnegative henough⟩
  · cases hgrow : store.wasm.mem.grow
        (allocatorRequiredPages size align oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) with
    | none =>
        right
        apply allocator_grow_failure_traps store params localValues stack code
          arity remainder controls calls size align oldBump hmod henv hread
          hbound
        · simpa only [allocatorBase] using hfirst
        · simpa only [allocatorBase, allocatorPtr, allocatorFinish] using hsecond
        · simpa only [allocatorBase, allocatorPtr, allocatorFinish] using hnegative
        · simpa only [allocatorBase, allocatorPtr, allocatorFinish,
            allocatorRequiredPages] using henough
        · simpa only [allocatorBase, allocatorPtr, allocatorFinish,
            allocatorRequiredPages] using hgrow
    | some result =>
        rcases result with ⟨memory, previousPages⟩
        left
        refine ⟨hnegative, Or.inr ?_⟩
        refine ⟨memory, previousPages, rfl, ?_⟩
        have hfacts :
            previousPages = store.wasm.mem.pages ∧
              memory.pages = store.wasm.mem.pages +
                (allocatorRequiredPages size align oldBump -
                  UInt32.ofNat store.wasm.mem.pages).toNat :=
          mem_grow_some_facts store.wasm.mem memory
            (allocatorRequiredPages size align oldBump -
              UInt32.ofNat store.wasm.mem.pages)
            (store.wasm.memoryCap store.runtime.currentModule 0)
            previousPages hgrow
        have hboundGrown : 1053960 + 4 ≤ memory.pages * 65536 := by
          calc
            1053960 + 4 ≤ store.wasm.mem.pages * 65536 := hbound
            _ ≤ (store.wasm.mem.pages +
                (allocatorRequiredPages size align oldBump -
                  UInt32.ofNat store.wasm.mem.pages).toNat) * 65536 := by
              omega
            _ = memory.pages * 65536 := by rw [hfacts.2]
        have hresult : previousPages.toUInt32 ≠ (0xffffffff : UInt32) := by
          rw [hfacts.1]
          intro heq
          have heqNat := congrArg UInt32.toNat heq
          rw [UInt32.toNat_ofNat_of_lt'
            (by simpa only [UInt32.size] using (show store.wasm.mem.pages <
              4294967296 by omega))] at heqNat
          have hmax : (0xffffffff : UInt32).toNat = 4294967295 := by decide
          rw [hmax] at heqNat
          omega
        exact allocator_grow_success_steps store params localValues stack code
          arity remainder controls calls size align oldBump memory previousPages
          hmod hread hbound hboundGrown hfirst hsecond hnegative henough hgrow
          hresult

end Project.HexDecodeStdio
