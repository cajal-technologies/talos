import Project.HexStdio.Spec
import HexDecodeStdio.AllocatorSteps

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! The definitions and lemmas this file builds on live in
`HexDecodeStdio.AllocatorSteps`, shared with the decode
proofs, and are re-exported under this namespace. -/
export Project.HexDecodeStdio (
  allocatorBase allocatorPtr allocatorFinish allocatorRequiredPages Reaches
  Reaches.prepend Reaches.trans TrapsWith.prependReaches
  TerminatesWith.prependReaches mem_grow_some_facts allocatorBumpStore
  allocatorGrownStore allocator_first_overflow_traps
  allocator_size_overflow_traps allocator_signed_limit_traps
  allocator_grow_failure_traps allocator_no_grow_steps
  allocator_grow_success_steps oomFinalStore oom_wrapper_steps
  oom_wrapper_traps)

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
    ((allocatorRequiredPages size align oldBump ≤
          UInt32.ofNat store.wasm.mem.pages) ∧
        ¬ (allocatorFinish size align oldBump).toInt32 < UInt32.toInt32 0 ∧ Reaches
        ⟨.running
          ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
            [.call 15] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        ⟨.running
          ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
            code, arity, remainder, controls, calls⟩,
          allocatorBumpStore store (allocatorFinish size align oldBump)⟩ ∨
      ∃ memory previousPages,
        ¬ allocatorRequiredPages size align oldBump ≤
            UInt32.ofNat store.wasm.mem.pages ∧
        store.wasm.mem.grow
            (allocatorRequiredPages size align oldBump -
              UInt32.ofNat store.wasm.mem.pages)
            (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) ∧
        ¬ (allocatorFinish size align oldBump).toInt32 < UInt32.toInt32 0 ∧
        Reaches
          ⟨.running
            ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
              [.call 15] ++ code, arity, remainder, controls, calls⟩,
            store⟩
          ⟨.running
            ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
              code, arity, remainder, controls, calls⟩,
            allocatorBumpStore (allocatorGrownStore store memory)
              (allocatorFinish size align oldBump)⟩) ∨
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
    left
    exact ⟨henough, hnegative, allocator_no_grow_steps store params localValues stack code
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
        right
        refine ⟨memory, previousPages, henough, rfl, hnegative, ?_⟩
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

end Project.HexEncodeStdio
