import HexEncodeStdio.AllocatorOperational

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Exact exceptional paths through function 18, Rust's bump reallocator.
Unlike the fresh allocator, a successful call also copies the live prefix of
the previous allocation. -/

theorem reallocator_first_overflow_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hoverflow : allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues,
            [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
          [.call 18] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]
    rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply TrapsWith.prepend Step.block
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend
    (Step.load32 (address := 0) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.ltU (result := 1) (by simp [hoverflow]))
  apply TrapsWith.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

theorem reallocator_size_overflow_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align)
    (hsecond : allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues,
            [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
          [.call 18] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]; rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply TrapsWith.prepend Step.block
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend
    (Step.load32 (address := 0) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.ltU (result := 0) (by simp [hfirst]))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.sub
  apply TrapsWith.prepend Step.and
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  have hsecond' :
      newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) <
        ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg] using hsecond
  apply TrapsWith.prepend (Step.ltU (result := 1) (by simp [hsecond']))
  apply TrapsWith.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

theorem reallocator_signed_limit_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align)
    (hnegative : (allocatorFinish newSize align oldBump).toInt32 <
      UInt32.toInt32 0) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues,
            [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
          [.call 18] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]; rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply TrapsWith.prepend Step.block
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend
    (Step.load32 (address := 0) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.ltU (result := 0) (by simp [hfirst]))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.sub
  apply TrapsWith.prepend Step.and
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  have hsecond' : ¬
      newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) <
        ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg] using hsecond
  apply TrapsWith.prepend (Step.ltU (result := 0) (by simp [hsecond']))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.ltS (result := 1) (by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg]
      using hnegative))
  apply TrapsWith.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

theorem reallocator_grow_failure_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish newSize align oldBump).toInt32 <
      UInt32.toInt32 0)
    (hneed : ¬ allocatorRequiredPages newSize align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages newSize align oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) = none) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues,
            [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
          [.call 18] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]; rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply TrapsWith.prepend Step.block
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend
    (Step.load32 (address := 0) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.ltU (result := 0) (by simp [hfirst]))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.sub
  apply TrapsWith.prepend Step.and
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  have hsecond' : ¬
      newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) <
        ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg] using hsecond
  apply TrapsWith.prepend (Step.ltU (result := 0) (by simp [hsecond']))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  have hnegative' : ¬
      (newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&&
        (-align))).toInt32 < UInt32.toInt32 0 := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg]
      using hnegative
  apply TrapsWith.prepend
    (Step.ltS (result := 0) (if_neg hnegative').symm)
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend Step.block
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend Step.shrU
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend Step.memorySize
  rw [hmod]
  have hm64 : «module».memIs64 = false := rfl
  rw [hm64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  apply TrapsWith.prepend (Step.localTee rfl)
  have hneed' : ¬
      ((65535 + (newSize + ((allocatorBase oldBump +
        (0xffffffff + align)) &&& (-align)))) >>> (16 % 32)) ≤
          UInt32.ofNat store.wasm.mem.pages := by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using hneed
  apply TrapsWith.prepend
    (Step.leU (result := 0) (if_neg hneed').symm)
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.sub
  apply TrapsWith.prepend (Step.memoryGrowFailure (by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using hgrow))
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.eq (result := 1) (by simp))
  apply TrapsWith.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

def reallocatorCopyLen (oldSize newSize : UInt32) : UInt32 :=
  if newSize < oldSize then newSize else oldSize

def reallocatorResultStore (store : MachineStore Universal.State)
    (oldPtr oldSize align newSize oldBump : UInt32) :
    MachineStore Universal.State :=
  let bumped := allocatorBumpStore store
    (allocatorFinish newSize align oldBump)
  let ptr := allocatorPtr oldBump align
  let len := reallocatorCopyLen oldSize newSize
  if ptr = 0 ∨ len = 0 then bumped
  else { bumped with wasm := { bumped.wasm with
    mem := bumped.wasm.mem.copy ptr.toNat oldPtr.toNat len.toNat } }

theorem reallocator_no_grow_steps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish newSize align oldBump).toInt32 <
      UInt32.toInt32 0)
    (henough : allocatorRequiredPages newSize align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages)
    (hsource : oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : (allocatorPtr oldBump align).toNat +
        (reallocatorCopyLen oldSize newSize).toNat ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      ⟨.running
        ⟨⟨params, localValues,
            [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
          [.call 18] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      ⟨.running
        ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
          code, arity, remainder, controls, calls⟩,
        reallocatorResultStore store oldPtr oldSize align newSize oldBump⟩ := by
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.load32 (address := 0) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU (result := 0) (by simp [hfirst]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have hsecond' : ¬
      newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) <
        ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg] using hsecond
  apply Reaches.prepend (Step.ltU (result := 0) (by simp [hsecond']))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  have hnegative' : ¬
      (newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&&
        (-align))).toInt32 < UInt32.toInt32 0 := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg]
      using hnegative
  apply Reaches.prepend
    (Step.ltS (result := 0) (if_neg hnegative').symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shrU
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.memorySize
  rw [hmod]
  have hm64 : «module».memIs64 = false := rfl
  rw [hm64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  apply Reaches.prepend (Step.localTee rfl)
  have henough' :
      ((65535 + (newSize + ((allocatorBase oldBump +
        (0xffffffff + align)) &&& (-align)))) >>> (16 % 32)) ≤
          UInt32.ofNat store.wasm.mem.pages := by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using henough
  apply Reaches.prepend
    (Step.leU (result := 1) (if_pos henough').symm)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend
    (Step.store32 (address := 0) (offset := 1053960)
      (by simpa using hbound))
  simp only [setMemory_eq, allocatorBumpStore]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz rfl)
  by_cases hptr :
      (allocatorBase oldBump + (0xffffffff + align)) &&& (0 - align) = 0
  · rw [if_pos hptr]
    have hptrDef : allocatorPtr oldBump align = 0 := by
      simpa [allocatorPtr] using hptr
    have hptrNeg :
        (allocatorBase oldBump + (0xffffffff + align)) &&& (-align) = 0 := by
      simpa [UInt32.sub_eq_add_neg] using hptr
    apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.returnFromCallExplicit rfl)
    simp only [reallocatorResultStore, hptrDef, true_or, if_true]
    simp [allocatorBumpStore, allocatorFinish, allocatorPtr, hptrNeg]
    exact ⟨[], .refl _⟩
  · rw [if_neg hptr]
    have hptrDef : allocatorPtr oldBump align ≠ 0 := by
      simpa [allocatorPtr] using hptr
    have hptrNeg :
        (allocatorBase oldBump + (0xffffffff + align)) &&& (-align) ≠ 0 := by
      simpa [UInt32.sub_eq_add_neg] using hptr
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.ltU rfl)
    apply Reaches.prepend (Step.select rfl)
    have hselect :
        (if (if newSize < oldSize then (1 : UInt32) else 0) ≠ 0 then
            Value.i32 newSize else Value.i32 oldSize) =
          .i32 (reallocatorCopyLen oldSize newSize) := by
      by_cases h : newSize < oldSize <;> simp [h, reallocatorCopyLen]
    rw [hselect]
    apply Reaches.prepend (Step.localTee rfl)
    apply Reaches.prepend (Step.eqz rfl)
    by_cases hlen : reallocatorCopyLen oldSize newSize = 0
    · rw [if_pos hlen]
      apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.returnFromCallExplicit rfl)
      simp only [reallocatorResultStore, hptrDef, hlen, or_false, if_true]
      simp [allocatorBumpStore, allocatorFinish, allocatorPtr]
      exact ⟨[], .refl _⟩
    · rw [if_neg hlen]
      apply Reaches.prepend Step.brIfZero
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.memoryCopy32
        (by
          change (allocatorPtr oldBump align).toNat +
            (reallocatorCopyLen oldSize newSize).toNat ≤
              store.wasm.mem.pages * 65536
          exact hdestination)
        (by
          change oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
            store.wasm.mem.pages * 65536
          exact hsource))
      rw [setMemory_eq]
      apply Reaches.prepend (Step.exitControl rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.returnFromCallExplicit rfl)
      simp only [reallocatorResultStore, hptrDef, hlen, or_false, if_false]
      simp [allocatorBumpStore, allocatorFinish, allocatorPtr]
      exact ⟨[], .refl _⟩

theorem reallocator_grow_success_steps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (memory : Mem) (previousPages : Nat)
    (hmod : store.runtime.currentModule = «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hboundGrown : 1053960 + 4 ≤ memory.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish newSize align oldBump).toInt32 <
      UInt32.toInt32 0)
    (hneed : ¬ allocatorRequiredPages newSize align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages newSize align oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages))
    (hresult : previousPages.toUInt32 ≠ (0xffffffff : UInt32))
    (hsource : oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
      memory.pages * 65536)
    (hdestination : (allocatorPtr oldBump align).toNat +
        (reallocatorCopyLen oldSize newSize).toNat ≤ memory.pages * 65536) :
    Reaches
      ⟨.running
        ⟨⟨params, localValues,
            [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
          [.call 18] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      ⟨.running
        ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
          code, arity, remainder, controls, calls⟩,
        reallocatorResultStore (allocatorGrownStore store memory)
          oldPtr oldSize align newSize oldBump⟩ := by
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.load32 (address := 0) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU (result := 0) (by simp [hfirst]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have hsecond' : ¬
      newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) <
        ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg] using hsecond
  apply Reaches.prepend (Step.ltU (result := 0) (by simp [hsecond']))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  have hnegative' : ¬
      (newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&&
        (-align))).toInt32 < UInt32.toInt32 0 := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg]
      using hnegative
  apply Reaches.prepend
    (Step.ltS (result := 0) (if_neg hnegative').symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shrU
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.memorySize
  rw [hmod]
  have hm64 : «module».memIs64 = false := rfl
  rw [hm64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  apply Reaches.prepend (Step.localTee rfl)
  have hneed' : ¬
      ((65535 + (newSize + ((allocatorBase oldBump +
        (0xffffffff + align)) &&& (-align)))) >>> (16 % 32)) ≤
          UInt32.ofNat store.wasm.mem.pages := by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using hneed
  apply Reaches.prepend
    (Step.leU (result := 0) (if_neg hneed').symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.memoryGrowSuccess (by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using hgrow))
  rw [setMemory_eq]
  simp only [allocatorGrownStore]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 0) (by simp [hresult]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend
    (Step.store32 (address := 0) (offset := 1053960)
      (by simpa using hboundGrown))
  simp only [setMemory_eq, allocatorBumpStore]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz rfl)
  by_cases hptr :
      (allocatorBase oldBump + (0xffffffff + align)) &&& (0 - align) = 0
  · rw [if_pos hptr]
    have hptrDef : allocatorPtr oldBump align = 0 := by
      simpa [allocatorPtr] using hptr
    have hptrNeg :
        (allocatorBase oldBump + (0xffffffff + align)) &&& (-align) = 0 := by
      simpa [UInt32.sub_eq_add_neg] using hptr
    apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.returnFromCallExplicit rfl)
    simp only [reallocatorResultStore, hptrDef, true_or, if_true]
    simp [allocatorBumpStore, allocatorGrownStore, allocatorFinish,
      allocatorPtr, hptrNeg]
    exact ⟨[], .refl _⟩
  · rw [if_neg hptr]
    have hptrDef : allocatorPtr oldBump align ≠ 0 := by
      simpa [allocatorPtr] using hptr
    have hptrNeg :
        (allocatorBase oldBump + (0xffffffff + align)) &&& (-align) ≠ 0 := by
      simpa [UInt32.sub_eq_add_neg] using hptr
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.ltU rfl)
    apply Reaches.prepend (Step.select rfl)
    have hselect :
        (if (if newSize < oldSize then (1 : UInt32) else 0) ≠ 0 then
            Value.i32 newSize else Value.i32 oldSize) =
          .i32 (reallocatorCopyLen oldSize newSize) := by
      by_cases h : newSize < oldSize <;> simp [h, reallocatorCopyLen]
    rw [hselect]
    apply Reaches.prepend (Step.localTee rfl)
    apply Reaches.prepend (Step.eqz rfl)
    by_cases hlen : reallocatorCopyLen oldSize newSize = 0
    · rw [if_pos hlen]
      apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.returnFromCallExplicit rfl)
      simp only [reallocatorResultStore, hptrDef, hlen, or_false, if_true]
      simp [allocatorBumpStore, allocatorGrownStore, allocatorFinish,
        allocatorPtr]
      exact ⟨[], .refl _⟩
    · rw [if_neg hlen]
      apply Reaches.prepend Step.brIfZero
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.memoryCopy32
        (by
          change (allocatorPtr oldBump align).toNat +
            (reallocatorCopyLen oldSize newSize).toNat ≤ memory.pages * 65536
          exact hdestination)
        (by
          change oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
            memory.pages * 65536
          exact hsource))
      rw [setMemory_eq]
      apply Reaches.prepend (Step.exitControl rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.returnFromCallExplicit rfl)
      simp only [reallocatorResultStore, hptrDef, hlen, or_false, if_false]
      simp [allocatorBumpStore, allocatorGrownStore, allocatorFinish,
        allocatorPtr]
      exact ⟨[], .refl _⟩

/-- Exhaustive outcome of one reallocator invocation.  The side conditions
are precisely the source/destination bounds needed by its final `memory.copy`;
vector callers derive them from their capacity invariant. -/
theorem reallocator_call_outcome
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hsource : oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages newSize align oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump align).toNat +
          (reallocatorCopyLen oldSize newSize).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages newSize align oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
          memory.pages * 65536 ∧
      (allocatorPtr oldBump align).toNat +
          (reallocatorCopyLen oldSize newSize).toNat ≤
          memory.pages * 65536) :
    ((allocatorRequiredPages newSize align oldBump ≤
          UInt32.ofNat store.wasm.mem.pages) ∧ Reaches
        ⟨.running
          ⟨⟨params, localValues,
              [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
            [.call 18] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        ⟨.running
          ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
            code, arity, remainder, controls, calls⟩,
          reallocatorResultStore store oldPtr oldSize align newSize oldBump⟩ ∨
      ∃ memory previousPages,
        store.wasm.mem.grow
            (allocatorRequiredPages newSize align oldBump -
              UInt32.ofNat store.wasm.mem.pages)
            (store.wasm.memoryCap store.runtime.currentModule 0) =
              some (memory, previousPages) ∧
        Reaches
          ⟨.running
            ⟨⟨params, localValues,
                [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
              [.call 18] ++ code, arity, remainder, controls, calls⟩,
            store⟩
          ⟨.running
            ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
              code, arity, remainder, controls, calls⟩,
            reallocatorResultStore (allocatorGrownStore store memory)
              oldPtr oldSize align newSize oldBump⟩) ∨
      TrapsWith
        ⟨.running
          ⟨⟨params, localValues,
              [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
            [.call 18] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  by_cases hfirst : allocatorBase oldBump +
      ((0xffffffff : UInt32) + align) < (0xffffffff : UInt32) + align
  · right
    exact reallocator_first_overflow_traps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump
      hmod henv hread hbound hfirst
  by_cases hsecond : allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align
  · right
    exact reallocator_size_overflow_traps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump
      hmod henv hread hbound hfirst hsecond
  by_cases hnegative :
      (allocatorFinish newSize align oldBump).toInt32 < UInt32.toInt32 0
  · right
    exact reallocator_signed_limit_traps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump
      hmod henv hread hbound hfirst hsecond hnegative
  by_cases henough : allocatorRequiredPages newSize align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages
  · left
    left
    exact ⟨henough, reallocator_no_grow_steps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump hmod
      hread hbound hfirst hsecond hnegative henough hsource
      (hdestination henough)⟩
  · cases hgrow : store.wasm.mem.grow
        (allocatorRequiredPages newSize align oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) with
    | none =>
        right
        exact reallocator_grow_failure_traps store params localValues stack
          code arity remainder controls calls oldPtr oldSize align newSize
          oldBump hmod henv hread hbound hfirst hsecond hnegative henough hgrow
    | some result =>
        rcases result with ⟨memory, previousPages⟩
        left
        right
        refine ⟨memory, previousPages, rfl, ?_⟩
        have hfacts := mem_grow_some_facts store.wasm.mem memory
          (allocatorRequiredPages newSize align oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0)
          previousPages hgrow
        have hboundGrown : 1053960 + 4 ≤ memory.pages * 65536 := by
          calc
            1053960 + 4 ≤ store.wasm.mem.pages * 65536 := hbound
            _ ≤ (store.wasm.mem.pages +
                (allocatorRequiredPages newSize align oldBump -
                  UInt32.ofNat store.wasm.mem.pages).toNat) * 65536 := by omega
            _ = memory.pages * 65536 := by rw [hfacts.2]
        have hresult : previousPages.toUInt32 ≠ (0xffffffff : UInt32) := by
          rw [hfacts.1]
          intro heq
          have heqNat := congrArg UInt32.toNat heq
          rw [UInt32.toNat_ofNat_of_lt'
            (by simpa only [UInt32.size] using
              (show store.wasm.mem.pages < 4294967296 by omega))] at heqNat
          have hmax : (0xffffffff : UInt32).toNat = 4294967295 := by decide
          rw [hmax] at heqNat
          omega
        have hb := hgrownBounds memory previousPages hgrow
        exact reallocator_grow_success_steps store params localValues stack
          code arity remainder controls calls oldPtr oldSize align newSize
          oldBump memory previousPages hmod hread hbound hboundGrown hfirst
          hsecond hnegative henough hgrow hresult hb.1 hb.2
end Project.HexEncodeStdio
