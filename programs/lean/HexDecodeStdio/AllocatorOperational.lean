import HexDecodeStdio.OperationalOutcome

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Operational OOM legs of the bump allocator.  These lemmas complement the
Iris normal-return specification: they retain the exact trap reason and host
store when an arithmetic guard selects the private OOM wrapper. -/

def allocatorBase (oldBump : UInt32) : UInt32 :=
  if oldBump = 0 then 1054000 else oldBump

def allocatorPtr (oldBump align : UInt32) : UInt32 :=
  (allocatorBase oldBump + ((0xffffffff : UInt32) + align)) &&& (0 - align)

def allocatorFinish (size align oldBump : UInt32) : UInt32 :=
  size + allocatorPtr oldBump align

def allocatorRequiredPages (size align oldBump : UInt32) : UInt32 :=
  (65535 + allocatorFinish size align oldBump) >>> (16 % 32)

def Reaches (initial final : Config Universal.State) : Prop :=
  ∃ trace, Steps initial trace final

theorem Reaches.prepend {initial next final : Config Universal.State}
    {kind : StepKind} (head : Step initial kind next)
    (tail : Reaches next final) : Reaches initial final := by
  obtain ⟨trace, htrace⟩ := tail
  exact ⟨kind :: trace, .cons head htrace⟩

theorem Reaches.trans {initial middle final : Config Universal.State}
    (first : Reaches initial middle) (second : Reaches middle final) :
    Reaches initial final := by
  obtain ⟨pre, hpre⟩ := first
  obtain ⟨suffix, hsuffix⟩ := second
  exact ⟨pre ++ suffix, hpre.trans hsuffix⟩

theorem TrapsWith.prependReaches
    {initial middle : Config Universal.State} {reason : TrapReason}
    {post : MachineStore Universal.State → Prop}
    (pre : Reaches initial middle) (suffix : TrapsWith middle reason post) :
    TrapsWith initial reason post := by
  obtain ⟨trace, htrace⟩ := pre
  exact TrapsWith.prependSteps htrace suffix

theorem TerminatesWith.prependReaches
    {initial middle : Config Universal.State}
    {post : List Value → MachineStore Universal.State → Prop}
    (pre : Reaches initial middle) (suffix : TerminatesWith middle post) :
    TerminatesWith initial post := by
  obtain ⟨trace, htrace⟩ := pre
  exact TerminatesWith.prependSteps htrace suffix

theorem mem_grow_some_facts (mem memory : Mem) (delta : UInt32) (cap previous : Nat)
    (h : mem.grow delta cap = some (memory, previous)) :
    previous = mem.pages ∧ memory.pages = mem.pages + delta.toNat := by
  simp only [Mem.grow] at h
  split at h
  · exact ⟨(Prod.mk.inj (Option.some.inj h)).2.symm,
      congrArg Mem.pages (Prod.mk.inj (Option.some.inj h)).1.symm⟩
  · contradiction

def allocatorBumpStore (store : MachineStore Universal.State)
    (finish : UInt32) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with
      mem := store.wasm.mem.write32 1053960 finish } }

def allocatorGrownStore (store : MachineStore Universal.State)
    (memory : Mem) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with mem := memory } }

theorem allocator_first_overflow_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (size align oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hoverflow :
      ((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) <
        ((0xffffffff : UInt32) + align)) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
          [.call 15] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬15 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      15 - store.runtime.currentModule.imports.length]? = some func12Def := by
    rw [hmod]
    rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func12Def, Function.toLocals, Function.numParams,
    ValueType.zero, func12]
  apply TrapsWith.prepend Step.block
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
    (selected := .i32 (if oldBump = 0 then 1054000 else oldBump)) (by
      by_cases h : oldBump = 0 <;> simp [h]))
  apply TrapsWith.prepend Step.add
  apply TrapsWith.prepend (Step.localTee rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.ltU (result := 1) (by simp [hoverflow]))
  apply TrapsWith.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

theorem allocator_size_overflow_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (size align oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ ((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) <
        ((0xffffffff : UInt32) + align))
    (hsize :
      size + (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (0 - align)) <
        (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (0 - align))) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
          [.call 15] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬15 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      15 - store.runtime.currentModule.imports.length]? = some func12Def := by
    rw [hmod]
    rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func12Def, Function.toLocals, Function.numParams,
    ValueType.zero, func12]
  apply TrapsWith.prepend Step.block
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
    (selected := .i32 (if oldBump = 0 then 1054000 else oldBump)) (by
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
  have hsize' :
      size + (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (-align)) <
        (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (-align)) := by
    rw [UInt32.sub_eq_add_neg, UInt32.zero_add] at hsize
    exact hsize
  apply TrapsWith.prepend (Step.ltU (result := 1) (by simp [hsize']))
  apply TrapsWith.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

theorem allocator_signed_limit_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (size align oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ ((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) <
        ((0xffffffff : UInt32) + align))
    (hsecond : ¬
      size + (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (0 - align)) <
        (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (0 - align)))
    (hnegative :
      (size + (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + align)) &&& (0 - align))).toInt32 <
          UInt32.toInt32 0) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
          [.call 15] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬15 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      15 - store.runtime.currentModule.imports.length]? = some func12Def := by
    rw [hmod]
    rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func12Def, Function.toLocals, Function.numParams,
    ValueType.zero, func12]
  apply TrapsWith.prepend Step.block
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
    (selected := .i32 (if oldBump = 0 then 1054000 else oldBump)) (by
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
      size + (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (-align)) <
        (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (-align)) := by
    rw [UInt32.sub_eq_add_neg, UInt32.zero_add] at hsecond
    exact hsecond
  apply TrapsWith.prepend (Step.ltU (result := 0) (by simp [hsecond']))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  have hnegative' :
      (size + (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + align)) &&& (-align))).toInt32 <
          UInt32.toInt32 0 := by
    rw [UInt32.sub_eq_add_neg, UInt32.zero_add] at hnegative
    exact hnegative
  apply TrapsWith.prepend
    (Step.ltS (result := 1) (if_pos hnegative').symm)
  apply TrapsWith.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

theorem allocator_grow_failure_traps
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (size align oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ ((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) <
        ((0xffffffff : UInt32) + align))
    (hsecond : ¬
      size + (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (0 - align)) <
        (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (0 - align)))
    (hnegative : ¬
      (size + (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + align)) &&& (0 - align))).toInt32 <
          UInt32.toInt32 0)
    (hneed : ¬
      ((65535 + (size + (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + align)) &&& (0 - align)))) >>>
          (16 % 32)) ≤ UInt32.ofNat store.wasm.mem.pages)
    (hgrow : store.wasm.mem.grow
        (((65535 + (size +
          (((if oldBump = 0 then 1054000 else oldBump) +
            ((0xffffffff : UInt32) + align)) &&& (0 - align)))) >>>
              (16 % 32)) - UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) = none) :
    TrapsWith
      ⟨.running
        ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
          [.call 15] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  have hnot : ¬15 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      15 - store.runtime.currentModule.imports.length]? = some func12Def := by
    rw [hmod]
    rfl
  apply TrapsWith.prepend (Step.call hnot hfn)
  simp [func12Def, Function.toLocals, Function.numParams,
    ValueType.zero, func12]
  apply TrapsWith.prepend Step.block
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
    (selected := .i32 (if oldBump = 0 then 1054000 else oldBump)) (by
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
      size + (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (-align)) <
        (((if oldBump = 0 then 1054000 else oldBump) +
          ((0xffffffff : UInt32) + align)) &&& (-align)) := by
    rw [UInt32.sub_eq_add_neg, UInt32.zero_add] at hsecond
    exact hsecond
  apply TrapsWith.prepend (Step.ltU (result := 0) (by simp [hsecond']))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.const
  have hnegative' : ¬
      (size + (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + align)) &&& (-align))).toInt32 <
          UInt32.toInt32 0 := by
    rw [UInt32.sub_eq_add_neg, UInt32.zero_add] at hnegative
    exact hnegative
  apply TrapsWith.prepend
    (Step.ltS (result := 0) (if_neg hnegative').symm)
  apply TrapsWith.prepend Step.brIfZero
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
      ((65535 + (size + (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + align)) &&& (-align)))) >>>
          (16 % 32)) ≤ UInt32.ofNat store.wasm.mem.pages := by
    rw [UInt32.sub_eq_add_neg, UInt32.zero_add] at hneed
    exact hneed
  apply TrapsWith.prepend
    (Step.leU (result := 0) (if_neg hneed').symm)
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend (Step.localGet rfl)
  apply TrapsWith.prepend Step.sub
  apply TrapsWith.prepend (Step.memoryGrowFailure hgrow)
  apply TrapsWith.prepend Step.const
  apply TrapsWith.prepend (Step.ne (result := 0) (by simp))
  apply TrapsWith.prepend Step.brIfZero
  apply TrapsWith.prepend (Step.exitControl rfl)
  simp
  exact oom_wrapper_traps store _ _ _ _ _ _ _ _ hmod henv

/-- If the allocator's computed end already lies in the current memory, the
call returns the aligned pointer and updates only the bump word. -/
theorem allocator_no_grow_steps
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
    (hsecond : ¬ allocatorFinish size align oldBump <
      allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish size align oldBump).toInt32 <
      UInt32.toInt32 0)
    (henough : allocatorRequiredPages size align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages) :
    Reaches
        ⟨.running
          ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
            [.call 15] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        ⟨.running
          ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
            code, arity, remainder, controls, calls⟩,
          allocatorBumpStore store (allocatorFinish size align oldBump)⟩ := by
  have hnot : ¬15 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      15 - store.runtime.currentModule.imports.length]? = some func12Def := by
    rw [hmod]
    rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func12Def, Function.toLocals, Function.numParams,
    ValueType.zero, func12]
  apply Reaches.prepend Step.block
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
  have hptr :
      (allocatorBase oldBump + ((0xffffffff : UInt32) + align)) &&&
          (0 - align) = allocatorPtr oldBump align := by
    rfl
  rw [hptr]
  apply Reaches.prepend
    (Step.ltU (result := 0) (if_neg hsecond).symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.ltS (result := 0) (if_neg hnegative).symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shrU
  rw [show (65535 + (size + allocatorPtr oldBump align)) >>> (16 % 32) =
      allocatorRequiredPages size align oldBump by rfl]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.memorySize
  rw [hmod]
  have hm64 : «module».memIs64 = false := rfl
  rw [hm64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.leU (result := 1) (if_pos henough).symm)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend
    (Step.store32 (address := 0) (offset := 1053960) (by simpa using hbound))
  simp only [setMemory_eq, allocatorBumpStore]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.returnFromCallFallthrough rfl)
  simp [allocatorBumpStore]
  exact ⟨[], .refl _⟩

/-- Successful `memory.grow` followed by the allocator's ordinary return. -/
theorem allocator_grow_success_steps
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
    (hsecond : ¬ allocatorFinish size align oldBump <
      allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish size align oldBump).toInt32 <
      UInt32.toInt32 0)
    (hneed : ¬ allocatorRequiredPages size align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages size align oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages))
    (hresult : previousPages.toUInt32 ≠ (0xffffffff : UInt32)) :
    Reaches
        ⟨.running
          ⟨⟨params, localValues, [.i32 align, .i32 size] ++ stack⟩,
            [.call 15] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        ⟨.running
          ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
            code, arity, remainder, controls, calls⟩,
          allocatorBumpStore (allocatorGrownStore store memory)
            (allocatorFinish size align oldBump)⟩ := by
  have hnot : ¬15 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      15 - store.runtime.currentModule.imports.length]? = some func12Def := by
    rw [hmod]
    rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func12Def, Function.toLocals, Function.numParams,
    ValueType.zero, func12]
  apply Reaches.prepend Step.block
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
  have hptr :
      (allocatorBase oldBump + ((0xffffffff : UInt32) + align)) &&&
          (0 - align) = allocatorPtr oldBump align := by
    rfl
  rw [hptr]
  apply Reaches.prepend
    (Step.ltU (result := 0) (if_neg hsecond).symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.ltS (result := 0) (if_neg hnegative).symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shrU
  rw [show (65535 + (size + allocatorPtr oldBump align)) >>> (16 % 32) =
      allocatorRequiredPages size align oldBump by rfl]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.memorySize
  rw [hmod]
  have hm64 : «module».memIs64 = false := rfl
  rw [hm64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.leU (result := 0) (if_neg hneed).symm)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.memoryGrowSuccess hgrow)
  rw [setMemory_eq]
  simp only [allocatorGrownStore]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 1) (if_pos hresult).symm)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend
    (Step.store32 (address := 0) (offset := 1053960)
      (by simpa using hboundGrown))
  simp only [setMemory_eq, allocatorBumpStore]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.returnFromCallFallthrough rfl)
  simp [allocatorBumpStore, allocatorGrownStore]
  exact ⟨[], .refl _⟩

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

end Submission.HexDecodeStdio
