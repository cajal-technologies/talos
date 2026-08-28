import HexDecodeStdio.WriteAllOperational
import HexDecodeStdio.DecodeLoopReturnOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def decodeAfterStatus : Program := decodeAfterCore.drop 1

def decodeCommonConfig (store : MachineStore Universal.State)
    (data a b c d : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 a, .i32 b,
      .i32 c, .i32 d], []⟩, decodeAfterStatus, 0, [], [], []⟩, store⟩

def decodeFinishedStore (store : MachineStore Universal.State) :
    MachineStore Universal.State :=
  { store with wasm := { store.wasm with globals :=
      { globals := store.wasm.globals.globals.set 0
          (.i32 (decodeStack + 48)) } } }

@[simp] theorem writeAllResultStore_output
    (store : MachineStore Universal.State) (sp length : UInt32)
    (bytes : List UInt8) :
    (writeAllResultStore store sp bytes length).wasm.host.stdio.output =
      store.wasm.host.stdio.output ++ bytes := by
  rfl

@[simp] theorem writeAllResultStore_runtime
    (store : MachineStore Universal.State) (sp length : UInt32)
    (bytes : List UInt8) :
    (writeAllResultStore store sp bytes length).runtime = store.runtime := by
  rfl

@[simp] theorem writeAllResultStore_pages
    (store : MachineStore Universal.State) (sp length : UInt32)
    (bytes : List UInt8) :
    (writeAllResultStore store sp bytes length).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

theorem writeAllResultStore_global
    (store : MachineStore Universal.State) (sp length : UInt32)
    (bytes : List UInt8) (old : UInt32)
    (hglobal : globalAt? store 0 = some (.i32 old)) :
    globalAt? (writeAllResultStore store sp bytes length) 0 = some (.i32 sp) := by
  have hzero : 0 < store.wasm.globals.globals.length := by
    apply (getElem?_eq_some_iff.mp (show
      store.wasm.globals.globals[0]? = some (.i32 old) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  simp only [writeAllResultStore, writeAdapterResultStore, writeAllFrameStore,
    universalWriteStore, globalAt?, canonicalGlobalIndex_zero]
  exact List.getElem?_set_eq_of_lt (Value.i32 sp) (by
    simpa only [List.length_set] using hzero)

set_option maxRecDepth 100000 in
theorem decode_after_write_terminates
    (store : MachineStore Universal.State)
    (data a b c d length : UInt32) (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages)
    (houtput : store.wasm.host.stdio.output = bytes) :
    SmallStep.TerminatesWith
      ⟨.running ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 a, .i32 b,
          .i32 c, .i32 d], []⟩, decodeAfterStatus.drop 6,
        0, [], [], []⟩, store⟩
      (fun values final => values = [] ∧
        final.wasm.host.stdio.output = bytes) := by
  let capacity := store.wasm.mem.read32 (decodeStack + 12)
  let pointer := store.wasm.mem.read32 (decodeStack + 16)
  have hzero : 0 < store.wasm.globals.globals.length := by
    apply (getElem?_eq_some_iff.mp (show
      store.wasm.globals.globals[0]? = some (.i32 decodeStack) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  by_cases hcapacity : capacity = 0
  · simp only [decodeAfterStatus, decodeAfterCore, func9, List.drop]
    apply TerminatesWith.prepend Step.block
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend (Step.load32 (by
      change 1048544 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [show store.wasm.mem.read32 (decodeStack + 12) = 0 by
      simpa [capacity] using hcapacity]
    apply TerminatesWith.prepend (Step.localTee rfl)
    apply TerminatesWith.prepend (Step.eqz (result := 1) rfl)
    apply TerminatesWith.prepend
      (Step.brIf (condition := 1) (by decide) rfl)
    simp
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend Step.const
    apply TerminatesWith.prepend Step.add
    apply TerminatesWith.prepend (Step.globalSet (by
      simpa [globalAt?] using hzero))
    rw [setGlobal_zero_eq]
    apply TerminatesWith.prepend Step.finish
    apply TerminatesWith.done
    exact ⟨rfl, houtput⟩
  · simp only [decodeAfterStatus, decodeAfterCore, func9, List.drop]
    apply TerminatesWith.prepend Step.block
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend (Step.load32 (by
      change 1048544 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [show store.wasm.mem.read32 (decodeStack + 12) = capacity by rfl]
    apply TerminatesWith.prepend (Step.localTee rfl)
    apply TerminatesWith.prepend
      (Step.eqz (result := 0) (by simp [hcapacity]))
    apply TerminatesWith.prepend Step.brIfZero
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend (Step.load32 (by
      change 1048548 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [show store.wasm.mem.read32 (decodeStack + 16) = pointer by rfl]
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend Step.const
    have hdealloc := dealloc_noop_reaches store []
      [.i32 decodeStack, .i32 data, .i32 a, .i32 capacity, .i32 c, .i32 d]
      [.i32 1, .i32 capacity, .i32 pointer] [] 0 []
      [{ kind := .block, paramArity := 0, resultArity := 0,
         body := [.localGet 0, .load32 12, .localTee 3, .eqz, .br_if 0,
           .localGet 0, .load32 16, .localGet 3, .const 1, .call 17],
         continuation := [.localGet 0, .const 48, .add, .globalSet 0],
         belowStack := [] }] [] hmod
    apply TerminatesWith.prependReaches (by
      simpa [decodeAfterStatus, decodeAfterCore, decodeAfterRead,
        coreStructuredBody, coreFirstInstruction, func9] using hdealloc)
    apply TerminatesWith.prepend (Step.exitControl rfl)
    simp
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend Step.const
    apply TerminatesWith.prepend Step.add
    apply TerminatesWith.prepend (Step.globalSet (by
      simpa [globalAt?] using hzero))
    rw [setGlobal_zero_eq]
    apply TerminatesWith.prepend Step.finish
    apply TerminatesWith.done
    exact ⟨rfl, houtput⟩

set_option maxRecDepth 100000 in
theorem decode_common_terminates
    (store : MachineStore Universal.State)
    (data a b c d pointer length : UInt32) (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpointer : store.wasm.mem.read32 (decodeStack + 16) = pointer)
    (hlength : store.wasm.mem.read32 (decodeStack + 20) = length)
    (hlen : bytes.length = length.toNat) (hne : bytes ≠ [])
    (hread : store.wasm.mem.readBytes pointer.toNat length.toNat = bytes)
    (hbound : pointer.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536)
    (houtput : store.wasm.host.stdio.output = []) :
    SmallStep.TerminatesWith (decodeCommonConfig store data a b c d)
      (fun values final => values = [] ∧
        final.wasm.host.stdio.output = bytes) := by
  let inputCapacity := store.wasm.mem.read32 (decodeStack + 36)
  by_cases hinputZero : inputCapacity = 0
  · have hprefix : Reaches (decodeCommonConfig store data a b c d)
        ⟨.running ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 a, .i32 0,
            .i32 c, .i32 d], []⟩, decodeAfterStatus.drop 1,
          0, [], [], []⟩, store⟩ := by
      simp only [decodeCommonConfig, decodeAfterStatus, decodeAfterCore,
        func9, List.drop]
      apply Reaches.prepend Step.block
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.load32 (by
        change 1048568 ≤ store.wasm.mem.pages * 65536
        omega))
      rw [show store.wasm.mem.read32 (decodeStack + 36) = 0 by
        simpa [inputCapacity] using hinputZero]
      apply Reaches.prepend (Step.localTee rfl)
      apply Reaches.prepend (Step.eqz (result := 1) rfl)
      apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
      simp
      exact ⟨[], .refl _⟩
    apply TerminatesWith.prependReaches hprefix
    simp only [decodeAfterStatus, decodeAfterCore, func9, List.drop]
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend (Step.load32 (by
      change 1048548 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [hpointer]
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend (Step.load32 (by
      change 1048552 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [hlength]
    have hwrite := write_all_nonempty_reaches store []
      [.i32 decodeStack, .i32 data, .i32 a, .i32 0, .i32 c, .i32 d] []
      (decodeAfterStatus.drop 6) 0 [] [] [] pointer length decodeStack bytes
      hmod henv hglobal hlen hne hread hbound (by
        change 1048528 ≤ store.wasm.mem.pages * 65536
        omega) (by decide) (by bv_decide)
    apply TerminatesWith.prependReaches hwrite
    apply decode_after_write_terminates
      (store := writeAllResultStore store decodeStack bytes length)
      (data := data) (a := a) (b := 0) (c := c) (d := d)
      (length := length) (bytes := bytes)
    · simpa using hmod
    · exact writeAllResultStore_global store decodeStack length bytes
        decodeStack hglobal
    · simpa using hpages
    · simp [writeAllResultStore_output, houtput]
  · have hprefix : Reaches (decodeCommonConfig store data a b c d)
        ⟨.running ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 a,
            .i32 inputCapacity, .i32 c, .i32 d], []⟩,
          decodeAfterStatus.drop 1, 0, [], [], []⟩, store⟩ := by
      simp only [decodeCommonConfig, decodeAfterStatus, decodeAfterCore,
        func9, List.drop]
      apply Reaches.prepend Step.block
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.load32 (by
        change 1048568 ≤ store.wasm.mem.pages * 65536
        omega))
      rw [show store.wasm.mem.read32 (decodeStack + 36) = inputCapacity by rfl]
      apply Reaches.prepend (Step.localTee rfl)
      apply Reaches.prepend (Step.eqz (result := 0) (by simp [hinputZero]))
      apply Reaches.prepend Step.brIfZero
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend Step.const
      have hdealloc := dealloc_noop_reaches store []
        [.i32 decodeStack, .i32 data, .i32 a, .i32 inputCapacity,
          .i32 c, .i32 d] [.i32 1, .i32 inputCapacity, .i32 data] [] 0 []
        [{ kind := .block, paramArity := 0, resultArity := 0,
           body := [.localGet 0, .load32 36, .localTee 3, .eqz, .br_if 0,
             .localGet 1, .localGet 3, .const 1, .call 17],
           continuation := [.localGet 0, .load32 16, .localGet 0,
             .load32 20, .call 11,
             .block 0 0 [.localGet 0, .load32 12, .localTee 3, .eqz,
               .br_if 0, .localGet 0, .load32 16, .localGet 3, .const 1,
               .call 17],
             .localGet 0, .const 48, .add, .globalSet 0],
           belowStack := [] }] [] hmod
      refine hdealloc.trans ?_
      apply Reaches.prepend (Step.exitControl rfl)
      simp [decodeAfterStatus, decodeAfterCore, coreStructuredBody,
        coreFirstInstruction, func9]
      exact ⟨[], .refl _⟩
    apply TerminatesWith.prependReaches hprefix
    simp only [decodeAfterStatus, decodeAfterCore, func9, List.drop]
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend (Step.load32 (by
      change 1048548 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [hpointer]
    apply TerminatesWith.prepend (Step.localGet rfl)
    apply TerminatesWith.prepend (Step.load32 (by
      change 1048552 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [hlength]
    have hwrite := write_all_nonempty_reaches store []
      [.i32 decodeStack, .i32 data, .i32 a, .i32 inputCapacity, .i32 c,
        .i32 d] [] (decodeAfterStatus.drop 6) 0 [] [] [] pointer length
      decodeStack bytes hmod henv hglobal hlen hne hread hbound (by
        change 1048528 ≤ store.wasm.mem.pages * 65536
        omega) (by decide) (by bv_decide)
    apply TerminatesWith.prependReaches hwrite
    apply decode_after_write_terminates
      (store := writeAllResultStore store decodeStack bytes length)
      (data := data) (a := a) (b := inputCapacity) (c := c) (d := d)
      (length := length) (bytes := bytes)
    · simpa using hmod
    · exact writeAllResultStore_global store decodeStack length bytes
        decodeStack hglobal
    · simpa using hpages
    · simp [writeAllResultStore_output, houtput]

end Submission.HexDecodeStdio
