import HexDecodeStdio.HostOperational
import HexDecodeStdio.DecodeCoreOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def writeAllOuterBody : Program :=
  coreStructuredBody (coreFirstInstruction (func8.drop 5))

def writeAllLoopBody : Program :=
  coreStructuredBody (coreFirstInstruction (writeAllOuterBody.drop 3))

def writeAllAfterAdapter : Program := writeAllLoopBody.drop 7

def writeAllOuterControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := writeAllOuterBody, continuation := func8.drop 6,
    belowStack := [] }

def writeAllLoopControl : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := writeAllLoopBody, continuation := writeAllOuterBody.drop 4,
    belowStack := [] }

def writeAllFrameStore (store : MachineStore Universal.State) (sp : UInt32) :
    MachineStore Universal.State :=
  { store with wasm := { store.wasm with globals :=
      { globals := store.wasm.globals.globals.set 0 (.i32 (sp - 16)) } } }

def writeAllResultStore (store : MachineStore Universal.State)
    (sp : UInt32) (bytes : List UInt8) (length : UInt32) :
    MachineStore Universal.State :=
  let written := writeAdapterResultStore (writeAllFrameStore store sp)
    (sp - 16) bytes length
  { written with wasm := { written.wasm with globals :=
      { globals := written.wasm.globals.globals.set 0 (.i32 sp) } } }

set_option maxRecDepth 100000 in
theorem write_all_nonempty_reaches
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (pointer length sp : UInt32) (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hlen : bytes.length = length.toNat) (hne : bytes ≠ [])
    (hread : store.wasm.mem.readBytes pointer.toNat length.toNat = bytes)
    (hwriteBound : pointer.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536)
    (hframe : (sp - 16).toNat + 16 ≤ store.wasm.mem.pages * 65536)
    (hframe4 : ((sp - 16) + 4).toNat = (sp - 16).toNat + 4)
    (hrestore : (sp - 16) + 16 = sp) :
    Reaches
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 length, .i32 pointer] ++ stack⟩,
          [.call 11] ++ code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running
        ⟨⟨outerParams, outerLocalValues, stack⟩,
          code, arity, remainder, controls, calls⟩,
        writeAllResultStore store sp bytes length⟩ := by
  let frame := sp - 16
  let framed := writeAllFrameStore store sp
  have hzero : 0 < store.wasm.globals.globals.length := by
    apply (getElem?_eq_some_iff.mp (show
      store.wasm.globals.globals[0]? = some (.i32 sp) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  have hlength : length ≠ 0 := by
    intro hz
    have hbytesZero : bytes.length = 0 := by simpa [hz] using hlen
    apply hne
    simpa only [List.length_eq_zero_iff] using hbytesZero
  apply Reaches.prepend (Step.call (fn := func8Def)
    (by rw [hmod]; decide) (by rw [hmod]; rfl))
  simp only [func8Def, Function.toLocals, Function.numParams,
    ValueType.zero, func8]
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simpa [globalAt?] using hzero))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by
    have : length ≠ 0 := by
      intro hz
      subst length
      simp at hlen
      exact hne hlen
    simp [this]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.loop
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have hprefix : Reaches
      ⟨.running
        ⟨⟨[.i32 pointer, .i32 length],
            [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0],
            [.i32 length, .i32 pointer, .i32 (15 + frame), .i32 frame]⟩,
          [.call 20] ++ writeAllAfterAdapter, 0, [],
          [writeAllLoopControl, writeAllOuterControl],
          ({ locals := ⟨outerParams, outerLocalValues, stack⟩
             continuation := code
             resultArity := arity
             callerRemainder := remainder
             control := controls
             returningInstance := store.runtime.entry } :: calls)⟩,
        framed⟩
      ⟨.running
        ⟨⟨[.i32 pointer, .i32 length],
            [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
          writeAllAfterAdapter, 0, [],
          [writeAllLoopControl, writeAllOuterControl],
          ({ locals := ⟨outerParams, outerLocalValues, stack⟩
             continuation := code
             resultArity := arity
             callerRemainder := remainder
             control := controls
             returningInstance := store.runtime.entry } :: calls)⟩,
        writeAdapterResultStore framed frame bytes length⟩ := by
    apply write_adapter_reaches framed
      [.i32 pointer, .i32 length]
      [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0] []
      writeAllAfterAdapter 0 [] [writeAllLoopControl, writeAllOuterControl]
      ({ locals := ⟨outerParams, outerLocalValues, stack⟩
         continuation := code
         resultArity := arity
         callerRemainder := remainder
         control := controls
         returningInstance := store.runtime.entry } :: calls)
      frame (15 + frame) pointer length bytes
    · simpa [framed, writeAllFrameStore] using hmod
    · simpa [framed, writeAllFrameStore] using henv
    · exact hlen
    · simpa [framed, writeAllFrameStore] using hread
    · simpa [framed, writeAllFrameStore] using hwriteBound
    · simpa [frame, framed, writeAllFrameStore] using
        (show (sp - 16).toNat + 1 ≤ store.wasm.mem.pages * 65536 by omega)
    · simpa [frame, framed, writeAllFrameStore] using
        (show (sp - 16).toNat + 4 + 4 ≤
          store.wasm.mem.pages * 65536 by omega)
  simp only [writeAllOuterBody, writeAllLoopBody, writeAllAfterAdapter,
    coreStructuredBody, coreFirstInstruction, func8, List.drop] at hprefix ⊢
  refine hprefix.trans ?_
  let written := writeAdapterResultStore framed frame bytes length
  have hwrittenPages : written.wasm.mem.pages = store.wasm.mem.pages := by
    rfl
  have hwrittenTag : written.wasm.mem.read8 frame = 4 := by
    simp only [written, writeAdapterResultStore]
    rw [Submission.HexDecodeStdio.Mem.read8_write32_disjoint_core _
      (frame + 4) frame length (Or.inl (by
        change frame.toNat < (frame + 4).toNat
        simpa only [frame, hframe4] using
          (show (sp - 16).toNat < (sp - 16).toNat + 4 by omega)))]
    simp [Mem.read8, Mem.write8]
  have hwrittenCount : written.wasm.mem.read32 (frame + 4) = length := by
    simp only [written, writeAdapterResultStore]
    exact Mem.read32_write32_same _ _ _
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change frame.toNat + 1 ≤ written.wasm.mem.pages * 65536
    rw [hwrittenPages]
    change (sp - 16).toNat + 1 ≤ store.wasm.mem.pages * 65536
    omega))
  change Reaches
    ⟨.running ⟨⟨_, _,
      [.i32 ((writeAdapterResultStore framed frame bytes length).wasm.mem.read8
        (frame + 0)).toUInt32]⟩, _, _, _, _, _⟩,
      writeAdapterResultStore framed frame bytes length⟩ _
  simp only [UInt32.add_zero, hwrittenTag]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) (by
    change 1 = if (written.wasm.mem.read8 frame).toUInt32 = 4 then 1 else 0
    rw [hwrittenTag]
    decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change frame.toNat + 4 + 4 ≤ written.wasm.mem.pages * 65536
    rw [hwrittenPages]
    change (sp - 16).toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hwrittenCount]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.brIf (condition := length) hlength rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU (result := 0) (by simp))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  simp
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.br rfl)
  simp [writeAllLoopControl, writeAllOuterControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 16 + frame = sp by rw [UInt32.add_comm, hrestore]]
  have hwzero : 0 < written.wasm.globals.globals.length := by
    change 0 < (store.wasm.globals.globals.set 0 (.i32 (sp - 16))).length
    simpa only [List.length_set] using hzero
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?] using hwzero))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough (by
    simp [written, framed, writeAdapterResultStore, writeAllFrameStore]))
  simp [writeAllResultStore, written, framed, writeAllFrameStore,
    writeAdapterResultStore, resumeCaller]
  exact ⟨[], .refl _⟩

end Submission.HexDecodeStdio
