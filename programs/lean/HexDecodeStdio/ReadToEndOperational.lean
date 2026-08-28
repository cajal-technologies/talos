import HexDecodeStdio.ReadChunkFull
import HexDecodeStdio.ReadToEnd

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def readToEndFrameStore (store : MachineStore Universal.State)
    (frame : UInt32) : MachineStore Universal.State :=
  let memLen := store.wasm.mem.write32 (frame + 12) 0
  let memVec := memLen.write64 (frame + 4) 4294967296
  { store with wasm := { store.wasm with
      globals := { globals := store.wasm.globals.globals.set 0 (.i32 frame) }
      mem := memVec } }

@[simp] theorem readToEndFrameStore_runtime
    (store : MachineStore Universal.State) (frame : UInt32) :
    (readToEndFrameStore store frame).runtime = store.runtime := by
  rfl

@[simp] theorem readToEndFrameStore_pages
    (store : MachineStore Universal.State) (frame : UInt32) :
    (readToEndFrameStore store frame).wasm.mem.pages = store.wasm.mem.pages := by
  rfl

theorem read_to_end_to_first_chunk
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out sp : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hframe : (sp - 32).toNat + 32 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, .i32 out :: stack⟩,
            [.call 10] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨[.i32 out],
              [.i32 (sp - 32), .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i64 0],
              [.i32 ((sp - 32) + 4), .i32 ((sp - 32) + 31),
                .i32 ((sp - 32) + 16)]⟩,
            [.call 4] ++ readToEndAfterFirstRead, 0, [], [],
            { locals := ⟨outerParams, outerLocalValues, stack⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩
         store := readToEndFrameStore store (sp - 32) } :
        Config Universal.State) := by
  have hnot : ¬10 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      10 - store.runtime.currentModule.imports.length]? = some func7Def := by
    rw [hmod]
    rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp only [func7Def, Function.toLocals, Function.numParams,
    ValueType.zero, func7_first_read_split]
  simp
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simp [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    simpa using (show (sp - 32).toNat + 12 + 4 ≤
      store.wasm.mem.pages * 65536 by omega)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    simpa using (show (sp - 32).toNat + 4 + 8 ≤
      store.wasm.mem.pages * 65536 by omega)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 4 + (sp - 32) = (sp - 32) + 4 by bv_decide,
    show 31 + (sp - 32) = (sp - 32) + 31 by bv_decide,
    show 16 + (sp - 32) = (sp - 32) + 16 by bv_decide]
  simp [readToEndFrameStore, readToEndAfterFirstRead, setMemory_eq]
  exact ⟨[], .refl _⟩

def readToEndFinishedStore (store : MachineStore Universal.State)
    (out frame restore : UInt32) (vectorWord : UInt64)
    (length : UInt32) : MachineStore Universal.State :=
  let memLen := store.wasm.mem.write32 (out + 8) length
  let memVec := memLen.write64 out vectorWord
  { store with wasm := { store.wasm with
      globals := { globals := store.wasm.globals.globals.set 0 (.i32 restore) }
      mem := memVec } }

private def firstInstruction : Program → Instruction
  | instruction :: _ => instruction
  | [] => .unreachable

private def structuredBody : Instruction → Program
  | .block _ _ body _ _ => body
  | .loop _ _ body _ _ => body
  | _ => []

def readToEndOuterBody : Program :=
  structuredBody (firstInstruction readToEndAfterFirstRead)

def readToEndMiddleBody : Program :=
  structuredBody (firstInstruction readToEndOuterBody)

def readToEndInnerBody : Program :=
  structuredBody (firstInstruction readToEndMiddleBody)

def readToEndLoopBody : Program :=
  structuredBody (firstInstruction (readToEndInnerBody.drop 19))

def readToEndIterationOuter : Program :=
  structuredBody (firstInstruction (readToEndLoopBody.drop 4))

def readToEndIteration1 : Program :=
  structuredBody (firstInstruction readToEndIterationOuter)

def readToEndIteration2 : Program :=
  structuredBody (firstInstruction readToEndIteration1)

def readToEndIteration3 : Program :=
  structuredBody (firstInstruction readToEndIteration2)

def readToEndIteration4 : Program :=
  structuredBody (firstInstruction readToEndIteration3)

def readToEndIteration5 : Program :=
  structuredBody (firstInstruction readToEndIteration4)

def readToEndIteration6 : Program :=
  structuredBody (firstInstruction readToEndIteration5)

def readToEndGrowthCheck : Program :=
  structuredBody (firstInstruction readToEndIteration6)

private def blockControl (body continuation : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body, continuation, belowStack := [] }

def readToEndLoopControls : List ControlFrame :=
  [{ kind := .loop, paramArity := 0, resultArity := 0,
      body := readToEndLoopBody,
      continuation := readToEndInnerBody.drop 20, belowStack := [] },
    { kind := .block, paramArity := 0, resultArity := 0,
      body := readToEndInnerBody,
      continuation := readToEndMiddleBody.drop 1, belowStack := [] },
    { kind := .block, paramArity := 0, resultArity := 0,
      body := readToEndMiddleBody,
      continuation := readToEndOuterBody.drop 1, belowStack := [] },
    { kind := .block, paramArity := 0, resultArity := 0,
      body := readToEndOuterBody,
      continuation := readToEndAfterFirstRead.drop 1, belowStack := [] }]

def readToEndDirectControls : List ControlFrame :=
  blockControl readToEndIteration6 (readToEndIteration5.drop 1) ::
  blockControl readToEndIteration5 (readToEndIteration4.drop 1) ::
  blockControl readToEndIteration4 (readToEndIteration3.drop 1) ::
  blockControl readToEndIteration3 (readToEndIteration2.drop 1) ::
  blockControl readToEndIteration2 (readToEndIteration1.drop 1) ::
  blockControl readToEndIteration1 (readToEndIterationOuter.drop 1) ::
  blockControl readToEndIterationOuter (readToEndLoopBody.drop 5) ::
  readToEndLoopControls

def readToEndLoopConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled : UInt32) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndLoopBody, 0, [], readToEndLoopControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndDirectConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled : UInt32) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 data, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndIteration6.drop 1, 0, [], readToEndDirectControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndTarget (chunk capacity length : UInt32) : UInt32 :=
  if chunk < capacity - length then chunk else capacity - length

def readToEndRemaining (chunk capacity length filled : UInt32) : UInt32 :=
  readToEndTarget chunk capacity length - filled

def readToEndDestination (data length filled : UInt32) : UInt32 :=
  filled + (length + data)

def readToEndFillStore (store : MachineStore Universal.State)
    (destination count : UInt32) : MachineStore Universal.State :=
  { store with
    wasm := { store.wasm with
      mem := store.wasm.mem.fill destination.toNat count.toNat (0 : UInt8) } }

def readToEndAfterAdapterConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining : UInt32) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 remaining, .i32 target, .i32 (length + data),
            .i32 (capacity - length), .i32 0, .i32 0,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndIteration6.drop 15, 0, [], readToEndDirectControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndAfterReadSuccessConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count : UInt32) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 count, .i32 target, .i32 (length + data),
            .i32 (capacity - length), .i32 0, .i32 4,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndIterationOuter.drop 1, 0, [],
        blockControl readToEndIterationOuter (readToEndLoopBody.drop 5) ::
          readToEndLoopControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndLengthStore (store : MachineStore Universal.State)
    (frame count length : UInt32) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with
      mem := store.wasm.mem.write32 (frame + 12) (length + count) } }

def readToEndReturnConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count : UInt32) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 (length + count),
            .i32 filled, .i32 count, .i32 target, .i32 (length + data),
            .i32 (capacity - length), .i32 0, .i32 4,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndAfterFirstRead.drop 1, 0, [], [],
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := readToEndLengthStore store frame count length }

def readToEndContinuedLoopConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled previousCount previousTarget
      previousBase previousSpare : UInt32) : Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 previousCount, .i32 previousTarget, .i32 previousBase,
            .i32 previousSpare, .i32 0, .i32 4,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndLoopBody, 0, [], readToEndLoopControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndContinuedDirectConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled previousTarget previousBase
      previousSpare : UInt32) : Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 data, .i32 previousTarget, .i32 previousBase,
            .i32 previousSpare, .i32 0, .i32 4,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndIteration6.drop 1, 0, [], readToEndDirectControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndContinuedAfterAdapterConfig
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining : UInt32) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 remaining, .i32 target, .i32 (length + data),
            .i32 (capacity - length), .i32 0, .i32 4,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndIteration6.drop 15, 0, [], readToEndDirectControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndNewCapacity (capacity : UInt32) : UInt32 :=
  if (32 : UInt32) + capacity > capacity <<< 1 then (32 : UInt32) + capacity
  else capacity <<< 1

def readToEndGrowthControls : List ControlFrame :=
  blockControl readToEndGrowthCheck (readToEndIteration6.drop 1) ::
    readToEndDirectControls

def readToEndGrowCallConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled scratch9 status : UInt32) :
    Config Universal.State :=
  let newCapacity := readToEndNewCapacity capacity
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 data, .i32 newCapacity, .i32 (capacity <<< 1),
            .i32 scratch9, .i32 0, .i32 status,
            .i32 0, .i32 0, .i64 0],
          [.i32 newCapacity, .i32 data, .i32 capacity,
            .i32 (frame + 16)]⟩,
        [.call 7] ++ readToEndGrowthCheck.drop 23, 0, [],
        readToEndGrowthControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndAfterGrowConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled scratch9 status : UInt32) :
    Config Universal.State :=
  let newCapacity := readToEndNewCapacity capacity
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 data, .i32 newCapacity, .i32 (capacity <<< 1),
            .i32 scratch9, .i32 0, .i32 status,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndGrowthCheck.drop 23, 0, [], readToEndGrowthControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndGrownDirectConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled previousTarget previousBase
      scratch9 status : UInt32) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 data, .i32 previousTarget, .i32 previousBase,
            .i32 scratch9, .i32 0, .i32 status,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndIteration6.drop 1, 0, [], readToEndDirectControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndGrownAfterAdapterConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining
      previousBase scratch9 status : UInt32) : Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 out],
          [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
            .i32 remaining, .i32 target, .i32 (length + data),
            .i32 (capacity - length), .i32 0, .i32 status,
            .i32 0, .i32 0, .i64 0], []⟩,
        readToEndIteration6.drop 15, 0, [], readToEndDirectControls,
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls⟩
    store := store }

def readToEndGrowFinishedStore (store : MachineStore Universal.State)
    (frame ptr newCapacity : UInt32) : MachineStore Universal.State :=
  let memData := store.wasm.mem.write32 (frame + 8) ptr
  { store with wasm := { store.wasm with
      mem := memData.write32 (frame + 4) newCapacity } }

/-- A successful nonempty first chunk initializes the direct-read loop. -/
theorem read_to_end_after_first_nonempty_to_loop
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame capacity data length : UInt32)
    (htag : store.wasm.mem.read8 (frame + 16) = 4)
    (hcount : store.wasm.mem.read32 (frame + 20) = length)
    (hlengthNe : length ≠ 0)
    (hcapacity : store.wasm.mem.read32 (frame + 4) = capacity)
    (hdata : store.wasm.mem.read32 (frame + 8) = data)
    (hlength : store.wasm.mem.read32 (frame + 12) = length)
    (htagBound : frame.toNat + 16 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 20 + 4 ≤ store.wasm.mem.pages * 65536)
    (hcapacityBound : frame.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hdataBound : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hlengthBound : frame.toNat + 12 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      ({ expr := .running
          ⟨⟨[.i32 out],
              [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i64 0], []⟩,
            readToEndAfterFirstRead, 0, [], [],
            { locals := ⟨outerParams, outerLocalValues, stack⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩
         store := store } : Config Universal.State)
      (readToEndLoopConfig store outerParams outerLocalValues stack code arity
        remainder controls calls out frame 8192 capacity data length 0) := by
  simp only [readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by simpa using htagBound))
  rw [htag]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 0) (by decide))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcountBound))
  rw [hcount]
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hlengthNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcapacityBound))
  rw [hcapacity]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hlengthBound))
  rw [hlength]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.loop
  simp [readToEndLoopConfig, readToEndLoopControls, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction]
  exact ⟨[], .refl _⟩

/-- A loop iteration whose vector still has spare capacity skips the grow
call and reaches the direct-read phase. -/
theorem read_to_end_loop_skip_growth
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled : UInt32)
    (hlengthNe : length ≠ 0) (hspare : length ≠ capacity)
    (hdata : store.wasm.mem.read32 (frame + 8) = data)
    (hdataBound : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndLoopConfig store outerParams outerLocalValues stack code arity
        remainder controls calls out frame chunk capacity data length filled)
      (readToEndDirectConfig store outerParams outerLocalValues stack code arity
        remainder controls calls out frame chunk capacity data length filled) := by
  simp only [readToEndLoopConfig, readToEndLoopBody, structuredBody,
    firstInstruction, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.or
  apply Reaches.prepend (Step.brIf (condition := length ||| capacity)
    (by simp only [ne_eq, UInt32.or_eq_zero_iff]; aesop) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hdataBound))
  rw [hdata]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ne (result := 1) (by simp [hspare]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [readToEndDirectConfig, readToEndDirectControls, blockControl,
    readToEndIteration6, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndGrowthCheck, readToEndLoopControls,
    readToEndLoopBody, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, structuredBody, firstInstruction,
    readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

/-- The same spare-capacity branch for a loop reached after an earlier
successful read; the four overwritten scratch locals may contain old data. -/
theorem read_to_end_continued_loop_skip_growth
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled previousCount previousTarget
      previousBase previousSpare : UInt32)
    (hlengthNe : length ≠ 0) (hspare : length ≠ capacity)
    (hdata : store.wasm.mem.read32 (frame + 8) = data)
    (hdataBound : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndContinuedLoopConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled previousCount previousTarget previousBase previousSpare)
      (readToEndContinuedDirectConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled previousTarget previousBase previousSpare) := by
  simp only [readToEndContinuedLoopConfig, readToEndLoopBody, structuredBody,
    firstInstruction, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.or
  apply Reaches.prepend (Step.brIf (condition := length ||| capacity)
    (by simp only [ne_eq, UInt32.or_eq_zero_iff]; aesop) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hdataBound))
  rw [hdata]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ne (result := 1) (by simp [hspare]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [readToEndContinuedDirectConfig, readToEndDirectControls, blockControl,
    readToEndIteration6, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndLoopControls, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction, readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

/-- A full vector reaches the byte-vector grow call. -/
theorem read_to_end_loop_to_grow
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled : UInt32)
    (hlengthNe : length ≠ 0) (hfull : length = capacity)
    (hdata : store.wasm.mem.read32 (frame + 8) = data)
    (hdataBound : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndLoopConfig store outerParams outerLocalValues stack code arity
        remainder controls calls out frame chunk capacity data length filled)
      (readToEndGrowCallConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out frame chunk capacity data length
        filled 0 0) := by
  simp only [readToEndLoopConfig, readToEndLoopBody, structuredBody,
    firstInstruction, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.or
  apply Reaches.prepend (Step.brIf (condition := length ||| capacity)
    (by simp only [ne_eq, UInt32.or_eq_zero_iff]; aesop) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hdataBound))
  rw [hdata]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ne (result := 0) (by simp [hfull]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.gtU
    (result := if (32 : UInt32) + capacity > capacity <<< 1 then 1 else 0)
    (by simp))
  apply Reaches.prepend (Step.select
    (selected := .i32 (readToEndNewCapacity capacity)) (by
      by_cases h : (32 : UInt32) + capacity > capacity <<< 1 <;>
        simp [readToEndNewCapacity, h]))
  apply Reaches.prepend (Step.localTee rfl)
  rw [show 16 + frame = frame + 16 by bv_decide]
  simp [readToEndGrowCallConfig, readToEndNewCapacity,
    readToEndGrowthControls, readToEndDirectControls, blockControl,
    readToEndIteration6, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndGrowthCheck, readToEndLoopControls,
    readToEndLoopBody, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, structuredBody, firstInstruction,
    readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

/-- Continued full-vector iterations reach the same byte-vector grow call
while preserving the status scratch word. -/
theorem read_to_end_continued_loop_to_grow
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled previousCount previousTarget
      previousBase previousSpare : UInt32)
    (hlengthNe : length ≠ 0) (hfull : length = capacity)
    (hdata : store.wasm.mem.read32 (frame + 8) = data)
    (hdataBound : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndContinuedLoopConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled previousCount previousTarget previousBase previousSpare)
      (readToEndGrowCallConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out frame chunk capacity data length
        filled previousSpare 4) := by
  simp only [readToEndContinuedLoopConfig, readToEndLoopBody, structuredBody,
    firstInstruction, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.or
  apply Reaches.prepend (Step.brIf (condition := length ||| capacity)
    (by simp only [ne_eq, UInt32.or_eq_zero_iff]; aesop) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hdataBound))
  rw [hdata]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ne (result := 0) (by simp [hfull]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.gtU
    (result := if (32 : UInt32) + capacity > capacity <<< 1 then 1 else 0)
    (by simp))
  apply Reaches.prepend (Step.select
    (selected := .i32 (readToEndNewCapacity capacity)) (by
      by_cases h : (32 : UInt32) + capacity > capacity <<< 1 <;>
        simp [readToEndNewCapacity, h]))
  apply Reaches.prepend (Step.localTee rfl)
  rw [show 16 + frame = frame + 16 by bv_decide]
  simp [readToEndGrowCallConfig, readToEndNewCapacity,
    readToEndGrowthControls, readToEndDirectControls, blockControl,
    readToEndIteration6, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndGrowthCheck, readToEndLoopControls,
    readToEndLoopBody, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, structuredBody, firstInstruction,
    readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

/-- Invoke the byte-vector grow routine, preserving its normal result store
or propagating the distinguished allocator OOM trap. -/
theorem read_to_end_grow_call_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled scratch9 status oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hnonneg : ¬ (readToEndNewCapacity capacity).toInt32 <
      UInt32.toInt32 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hout : (frame + 16).toNat + 12 ≤
      store.wasm.mem.pages * 65536)
    (hsource : data.toNat +
        (reallocatorCopyLen capacity
          (readToEndNewCapacity capacity)).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages
          (readToEndNewCapacity capacity) 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages (readToEndNewCapacity capacity) 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      data.toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
            memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
            memory.pages * 65536) :
    ReachesOrOOM
      (readToEndGrowCallConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out frame chunk capacity data length
        filled scratch9 status)
      (fun final => ∃ allocStore,
        ByteGrowSuccess store capacity data (readToEndNewCapacity capacity)
            oldBump allocStore ∧
        final = readToEndAfterGrowConfig
          (growResultOkStore allocStore (frame + 16)
            (allocatorPtr oldBump 1) (readToEndNewCapacity capacity))
          outerParams outerLocalValues stack code arity remainder controls
          calls out frame chunk capacity data length filled scratch9 status) := by
  have hgrow := byte_grow_call_outcome store
    [.i32 out]
    [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
      .i32 data, .i32 (readToEndNewCapacity capacity),
      .i32 (capacity <<< 1), .i32 scratch9, .i32 0, .i32 status,
      .i32 0, .i32 0, .i64 0]
    [] (readToEndGrowthCheck.drop 23) 0 [] readToEndGrowthControls
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    (frame + 16) capacity data (readToEndNewCapacity capacity) oldBump
    hmod henv hread hbound hpages hnonneg hptr hout hsource hdestination
    hgrownBounds
  rcases hgrow with ⟨allocStore, _hfinish, hsuccess, hreach⟩ | htrap
  · left
    refine ⟨_, ?_, ⟨allocStore, hsuccess, rfl⟩⟩
    have hruntime :
        (growResultOkStore allocStore (frame + 16)
          (allocatorPtr oldBump 1)
          (readToEndNewCapacity capacity)).runtime = store.runtime := by
      calc
        _ = allocStore.runtime := rfl
        _ = store.runtime := hsuccess.runtime_eq
    simpa [readToEndGrowCallConfig, readToEndAfterGrowConfig,
      growResultFinal, hruntime] using hreach
  · exact Or.inr (by
      simpa [readToEndGrowCallConfig] using htrap)

/-- Consume a successful byte-vector grow result, install its pointer and
capacity in the vector descriptor, and rejoin the direct-read phase. -/
theorem read_to_end_after_grow_success
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled scratch9 status ptr : UInt32)
    (htag : store.wasm.mem.read32 (frame + 16) = 0)
    (hptrRead : store.wasm.mem.read32 (frame + 20) = ptr)
    (htagBound : frame.toNat + 16 + 4 ≤ store.wasm.mem.pages * 65536)
    (hptrBound : frame.toNat + 20 + 4 ≤ store.wasm.mem.pages * 65536)
    (hdataBound : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hcapacityBound : frame.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndAfterGrowConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out frame chunk capacity data length
        filled scratch9 status)
      (readToEndGrownDirectConfig
        (readToEndGrowFinishedStore store frame ptr
          (readToEndNewCapacity capacity))
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame chunk (readToEndNewCapacity capacity) ptr length filled
        (readToEndNewCapacity capacity) (capacity <<< 1) scratch9 status) := by
  simp only [readToEndAfterGrowConfig, readToEndGrowthCheck, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using htagBound))
  rw [htag]
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hptrBound))
  rw [hptrRead]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by simpa using hdataBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    simpa [Mem.write32_pages] using hcapacityBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  simp [readToEndGrownDirectConfig, readToEndGrowFinishedStore,
    readToEndGrowthControls, readToEndDirectControls, blockControl,
    readToEndIteration6, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndLoopControls, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction, readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 20000 in
/-- Fill the uninitialized spare range with zeros and perform one universal
host read.  The result configuration is positioned immediately after the
adapter call. -/
theorem read_to_end_direct_read
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining : UInt32)
    (bytes : List UInt8)
    (htarget : readToEndTarget chunk capacity length = target)
    (hremaining : target - filled = remaining)
    (hremainingNe : remaining ≠ 0)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hbytes : bytes = store.wasm.host.stdio.input.take target.toNat)
    (hfillBound : (filled + (length + data)).toNat + remaining.toNat ≤
      store.wasm.mem.pages * 65536)
    (hreadBound : (length + data).toNat + bytes.length ≤
      store.wasm.mem.pages * 65536)
    (hresultBound : (frame + 16).toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndDirectConfig store outerParams outerLocalValues stack code arity
        remainder controls calls out frame chunk capacity data length filled)
      (readToEndAfterAdapterConfig
        (readAdapterResultStore
          (readToEndFillStore store (filled + (length + data)) remaining)
          (frame + 16) (length + data) bytes)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame chunk capacity data length filled target remaining) := by
  simp only [readToEndDirectConfig, readToEndIteration6, structuredBody,
    firstInstruction, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndLoopBody, readToEndInnerBody,
    readToEndMiddleBody, readToEndOuterBody, readToEndAfterFirstRead,
    func7, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU
    (result := if chunk < capacity - length then 1 else 0) (by simp))
  apply Reaches.prepend (Step.select (selected := .i32 target) (by
    rw [← htarget]
    by_cases h : chunk < capacity - length <;>
      simp [readToEndTarget, h]))
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  rw [hremaining]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hremainingNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.memoryFill32 (by simpa using hfillBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  rw [show 16 + frame = frame + 16 by bv_decide,
    show 31 + frame = frame + 31 by bv_decide]
  let filledStore := readToEndFillStore store
    (filled + (length + data)) remaining
  have hfilledPages :
      filledStore.wasm.mem.pages = store.wasm.mem.pages := rfl
  have hadapter := read_adapter_reaches filledStore
    [.i32 out]
    [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
      .i32 remaining, .i32 target, .i32 (length + data),
      .i32 (capacity - length), .i32 0, .i32 0,
      .i32 0, .i32 0, .i64 0]
    [] (readToEndIteration6.drop 15) 0 [] readToEndDirectControls
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    (frame + 16) (frame + 31) (length + data) target bytes
    (by simpa [filledStore, readToEndFillStore] using hmod)
    (by simpa [filledStore, readToEndFillStore] using henv)
    (by simpa [filledStore, readToEndFillStore] using hbytes)
    (by rw [hfilledPages]; exact hreadBound)
    (by rw [hfilledPages]; simpa using
      (show (frame + 16).toNat + 1 ≤ store.wasm.mem.pages * 65536 by omega))
    (by rw [hfilledPages]; exact hresultBound)
  simpa [filledStore, readToEndAfterAdapterConfig,
    readToEndFillStore, readToEndIteration6, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction, readToEndAfterFirstRead,
    func7] using hadapter

set_option maxRecDepth 20000 in
/-- Direct read on a continued iteration; the status scratch word already has
the successful tag from the preceding iteration. -/
theorem read_to_end_continued_direct_read
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining : UInt32)
    (previousTarget previousBase previousSpare : UInt32)
    (bytes : List UInt8)
    (htarget : readToEndTarget chunk capacity length = target)
    (hremaining : target - filled = remaining)
    (hremainingNe : remaining ≠ 0)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hbytes : bytes = store.wasm.host.stdio.input.take target.toNat)
    (hfillBound : (filled + (length + data)).toNat + remaining.toNat ≤
      store.wasm.mem.pages * 65536)
    (hreadBound : (length + data).toNat + bytes.length ≤
      store.wasm.mem.pages * 65536)
    (hresultBound : (frame + 16).toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndContinuedDirectConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled previousTarget previousBase previousSpare)
      (readToEndContinuedAfterAdapterConfig
        (readAdapterResultStore
          (readToEndFillStore store (filled + (length + data)) remaining)
          (frame + 16) (length + data) bytes)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame chunk capacity data length filled target remaining) := by
  simp only [readToEndContinuedDirectConfig, readToEndIteration6,
    structuredBody, firstInstruction, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU
    (result := if chunk < capacity - length then 1 else 0) (by simp))
  apply Reaches.prepend (Step.select (selected := .i32 target) (by
    rw [← htarget]
    by_cases h : chunk < capacity - length <;>
      simp [readToEndTarget, h]))
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  rw [hremaining]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hremainingNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.memoryFill32 (by simpa using hfillBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  rw [show 16 + frame = frame + 16 by bv_decide,
    show 31 + frame = frame + 31 by bv_decide]
  let filledStore := readToEndFillStore store
    (filled + (length + data)) remaining
  have hfilledPages :
      filledStore.wasm.mem.pages = store.wasm.mem.pages := rfl
  have hadapter := read_adapter_reaches filledStore
    [.i32 out]
    [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
      .i32 remaining, .i32 target, .i32 (length + data),
      .i32 (capacity - length), .i32 0, .i32 4,
      .i32 0, .i32 0, .i64 0]
    [] (readToEndIteration6.drop 15) 0 [] readToEndDirectControls
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    (frame + 16) (frame + 31) (length + data) target bytes
    (by simpa [filledStore, readToEndFillStore] using hmod)
    (by simpa [filledStore, readToEndFillStore] using henv)
    (by simpa [filledStore, readToEndFillStore] using hbytes)
    (by rw [hfilledPages]; exact hreadBound)
    (by rw [hfilledPages]; simpa using
      (show (frame + 16).toNat + 1 ≤ store.wasm.mem.pages * 65536 by omega))
    (by rw [hfilledPages]; exact hresultBound)
  simpa [filledStore, readToEndContinuedAfterAdapterConfig,
    readToEndFillStore, readToEndIteration6, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction, readToEndAfterFirstRead,
    func7] using hadapter

set_option maxRecDepth 20000 in
/-- Continued direct read when the initialization range is already complete. -/
theorem read_to_end_continued_direct_read_no_fill
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target : UInt32)
    (previousTarget previousBase previousSpare : UInt32)
    (bytes : List UInt8)
    (htarget : readToEndTarget chunk capacity length = target)
    (hremaining : target - filled = 0)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hbytes : bytes = store.wasm.host.stdio.input.take target.toNat)
    (hreadBound : (length + data).toNat + bytes.length ≤
      store.wasm.mem.pages * 65536)
    (hresultBound : (frame + 16).toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndContinuedDirectConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled previousTarget previousBase previousSpare)
      (readToEndContinuedAfterAdapterConfig
        (readAdapterResultStore store (frame + 16) (length + data) bytes)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame chunk capacity data length filled target 0) := by
  simp only [readToEndContinuedDirectConfig, readToEndIteration6,
    structuredBody, firstInstruction, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU
    (result := if chunk < capacity - length then 1 else 0) (by simp))
  apply Reaches.prepend (Step.select (selected := .i32 target) (by
    rw [← htarget]
    by_cases h : chunk < capacity - length <;>
      simp [readToEndTarget, h]))
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  rw [hremaining]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.eqz (result := 1) (by decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  rw [show 16 + frame = frame + 16 by bv_decide,
    show 31 + frame = frame + 31 by bv_decide]
  have hadapter := read_adapter_reaches store
    [.i32 out]
    [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
      .i32 0, .i32 target, .i32 (length + data),
      .i32 (capacity - length), .i32 0, .i32 4,
      .i32 0, .i32 0, .i64 0]
    [] (readToEndIteration6.drop 15) 0 [] readToEndDirectControls
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    (frame + 16) (frame + 31) (length + data) target bytes
    hmod henv hbytes hreadBound
    (by simpa using
      (show (frame + 16).toNat + 1 ≤ store.wasm.mem.pages * 65536 by omega))
    hresultBound
  simpa [readToEndContinuedAfterAdapterConfig,
    readToEndIteration6, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndLoopBody, readToEndInnerBody,
    readToEndMiddleBody, readToEndOuterBody, structuredBody,
    firstInstruction, readToEndAfterFirstRead, func7] using hadapter

set_option maxRecDepth 20000 in
/-- Direct read after a successful vector growth. -/
theorem read_to_end_grown_direct_read
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining : UInt32)
    (previousTarget previousBase scratch9 status : UInt32)
    (bytes : List UInt8)
    (htarget : readToEndTarget chunk capacity length = target)
    (hremaining : target - filled = remaining)
    (hremainingNe : remaining ≠ 0)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hbytes : bytes = store.wasm.host.stdio.input.take target.toNat)
    (hfillBound : (filled + (length + data)).toNat + remaining.toNat ≤
      store.wasm.mem.pages * 65536)
    (hreadBound : (length + data).toNat + bytes.length ≤
      store.wasm.mem.pages * 65536)
    (hresultBound : (frame + 16).toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndGrownDirectConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out frame chunk capacity data length
        filled previousTarget previousBase scratch9 status)
      (readToEndGrownAfterAdapterConfig
        (readAdapterResultStore
          (readToEndFillStore store (filled + (length + data)) remaining)
          (frame + 16) (length + data) bytes)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame chunk capacity data length filled target remaining previousBase
        scratch9 status) := by
  simp only [readToEndGrownDirectConfig, readToEndIteration6,
    structuredBody, firstInstruction, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU
    (result := if chunk < capacity - length then 1 else 0) (by simp))
  apply Reaches.prepend (Step.select (selected := .i32 target) (by
    rw [← htarget]
    by_cases h : chunk < capacity - length <;>
      simp [readToEndTarget, h]))
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  rw [hremaining]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hremainingNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.memoryFill32 (by simpa using hfillBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  rw [show 16 + frame = frame + 16 by bv_decide,
    show 31 + frame = frame + 31 by bv_decide]
  let filledStore := readToEndFillStore store
    (filled + (length + data)) remaining
  have hfilledPages :
      filledStore.wasm.mem.pages = store.wasm.mem.pages := rfl
  have hadapter := read_adapter_reaches filledStore
    [.i32 out]
    [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
      .i32 remaining, .i32 target, .i32 (length + data),
      .i32 (capacity - length), .i32 0, .i32 status,
      .i32 0, .i32 0, .i64 0]
    [] (readToEndIteration6.drop 15) 0 [] readToEndDirectControls
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    (frame + 16) (frame + 31) (length + data) target bytes
    (by simpa [filledStore, readToEndFillStore] using hmod)
    (by simpa [filledStore, readToEndFillStore] using henv)
    (by simpa [filledStore, readToEndFillStore] using hbytes)
    (by rw [hfilledPages]; exact hreadBound)
    (by rw [hfilledPages]; simpa using
      (show (frame + 16).toNat + 1 ≤ store.wasm.mem.pages * 65536 by omega))
    (by rw [hfilledPages]; exact hresultBound)
  simpa [filledStore, readToEndGrownAfterAdapterConfig,
    readToEndFillStore, readToEndIteration6, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction, readToEndAfterFirstRead,
    func7] using hadapter

/-- The successful `Result` tag returned by the read adapter is classified
and control returns to the common vector-length update tail. -/
theorem read_to_end_after_adapter_success
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining count : UInt32)
    (htag : store.wasm.mem.read8 (frame + 16) = 4)
    (hcount : store.wasm.mem.read32 (frame + 20) = count)
    (hcountLe : count ≤ target)
    (htagBound : frame.toNat + 16 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 20 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndAfterAdapterConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target remaining)
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count) := by
  simp only [readToEndAfterAdapterConfig, readToEndIteration6, structuredBody,
    firstInstruction, readToEndIteration5, readToEndIteration4,
    readToEndIteration3, readToEndIteration2, readToEndIteration1,
    readToEndIterationOuter, readToEndLoopBody, readToEndInnerBody,
    readToEndMiddleBody, readToEndOuterBody, readToEndAfterFirstRead,
    func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by simpa using htagBound))
  rw [htag]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) (by decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcountBound))
  rw [hcount]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.gtU (result := 0) (by simp [hcountLe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.or
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.brTable rfl)
  simp [readToEndAfterReadSuccessConfig, readToEndDirectControls,
    readToEndLoopControls, blockControl, readToEndIterationOuter,
    readToEndLoopBody, readToEndInnerBody, readToEndMiddleBody,
    readToEndOuterBody, structuredBody, firstInstruction,
    readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

/-- Continued iterations classify the adapter result in the same way; the
already-successful status scratch word remains exactly `4`. -/
theorem read_to_end_continued_after_adapter_success
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining count : UInt32)
    (htag : store.wasm.mem.read8 (frame + 16) = 4)
    (hcount : store.wasm.mem.read32 (frame + 20) = count)
    (hcountLe : count ≤ target)
    (htagBound : frame.toNat + 16 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 20 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndContinuedAfterAdapterConfig store outerParams outerLocalValues
        stack code arity remainder controls calls out frame chunk capacity data
        length filled target remaining)
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count) := by
  simp only [readToEndContinuedAfterAdapterConfig, readToEndIteration6,
    structuredBody, firstInstruction, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by simpa using htagBound))
  rw [htag]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) (by decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcountBound))
  rw [hcount]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.gtU (result := 0) (by simp [hcountLe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.or
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.brTable rfl)
  simp [readToEndAfterReadSuccessConfig, readToEndLoopControls,
    blockControl, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction, readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

/-- Classify a successful adapter result after growth. -/
theorem read_to_end_grown_after_adapter_success
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target remaining count : UInt32)
    (previousBase scratch9 status : UInt32)
    (hstatus : (status &&& 4294967040) ||| 4 = 4)
    (htag : store.wasm.mem.read8 (frame + 16) = 4)
    (hcount : store.wasm.mem.read32 (frame + 20) = count)
    (hcountLe : count ≤ target)
    (htagBound : frame.toNat + 16 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 20 + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndGrownAfterAdapterConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target remaining previousBase scratch9 status)
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count) := by
  simp only [readToEndGrownAfterAdapterConfig, readToEndIteration6,
    structuredBody, firstInstruction, readToEndIteration5,
    readToEndIteration4, readToEndIteration3, readToEndIteration2,
    readToEndIteration1, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by simpa using htagBound))
  rw [htag]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) (by decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcountBound))
  rw [hcount]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.gtU (result := 0) (by simp [hcountLe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.or
  rw [hstatus]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.brTable rfl)
  simp [readToEndAfterReadSuccessConfig, readToEndLoopControls,
    blockControl, readToEndIterationOuter, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    structuredBody, firstInstruction, readToEndAfterFirstRead, func7]
  exact ⟨[], .refl _⟩

/-- A zero-byte successful read updates the vector length and exits the loop
to the function's common return suffix. -/
theorem read_to_end_after_read_eof
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count : UInt32)
    (hcount : count = 0)
    (hlengthBound : frame.toNat + 12 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count)
      (readToEndReturnConfig store outerParams outerLocalValues stack code arity
        remainder controls calls out frame chunk capacity data length filled
        target count) := by
  simp only [readToEndAfterReadSuccessConfig, readToEndIterationOuter,
    structuredBody, firstInstruction, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by simpa using hlengthBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 1) (by simp [hcount]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [readToEndReturnConfig, readToEndLengthStore,
    readToEndLoopControls, blockControl, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, structuredBody, firstInstruction, func7]
  exact ⟨[], .refl _⟩

/-- A nonempty read that exhausts the current spare tail restarts the loop
without changing the adaptive chunk size. -/
theorem read_to_end_after_read_spare_lt
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count : UInt32)
    (hcountNe : count ≠ 0)
    (hspareLt : capacity - length < chunk)
    (hlengthBound : frame.toNat + 12 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count)
      (readToEndContinuedLoopConfig
        (readToEndLengthStore store frame count length)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame chunk capacity data (length + count) (target - count)
        count target (length + data) (capacity - length)) := by
  simp only [readToEndAfterReadSuccessConfig, readToEndIterationOuter,
    structuredBody, firstInstruction, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by simpa using hlengthBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU (result := 1) (by simp [hspareLt]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [readToEndContinuedLoopConfig, readToEndLengthStore,
    readToEndLoopControls, blockControl, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, structuredBody, firstInstruction, func7]
  exact ⟨[], .refl _⟩

/-- A short nonempty read restarts the loop with the unread part of the
current target recorded in `filled`. -/
theorem read_to_end_after_read_partial
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count : UInt32)
    (hcountNe : count ≠ 0)
    (hspareNotLt : ¬ capacity - length < chunk)
    (hpartial : target ≠ count)
    (hlengthBound : frame.toNat + 12 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count)
      (readToEndContinuedLoopConfig
        (readToEndLengthStore store frame count length)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame chunk capacity data (length + count) (target - count)
        count target (length + data) (capacity - length)) := by
  simp only [readToEndAfterReadSuccessConfig, readToEndIterationOuter,
    structuredBody, firstInstruction, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by simpa using hlengthBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU (result := 0) (by simp [hspareNotLt]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ne (result := 1) (by simp [hpartial]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [readToEndContinuedLoopConfig, readToEndLengthStore,
    readToEndLoopControls, blockControl, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, structuredBody, firstInstruction, func7]
  exact ⟨[], .refl _⟩

/-- A full target read doubles a nonnegative adaptive chunk size before
restarting the loop. -/
theorem read_to_end_after_read_full_double
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count : UInt32)
    (hcountNe : count ≠ 0)
    (hspareNotLt : ¬ capacity - length < chunk)
    (hfull : target = count)
    (hchunkNonnegative : ¬ chunk.toInt32 < (0 : UInt32).toInt32)
    (hlengthBound : frame.toNat + 12 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count)
      (readToEndContinuedLoopConfig
        (readToEndLengthStore store frame count length)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame (chunk <<< 1) capacity data (length + count)
        (target - count) 0 target (length + data)
        (capacity - length)) := by
  simp only [readToEndAfterReadSuccessConfig, readToEndIterationOuter,
    structuredBody, firstInstruction, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by simpa using hlengthBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU (result := 0) (by simp [hspareNotLt]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ne (result := 0) (by simp [hfull]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ltS (result := 0)
    (if_neg (by simpa using hchunkNonnegative)).symm)
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 1) (by decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [readToEndContinuedLoopConfig, readToEndLengthStore,
    readToEndLoopControls, blockControl, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, structuredBody, firstInstruction, func7]
  exact ⟨[], .refl _⟩

/-- When doubling would cross the signed boundary, the adaptive chunk size
saturates at `UInt32.max`. -/
theorem read_to_end_after_read_full_saturate
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count : UInt32)
    (hcountNe : count ≠ 0)
    (hspareNotLt : ¬ capacity - length < chunk)
    (hfull : target = count)
    (hchunkNegative : chunk.toInt32 < (0 : UInt32).toInt32)
    (hlengthBound : frame.toNat + 12 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (readToEndAfterReadSuccessConfig store outerParams outerLocalValues stack
        code arity remainder controls calls out frame chunk capacity data
        length filled target count)
      (readToEndContinuedLoopConfig
        (readToEndLengthStore store frame count length)
        outerParams outerLocalValues stack code arity remainder controls calls
        out frame 4294967295 capacity data (length + count)
        (target - count) 1 target (length + data)
        (capacity - length)) := by
  simp only [readToEndAfterReadSuccessConfig, readToEndIterationOuter,
    structuredBody, firstInstruction, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by simpa using hlengthBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU (result := 0) (by simp [hspareNotLt]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ne (result := 0) (by simp [hfull]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ltS (result := 1)
    (if_pos (by simpa using hchunkNegative)).symm)
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by decide))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.br rfl)
  simp [readToEndContinuedLoopConfig, readToEndLengthStore,
    readToEndLoopControls, blockControl, readToEndLoopBody,
    readToEndInnerBody, readToEndMiddleBody, readToEndOuterBody,
    readToEndAfterFirstRead, structuredBody, firstInstruction, func7]
  exact ⟨[], .refl _⟩

/-- The common successful return suffix copies the vector descriptor to the
caller result slot, restores the stack pointer, and returns. -/
theorem read_to_end_return
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled target count restore : UInt32)
    (vectorWord : UInt64)
    (hlength : (readToEndLengthStore store frame count length).wasm.mem.read32
      (frame + 12) = length + count)
    (hvector : (readToEndLengthStore store frame count length).wasm.mem.read64
      (frame + 4) = vectorWord)
    (hlengthBound : frame.toNat + 12 + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorBound : frame.toNat + 4 + 8 ≤ store.wasm.mem.pages * 65536)
    (houtLenBound : out.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (houtBound : out.toNat + 8 ≤ store.wasm.mem.pages * 65536)
    (hdisjoint : (out + 8).toNat + 4 ≤ (frame + 4).toNat ∨
      (frame + 4).toNat + 8 ≤ (out + 8).toNat)
    (hglobal : (globalAt? (readToEndLengthStore store frame count length) 0).isSome = true)
    (hrestore : frame + 32 = restore) :
    Reaches
      (readToEndReturnConfig store outerParams outerLocalValues stack code arity
        remainder controls calls out frame chunk capacity data length filled
        target count)
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, stack⟩,
            code, arity, remainder, controls, calls⟩
         store := readToEndFinishedStore
           (readToEndLengthStore store frame count length)
           out frame restore vectorWord (length + count) } :
        Config Universal.State) := by
  simp only [readToEndReturnConfig, readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    simpa [readToEndLengthStore] using hlengthBound))
  rw [hlength]
  apply Reaches.prepend (Step.store32 (by
    simpa [readToEndLengthStore] using houtLenBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load64 rfl (by
    simpa [readToEndLengthStore] using hvectorBound))
  rw [Mem.read64_write32_disjoint _ _ _ _ hdisjoint]
  rw [hvector]
  apply Reaches.prepend (Step.store64 rfl (by
    simpa [readToEndLengthStore] using houtBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 32 + frame = frame + 32 by bv_decide, hrestore]
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?] using hglobal))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough rfl)
  simp [readToEndFinishedStore, readToEndLengthStore, resumeCaller]
  exact ⟨[], .refl _⟩

/-- The EOF branch immediately after the first `read_chunk`: copy the vector
descriptor to the caller's result slot, restore the stack pointer, and return. -/
theorem read_to_end_after_first_eof
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame restore : UInt32) (vectorWord : UInt64) (length : UInt32)
    (htag : store.wasm.mem.read8 (frame + 16) = 4)
    (hcount : store.wasm.mem.read32 (frame + 20) = 0)
    (hlength : store.wasm.mem.read32 (frame + 12) = length)
    (hvector : store.wasm.mem.read64 (frame + 4) = vectorWord)
    (htagBound : frame.toNat + 16 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 20 + 4 ≤ store.wasm.mem.pages * 65536)
    (hlengthBound : frame.toNat + 12 + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorBound : frame.toNat + 4 + 8 ≤ store.wasm.mem.pages * 65536)
    (houtLenBound : out.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (houtBound : out.toNat + 8 ≤ store.wasm.mem.pages * 65536)
    (hdisjoint : (out + 8).toNat + 4 ≤ (frame + 4).toNat ∨
      (frame + 4).toNat + 8 ≤ (out + 8).toNat)
    (hglobal : (globalAt? store 0).isSome = true)
    (hrestore : frame + 32 = restore) :
    Reaches
      ({ expr := .running
          ⟨⟨[.i32 out],
              [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                .i32 0, .i32 0, .i64 0], []⟩,
            readToEndAfterFirstRead, 0, [], [],
            { locals := ⟨outerParams, outerLocalValues, stack⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, stack⟩,
            code, arity, remainder, controls, calls⟩
         store := readToEndFinishedStore store out frame restore vectorWord
           length } : Config Universal.State) := by
  simp only [readToEndAfterFirstRead, func7, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by simpa using htagBound))
  rw [htag]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 0) (by decide))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcountBound))
  rw [hcount]
  apply Reaches.prepend (Step.eqz (result := 1) (by decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hlengthBound))
  rw [hlength]
  apply Reaches.prepend (Step.store32 (by simpa using houtLenBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load64 rfl (by simpa using hvectorBound))
  rw [Mem.read64_write32_disjoint _ _ _ _ hdisjoint]
  rw [hvector]
  apply Reaches.prepend (Step.store64 rfl (by
    simpa using houtBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 32 + frame = frame + 32 by bv_decide, hrestore]
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?] using hglobal))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough rfl)
  simp [readToEndFinishedStore, resumeCaller]
  exact ⟨[], .refl _⟩

end Submission.HexDecodeStdio
