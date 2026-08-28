import HexDecodeStdio.HostOperational
import HexDecodeStdio.ReserveOperational
import HexDecodeStdio.DecodeCore
import HexDecodeStdio.Outcome
import HexDecodeStdio.ReserveOutcome

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep
open Wasm.SepLogic

def readChunkFrameStore (store : MachineStore Universal.State)
    (frame : UInt32) : MachineStore Universal.State :=
  let mem32 := store.wasm.mem.write64 (frame + 32) 0
  let mem24 := mem32.write64 (frame + 24) 0
  let mem16 := mem24.write64 (frame + 16) 0
  let mem8 := mem16.write64 (frame + 8) 0
  { store with wasm := { store.wasm with
      globals := { globals := store.wasm.globals.globals.set 0 (.i32 frame) }
      mem := mem8 } }

@[simp] theorem readChunkFrameStore_runtime
    (store : MachineStore Universal.State) (frame : UInt32) :
    (readChunkFrameStore store frame).runtime = store.runtime := by
  rfl

@[simp] theorem readChunkFrameStore_pages
    (store : MachineStore Universal.State) (frame : UInt32) :
    (readChunkFrameStore store frame).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

def readChunkAfterRead : Program := func1.drop 26

def readChunkCallerFrame (outerParams outerLocalValues stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (returningInstance : ModuleInstanceId) :
    CallFrame :=
  { locals := ⟨outerParams, outerLocalValues, stack⟩
    continuation := code
    resultArity := arity
    callerRemainder := remainder
    control := controls
    returningInstance := returningInstance }

def readChunkCalls (outerParams outerLocalValues stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (returningInstance : ModuleInstanceId)
    (calls : List CallFrame) : List CallFrame :=
  readChunkCallerFrame outerParams outerLocalValues stack code arity remainder
    controls returningInstance :: calls

def readChunkAfterReadConfig (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector frame : UInt32) : Config Universal.State :=
  { expr := .running
      { locals := ⟨[.i32 out, .i32 ignored, .i32 vector],
          [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0], []⟩
        code := readChunkAfterRead
        resultArity := 0
        callerRemainder := []
        control := []
        calls := readChunkCalls outerParams outerLocalValues stack code arity
          remainder controls store.runtime.entry calls }
    store := store }

def readChunkCopiedStore (store : MachineStore Universal.State)
    (destination source count : UInt32) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with mem :=
      (store.wasm.mem.copy destination.toNat source.toNat count.toNat) } }

@[simp] theorem readChunkCopiedStore_pages
    (store : MachineStore Universal.State) (destination source count : UInt32) :
    (readChunkCopiedStore store destination source count).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

def readChunkFinishedStore (store : MachineStore Universal.State)
    (out vector count oldLength sp : UInt32) : MachineStore Universal.State :=
  let memOutCount := store.wasm.mem.write32 (out + 4) count
  let memOutTag := memOutCount.write8 out 4
  let memLength := memOutTag.write32 (vector + 8) (count + oldLength)
  { store with wasm := { store.wasm with
      globals := { globals := store.wasm.globals.globals.set 0 (.i32 sp) }
      mem := memLength } }

theorem read_chunk_to_after_read
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector sp : UInt32) (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hbytes : bytes = store.wasm.host.stdio.input.take 32)
    (h8no : ((sp - 48) + 8).toNat = (sp - 48).toNat + 8)
    (h40no : ((sp - 48) + 40).toNat = (sp - 48).toNat + 40)
    (hframe : (sp - 48).toNat + 48 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 vector, .i32 ignored, .i32 out] ++ stack⟩,
            [.call 4] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨[.i32 out, .i32 ignored, .i32 vector],
              [.i32 (sp - 48), .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            readChunkAfterRead, 0, [], [],
            { locals := ⟨outerParams, outerLocalValues, stack⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩
         store := readAdapterResultStore
           (readChunkFrameStore store (sp - 48))
           ((sp - 48) + 40) ((sp - 48) + 8) bytes } :
        Config Universal.State) := by
  have hnot : ¬4 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      4 - store.runtime.currentModule.imports.length]? = some func1Def := by
    rw [hmod]
    rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func1Def, Function.toLocals, Function.numParams, func1]
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simp [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    simpa using (show (sp - 48).toNat + 32 + 8 ≤
      store.wasm.mem.pages * 65536 by omega)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    simpa using (show (sp - 48).toNat + 24 + 8 ≤
      store.wasm.mem.pages * 65536 by omega)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    simpa using (show (sp - 48).toNat + 16 + 8 ≤
      store.wasm.mem.pages * 65536 by omega)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    simpa using (show (sp - 48).toNat + 8 + 8 ≤
      store.wasm.mem.pages * 65536 by omega)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  rw [show 8 + (sp - 48) = (sp - 48) + 8 by bv_decide,
    show 40 + (sp - 48) = (sp - 48) + 40 by bv_decide]
  let framed := readChunkFrameStore store (sp - 48)
  have hframedMod : framed.runtime.currentModule = «module» := by
    simpa [framed] using hmod
  have hframedEnv : framed.runtime.currentHost = Universal.envFor «module» := by
    simpa [framed] using henv
  have hreadBound : ((sp - 48) + 8).toNat + bytes.length ≤
      framed.wasm.mem.pages * 65536 := by
    have hlen : bytes.length ≤ 32 := by
      rw [hbytes, List.length_take]
      omega
    simp only [framed, readChunkFrameStore_pages]
    rw [h8no]
    omega
  have houtBound : ((sp - 48) + 40).toNat + 1 ≤
      framed.wasm.mem.pages * 65536 := by
    simp only [framed, readChunkFrameStore_pages]
    rw [h40no]
    omega
  have hout4Bound : ((sp - 48) + 40).toNat + 4 + 4 ≤
      framed.wasm.mem.pages * 65536 := by
    simp only [framed, readChunkFrameStore_pages]
    rw [h40no]
    omega
  have hadapter := read_adapter_reaches framed
    [.i32 out, .i32 ignored, .i32 vector]
    [.i32 (sp - 48), .i32 0, .i32 0, .i32 0, .i32 0] []
    readChunkAfterRead 0 [] []
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    ((sp - 48) + 40) ignored ((sp - 48) + 8) 32 bytes
    hframedMod hframedEnv (by
      simpa [framed, readChunkFrameStore] using hbytes)
    hreadBound houtBound hout4Bound
  simpa [framed, readChunkFrameStore, readChunkAfterRead, func1,
    ValueType.zero] using hadapter

/-- From the point immediately following the universal read adapter, a
nonempty chunk that fits in the current spare capacity is copied into the
vector and the caller is resumed.  This is deliberately a concrete
small-step lemma: it is the normal sibling of the exact OOM branch used when
the reserve call below cannot grow memory. -/
theorem read_chunk_after_read_fits
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector frame capacity data length count : UInt32)
    (htag : store.wasm.mem.read8 (frame + 40) = 4)
    (hcount : store.wasm.mem.read32 (frame + 44) = count)
    (hcountLt : count < 33)
    (hcountNe : count ≠ 0)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hdata : store.wasm.mem.read32 (vector + 4) = data)
    (hlength : store.wasm.mem.read32 (vector + 8) = length)
    (hfits : count ≤ capacity - length)
    (htagBound : frame.toNat + 40 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 44 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hcapacityBound : vector.toNat + 4 ≤
      store.wasm.mem.pages * 65536)
    (hdataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hlengthBound : vector.toNat + 8 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hsourceBound : (frame + 8).toNat + count.toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestinationBound : (data + length).toNat + count.toNat ≤
      store.wasm.mem.pages * 65536)
    (houtBound : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hglobal : (globalAt? store 0).isSome = true) :
    Reaches
      ({ expr := .running
          ⟨⟨[.i32 out, .i32 ignored, .i32 vector],
              [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            readChunkAfterRead, 0, [], [],
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
         store := readChunkFinishedStore
           (readChunkCopiedStore store (data + length) (frame + 8) count)
           out vector count length (frame + 48) } :
        Config Universal.State) := by
  simp only [readChunkAfterRead, func1, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by simpa using htagBound))
  simp only [htag]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) (by simp))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcountBound))
  simp only [hcount]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.geU (result := 0) (by
    simp only [if_neg (UInt32.not_le.mpr hcountLt)]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcapacityBound))
  simp only [UInt32.add_zero, hcapacity]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hlengthBound))
  simp only [hlength]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.leU (result := 1) (by simp [hfits]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hdataBound))
  simp only [hdata]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  rw [show 8 + frame = frame + 8 by bv_decide,
    show length + data = data + length by bv_decide]
  apply Reaches.prepend (by
    simpa only [setMemory_eq] using
      (Step.memoryCopy32 hdestinationBound hsourceBound))
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    simpa [Mem.copy_pages] using houtBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store8 (by
    simpa [Mem.copy_pages] using (show out.toNat + 1 ≤
      store.wasm.mem.pages * 65536 by omega)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.store32 (by
    change vector.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536
    exact hlengthBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.exitControl rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 48 + frame = frame + 48 by bv_decide]
  apply Reaches.prepend (Step.globalSet (by
    simpa [readChunkCopiedStore, globalAt?] using hglobal))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  simp [readChunkCopiedStore, readChunkFinishedStore, setMemory_eq,
    resumeCaller]
  exact ⟨[], .refl _⟩

/-- EOF suffix of `read_chunk`, starting just after the read adapter. -/
theorem read_chunk_after_read_eof
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector frame capacity length : UInt32)
    (htag : store.wasm.mem.read8 (frame + 40) = 4)
    (hcount : store.wasm.mem.read32 (frame + 44) = 0)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hlength : store.wasm.mem.read32 (vector + 8) = length)
    (htagBound : frame.toNat + 40 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 44 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hcapacityBound : vector.toNat + 4 ≤
      store.wasm.mem.pages * 65536)
    (hlengthBound : vector.toNat + 8 + 4 ≤
      store.wasm.mem.pages * 65536)
    (houtBound : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hglobal : (globalAt? store 0).isSome = true) :
    Reaches
      ({ expr := .running
          ⟨⟨[.i32 out, .i32 ignored, .i32 vector],
              [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            readChunkAfterRead, 0, [], [],
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
         store := readChunkFinishedStore store out vector 0 length
           (frame + 48) } : Config Universal.State) := by
  simp only [readChunkAfterRead, func1, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by simpa using htagBound))
  simp only [htag]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) (by simp))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcountBound))
  simp only [hcount]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.geU (result := 0) (by decide))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hcapacityBound))
  simp only [UInt32.add_zero, hcapacity]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by simpa using hlengthBound))
  simp only [hlength]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.leU (result := 1) (by simp))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 1) (by simp))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by simpa using houtBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store8 (by
    change out.toNat + 1 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.store32 (by
    change vector.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536
    exact hlengthBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.exitControl rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 48 + frame = frame + 48 by bv_decide]
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?] using hglobal))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  simp [readChunkFinishedStore, resumeCaller]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 20000 in
/-- Non-fitting post-read leg.  The call to the vector reserve routine is
split into a successful allocation/reallocation and the exact OOM trap; on
success the chunk is copied and `read_chunk` returns normally. -/
theorem read_chunk_after_read_reserve
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector frame capacity data length count oldBump : UInt32)
    (htag : store.wasm.mem.read8 (frame + 40) = 4)
    (hcount : store.wasm.mem.read32 (frame + 44) = count)
    (hcountLt : count < 33) (hcountNe : count ≠ 0)
    (hnotFits : ¬ count ≤ capacity - length)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hdata : store.wasm.mem.read32 (vector + 4) = data)
    (hlength : store.wasm.mem.read32 (vector + 8) = length)
    (hbump : store.wasm.mem.read32 1053960 = oldBump)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 frame))
    (htagBound : frame.toNat + 40 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 44 + 4 ≤ store.wasm.mem.pages * 65536)
    (hcapacityBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdataBound : vector.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hlengthBound : vector.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hbumpBound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 65536)
    (hsum : reserveRequired length count ≥ count)
    (hnonneg : ¬ (reserveNewCapacity length count capacity).toInt32 <
      UInt32.toInt32 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hreserveFrame : (frame - 16).toNat + 16 ≤
      store.wasm.mem.pages * 65536)
    (hreserveOutNo : ((frame - 16) + 4).toNat =
      (frame - 16).toNat + 4)
    (hreserveOutNext : (((frame - 16) + 4) + 4).toNat =
      ((frame - 16) + 4).toNat + 4)
    (hreserveRestore : (frame - 16) + 16 = frame)
    (hsource : data.toNat +
        (reallocatorCopyLen capacity
          (reserveNewCapacity length count capacity)).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages
          (reserveNewCapacity length count capacity) 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length count capacity)).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages
              (reserveNewCapacity length count capacity) 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      data.toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length count capacity)).toNat ≤
            memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length count capacity)).toNat ≤
            memory.pages * 65536)
    (hsuccessFacts : ∀ allocStore,
      ByteGrowSuccess (reserveFrameStore store (frame - 16)) capacity data
          (reserveNewCapacity length count capacity) oldBump allocStore →
      let reserved := reserveFinishStore
        (growResultOkStore allocStore ((frame - 16) + 4)
          (allocatorPtr oldBump 1)
          (reserveNewCapacity length count capacity))
        vector (allocatorPtr oldBump 1)
          (reserveNewCapacity length count capacity) frame
      reserved.wasm.mem.read32 (vector + 4) = allocatorPtr oldBump 1 ∧
      reserved.wasm.mem.read32 (vector + 8) = length ∧
      (frame + 8).toNat + count.toNat ≤
        reserved.wasm.mem.pages * 65536 ∧
      (allocatorPtr oldBump 1 + length).toNat + count.toNat ≤
        reserved.wasm.mem.pages * 65536 ∧
      out.toNat + 4 + 4 ≤ reserved.wasm.mem.pages * 65536 ∧
      vector.toNat + 4 + 4 ≤ reserved.wasm.mem.pages * 65536 ∧
      vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536 ∧
      (globalAt? reserved 0).isSome = true) :
    ReachesOrOOM
      (readChunkAfterReadConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out ignored vector frame)
      (fun final => ∃ allocStore,
        ByteGrowSuccess (reserveFrameStore store (frame - 16)) capacity data
          (reserveNewCapacity length count capacity) oldBump allocStore ∧
        let reserved := reserveFinishStore
          (growResultOkStore allocStore ((frame - 16) + 4)
            (allocatorPtr oldBump 1)
            (reserveNewCapacity length count capacity))
          vector (allocatorPtr oldBump 1)
            (reserveNewCapacity length count capacity) frame
        final =
          { expr := .running
              ⟨⟨outerParams, outerLocalValues, stack⟩,
                code, arity, remainder, controls, calls⟩
            store := readChunkFinishedStore
              (readChunkCopiedStore reserved
                (allocatorPtr oldBump 1 + length) (frame + 8) count)
              out vector count length (frame + 48) }) := by
  simp only [readChunkAfterReadConfig, readChunkCalls, readChunkCallerFrame,
    readChunkAfterRead, func1, List.drop]
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load8U (by simpa using htagBound))
  simp only [htag]
  apply ReachesOrOOM.prepend (Step.localTee rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend (Step.eq (result := 1) (by simp))
  apply ReachesOrOOM.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 (by simpa using hcountBound))
  simp only [hcount]
  apply ReachesOrOOM.prepend (Step.localTee rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend (Step.geU (result := 0) (by
    simp only [if_neg (UInt32.not_le.mpr hcountLt)]))
  apply ReachesOrOOM.prepend Step.brIfZero
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 (by simpa using hcapacityBound))
  simp only [UInt32.add_zero, hcapacity]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 (by simpa using hlengthBound))
  simp only [hlength]
  apply ReachesOrOOM.prepend (Step.localTee rfl)
  apply ReachesOrOOM.prepend Step.sub
  apply ReachesOrOOM.prepend (Step.leU (result := 0) (by simp [hnotFits]))
  apply ReachesOrOOM.prepend Step.brIfZero
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.bind
    (reserve_call_reachesOrOOM store _ _ _ _ _ _ _ _ vector length count
      capacity data frame oldBump hmod henv hglobal hsum hcapacity hdata hbump
      hbumpBound (Nat.le_of_lt hpages) hnonneg hptr hreserveFrame hreserveOutNo
      hreserveOutNext hreserveRestore hcapacityBound hdataBound hsource
      hdestination hgrownBounds)
  intro middle hmiddle
  rcases hmiddle with ⟨allocStore, _hfinish, hsuccess, rfl⟩
  dsimp only [growResultFinal]
  obtain ⟨hreservedData, hreservedLength, hsourceBound, hdestBound,
    houtBound, hreservedDataBound, hlengthBound, hreservedGlobal⟩ :=
      hsuccessFacts allocStore hsuccess
  let reserved := reserveFinishStore
    (growResultOkStore allocStore ((frame - 16) + 4)
      (allocatorPtr oldBump 1)
      (reserveNewCapacity length count capacity))
    vector (allocatorPtr oldBump 1)
      (reserveNewCapacity length count capacity) frame
  change ReachesOrOOM
    { expr := .running _
      store := reserved } _
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 (by
    change vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hlengthBound))
  rw [hreservedLength]
  apply ReachesOrOOM.prepend (Step.localSet rfl)
  apply ReachesOrOOM.prepend (Step.br rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply ReachesOrOOM.prepend Step.brIfZero
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 (by
    change vector.toNat + 4 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hreservedDataBound))
  rw [hreservedData]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.add
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend Step.add
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  rw [show 8 + frame = frame + 8 by bv_decide,
    show length + allocatorPtr oldBump 1 =
      allocatorPtr oldBump 1 + length by bv_decide]
  apply ReachesOrOOM.prepend (by
    simpa only [setMemory_eq] using
      (Step.memoryCopy32 hdestBound hsourceBound))
  apply ReachesOrOOM.prepend (Step.exitControl rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.store32 (by
    simpa [Mem.copy_pages] using houtBound))
  rw [setMemory_eq]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.const
  have houtOne : out.toNat + 1 ≤ reserved.wasm.mem.pages * 65536 := by
    exact (Nat.le_trans
      (by omega : out.toNat + 1 ≤ out.toNat + 4 + 4) houtBound)
  apply ReachesOrOOM.prepend (Step.store8 (by
    change out.toNat + 1 ≤ reserved.wasm.mem.pages * 65536
    exact houtOne))
  rw [setMemory_eq]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.add
  apply ReachesOrOOM.prepend (Step.store32 (by
    change vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hlengthBound))
  rw [setMemory_eq]
  apply ReachesOrOOM.prepend (Step.exitControl rfl)
  simp
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend Step.add
  rw [show 48 + frame = frame + 48 by bv_decide]
  apply ReachesOrOOM.prepend (Step.globalSet (by
    simpa [reserved, globalAt?] using hreservedGlobal))
  rw [setGlobal_zero_eq]
  apply ReachesOrOOM.prepend (Step.returnFromCallExplicit (by
    have hruntime := hsuccess.runtime_eq
    exact (congrArg (fun runtime => runtime.entry) hruntime).symm))
  apply ReachesOrOOM.refl
  refine ⟨allocStore, hsuccess, ?_⟩
  simp [reserved, readChunkCopiedStore, readChunkFinishedStore,
    resumeCaller]

end Submission.HexDecodeStdio
