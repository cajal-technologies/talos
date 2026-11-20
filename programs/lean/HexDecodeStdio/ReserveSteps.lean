import HexDecodeStdio.VectorGrowSteps

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio
open Wasm.SmallStep

/-! Operational control flow for module function 5 (`func2Def`), the byte
vector reserve routine used by `read_chunk` and by the decoder's final append.
-/

def reserveRequired (length additional : UInt32) : UInt32 :=
  length + additional

def reserveDoubled (capacity : UInt32) : UInt32 :=
  capacity <<< 1

def reserveCandidate (length additional capacity : UInt32) : UInt32 :=
  if reserveRequired length additional > reserveDoubled capacity then
    reserveRequired length additional
  else reserveDoubled capacity

def reserveNewCapacity (length additional capacity : UInt32) : UInt32 :=
  if reserveCandidate length additional capacity > 8 then
    reserveCandidate length additional capacity
  else 8

def reserveAfterGrow : Program := func2.drop 31

theorem func2_prefix_split :
    func2 =
      [.globalGet 0, .const 16, .sub, .localTee 3, .globalSet 0,
        .block 0 0
          [.localGet 2, .localGet 1, .add, .localTee 1,
            .localGet 2, .geU, .br_if 0,
            .const 0, .const 0, .call 60, .unreachable],
        .localGet 3, .const 4, .add,
        .localGet 0, .load32 0, .localTee 2,
        .localGet 0, .load32 4,
        .localGet 1, .localGet 2, .const 1, .shl, .localTee 2,
        .localGet 1, .localGet 2, .gtU, .select, .localTee 2,
        .const 8, .localGet 2, .const 8, .gtU, .select, .localTee 2,
        .call 7] ++ reserveAfterGrow := by
  rfl

def reserveFrameStore (store : MachineStore Universal.State)
    (frame : UInt32) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with globals :=
      { globals := store.wasm.globals.globals.set 0 (.i32 frame) } } }

@[simp] theorem reserveFrameStore_runtime
    (store : MachineStore Universal.State) (frame : UInt32) :
    (reserveFrameStore store frame).runtime = store.runtime := by
  rfl

theorem reserveFrameStore_global_zero
    (store : MachineStore Universal.State) (frame old : UInt32)
    (hglobal : globalAt? store 0 = some (.i32 old)) :
    globalAt? (reserveFrameStore store frame) 0 = some (.i32 frame) := by
  simp only [globalAt?, canonicalGlobalIndex_zero] at hglobal ⊢
  have hzero : 0 < store.wasm.globals.globals.length :=
    (getElem?_eq_some_iff.mp hglobal).1
  simpa [reserveFrameStore] using
    (List.getElem?_set_eq_of_lt (.i32 frame) hzero)

@[simp] theorem reserveFrameStore_memoryCap
    (store : MachineStore Universal.State) (frame : UInt32)
    (m : Module) (index : Nat) :
    (reserveFrameStore store frame).wasm.memoryCap m index =
      store.wasm.memoryCap m index := by
  rfl

@[simp] theorem reserveFrameStore_mem
    (store : MachineStore Universal.State) (frame : UInt32) :
    (reserveFrameStore store frame).wasm.mem = store.wasm.mem := by
  rfl

def reserveGrowCall
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (vector length additional capacity data sp : UInt32) :
    Config Universal.State :=
  let required := reserveRequired length additional
  let newCapacity := reserveNewCapacity length additional capacity
  let frame := sp - 16
  ⟨.running
    ⟨⟨[.i32 vector, .i32 required, .i32 newCapacity], [.i32 frame],
        [.i32 newCapacity, .i32 data, .i32 capacity, .i32 (frame + 4)]⟩,
      [.call 7] ++ reserveAfterGrow, 0, [], [],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    reserveFrameStore store frame⟩

def reserveVectorStore (store : MachineStore Universal.State)
    (vector data capacity : UInt32) : MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 vector capacity
  { store with wasm := { store.wasm with mem := mem1.write32 (vector + 4) data } }

def reserveFinishStore (store : MachineStore Universal.State)
    (vector data capacity sp : UInt32) : MachineStore Universal.State :=
  let stored := reserveVectorStore store vector data capacity
  { stored with wasm := { stored.wasm with globals :=
      { globals := stored.wasm.globals.globals.set 0 (.i32 sp) } } }

@[simp] theorem growResultOkStore_pages
    (store : MachineStore Universal.State) (out ptr size : UInt32) :
    (growResultOkStore store out ptr size).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

theorem growResultOkStore_read_tag
    (store : MachineStore Universal.State) (out ptr size : UInt32) :
    (growResultOkStore store out ptr size).wasm.mem.read32 out = 0 := by
  simp [growResultOkStore]

theorem growResultOkStore_read_ptr
    (store : MachineStore Universal.State) (out ptr size : UInt32)
    (hnext : (out + 4).toNat = out.toNat + 4) :
    (growResultOkStore store out ptr size).wasm.mem.read32 (out + 4) = ptr := by
  simp only [growResultOkStore]
  rw [Mem.read32_write32_disjoint]
  · exact Mem.read32_write32_same _ _ _
  · right
    omega

end Project.HexDecodeStdio
