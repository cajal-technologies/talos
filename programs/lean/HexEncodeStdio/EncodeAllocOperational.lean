import HexEncodeStdio.MainOperational
import HexEncodeStdio.ReserveOutcome

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def encodeAllocFrameStore (store : MachineStore Universal.State) :
    MachineStore Universal.State :=
  let memLen := store.wasm.mem.write32 1048524 0
  let memVec := memLen.write64 1048516 4294967296
  { store with wasm := { store.wasm with
      globals := { globals := store.wasm.globals.globals.set 0 (.i32 1048512) }
      mem := memVec } }

def encodeReserveControls : List ControlFrame :=
  [{ kind := .block, paramArity := 0, resultArity := 0,
      body := [.localGet 2, .eqz, .br_if 0, .localGet 3, .const 4, .add,
        .const 0, .localGet 2, .const 1, .shl, .call 5],
      continuation := func6.drop 16, belowStack := [] }]

def encodeMainCalls (store : MachineStore Universal.State)
    (pointer : UInt32) : List CallFrame :=
  [{ locals := ⟨[], [.i32 1048544, .i32 pointer, .i32 0, .i32 0], []⟩
     continuation := func10.drop 18
     resultArity := 0
     callerRemainder := []
     control := []
     returningInstance := store.runtime.entry }]

def encodeReserveConfig (store : MachineStore Universal.State)
    (pointer length : UInt32) : Config Universal.State :=
  { expr := .running
      ⟨⟨[.i32 1048552, .i32 pointer, .i32 length],
          [.i32 1048512, .i32 (pointer + length), .i32 0, .i32 0,
            .i32 0, .i32 0],
          [.i32 (length <<< 1), .i32 0, .i32 1048516]⟩,
        [.call 5], 0, [], encodeReserveControls,
        encodeMainCalls store pointer⟩
    store := encodeAllocFrameStore store }

/-- Enter the encoder and stop at its sole output allocation call. -/
theorem encode_call_to_reserve
    (store : MachineStore Universal.State) (pointer length : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hlengthNe : length ≠ 0)
    (hpages : 17 ≤ store.wasm.mem.pages) :
    Reaches
      ({ expr := .running
          ⟨⟨[], [.i32 1048544, .i32 pointer, .i32 0, .i32 0],
              [.i32 length, .i32 pointer, .i32 1048552]⟩,
            [.call 9] ++ func10.drop 18, 0, [], [], []⟩
         store := store } : Config Universal.State)
      (encodeReserveConfig store pointer length) := by
  have hnot : ¬9 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      9 - store.runtime.currentModule.imports.length]? = some func6Def := by
    rw [hmod]
    rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp only [func6Def, Function.toLocals, Function.numParams, ValueType.zero,
    func6, List.drop]
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simpa [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    exact le_trans (by decide : (1048512 : UInt32).toNat + 12 + 4 ≤
      17 * 65536) (Nat.mul_le_mul_right 65536 hpages)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    exact le_trans (by decide : (1048512 : UInt32).toNat + 4 + 8 ≤
      17 * 65536) (Nat.mul_le_mul_right 65536 hpages)))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hlengthNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  simp [encodeReserveConfig, encodeAllocFrameStore, encodeReserveControls,
    encodeMainCalls, setMemory_eq, UInt32.add_comm]
  exact ⟨[], .refl _⟩

end Project.HexEncodeStdio
