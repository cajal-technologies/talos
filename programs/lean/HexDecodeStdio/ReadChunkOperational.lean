import HexDecodeStdio.ReadChunkSteps
import HexDecodeStdio.HostOperational
import HexDecodeStdio.ReserveOperational
import HexDecodeStdio.DecodeCore
import HexDecodeStdio.Outcome
import HexDecodeStdio.ReserveOutcome

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep
open Wasm.SepLogic

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
  apply ReachesOrOOM.prepend (Step.load8U rfl (by simpa using htagBound))
  simp only [htag]
  apply ReachesOrOOM.prepend (Step.localTee rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend (Step.eq (result := 1) (by simp))
  apply ReachesOrOOM.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 rfl (by simpa using hcountBound))
  simp only [hcount]
  apply ReachesOrOOM.prepend (Step.localTee rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend (Step.geU (result := 0) (by
    simp only [ite_eq_right (UInt32.not_le.mpr hcountLt)]))
  apply ReachesOrOOM.prepend Step.brIfZero
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend Step.block
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 rfl (by simpa using hcapacityBound))
  simp only [UInt32.add_zero, hcapacity]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 rfl (by simpa using hlengthBound))
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
  apply ReachesOrOOM.prepend (Step.load32 rfl (by
    change vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hlengthBound))
  rw [hreservedLength]
  apply ReachesOrOOM.prepend (Step.localSet rfl)
  apply ReachesOrOOM.prepend (Step.br rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.eqz (result := 0) (by simp [hcountNe]))
  apply ReachesOrOOM.prepend Step.brIfZero
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.load32 rfl (by
    change vector.toNat + 4 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hreservedDataBound))
  rw [hreservedData]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.add
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend Step.add
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  rw [show 8 + frame = frame + 8 from UInt32.add_comm _ _,
    show length + allocatorPtr oldBump 1 =
      allocatorPtr oldBump 1 + length from UInt32.add_comm _ _]
  apply ReachesOrOOM.prepend (by
    simpa only [setMemory_eq] using
      (Step.memoryCopy32 hdestBound hsourceBound))
  apply ReachesOrOOM.prepend (Step.exitControl rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.store32 rfl (by
    simpa [Mem.copy_pages] using houtBound))
  rw [setMemory_eq]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.const
  have houtOne : out.toNat + 1 ≤ reserved.wasm.mem.pages * 65536 := by
    exact (Nat.le_trans
      (by omega : out.toNat + 1 ≤ out.toNat + 4 + 4) houtBound)
  apply ReachesOrOOM.prepend (Step.store8 rfl (by
    change out.toNat + 1 ≤ reserved.wasm.mem.pages * 65536
    exact houtOne))
  rw [setMemory_eq]
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.add
  apply ReachesOrOOM.prepend (Step.store32 rfl (by
    change vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hlengthBound))
  rw [setMemory_eq]
  apply ReachesOrOOM.prepend (Step.exitControl rfl)
  simp
  apply ReachesOrOOM.prepend (Step.localGet rfl)
  apply ReachesOrOOM.prepend Step.const
  apply ReachesOrOOM.prepend Step.add
  rw [show 48 + frame = frame + 48 from UInt32.add_comm _ _]
  apply ReachesOrOOM.prepend (Step.globalSet (by
    simpa [reserved, globalAt?] using hreservedGlobal))
  rw [setGlobal_zero_eq]
  apply ReachesOrOOM.prepend (Step.returnFromCallExplicit (by
    have hruntime := hsuccess.runtime_eq
    exact (congrArg (fun runtime => runtime.entry) hruntime).symm))
  apply ReachesOrOOM.refl
  refine ⟨allocStore, hsuccess, ?_⟩
  simp [readChunkCopiedStore, readChunkFinishedStore,
    resumeCaller]

end Project.HexDecodeStdio
