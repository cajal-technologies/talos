import HexEncodeStdio.ReserveOperational
import HexEncodeStdio.ReachOutcome

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- `reserve_call_outcome` packaged in the compositional outcome relation. -/
theorem reserve_call_reachesOrOOM
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (vector length additional capacity data sp oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hsum : reserveRequired length additional ≥ additional)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hdata : store.wasm.mem.read32 (vector + 4) = data)
    (hbump : store.wasm.mem.read32 1053960 = oldBump)
    (hbumpBound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages ≤ 65536)
    (hnonneg : ¬ (reserveNewCapacity length additional capacity).toInt32 <
      UInt32.toInt32 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hframe : (sp - 16).toNat + 16 ≤ store.wasm.mem.pages * 65536)
    (houtNoWrap : ((sp - 16) + 4).toNat = (sp - 16).toNat + 4)
    (houtNext : (((sp - 16) + 4) + 4).toNat =
      ((sp - 16) + 4).toNat + 4)
    (hrestore : (sp - 16) + 16 = sp)
    (hvectorBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorDataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hsource : data.toNat +
        (reallocatorCopyLen capacity
          (reserveNewCapacity length additional capacity)).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages
          (reserveNewCapacity length additional capacity) 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length additional capacity)).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages
              (reserveNewCapacity length additional capacity) 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      data.toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length additional capacity)).toNat ≤
            memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length additional capacity)).toNat ≤
            memory.pages * 65536) :
    ReachesOrOOM
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 additional, .i32 length, .i32 vector] ++ stack⟩,
          [.call 5] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (fun final => ∃ allocStore,
        ByteGrowSuccess (reserveFrameStore store (sp - 16)) capacity data
            (reserveNewCapacity length additional capacity) oldBump allocStore ∧
        final = growResultFinal
          (reserveFinishStore
            (growResultOkStore allocStore ((sp - 16) + 4)
              (allocatorPtr oldBump 1)
              (reserveNewCapacity length additional capacity))
            vector (allocatorPtr oldBump 1)
              (reserveNewCapacity length additional capacity) sp)
          outerParams outerLocalValues stack code arity remainder controls
          calls) := by
  rcases reserve_call_outcome store outerParams outerLocalValues stack code
      arity remainder controls calls vector length additional capacity data sp
      oldBump hmod henv hglobal hsum hcapacity hdata hbump hbumpBound hpages
      hnonneg hptr hframe houtNoWrap houtNext hrestore hvectorBound
      hvectorDataBound hsource hdestination hgrownBounds with
    ⟨allocStore, hsuccess, hreach⟩ | htrap
  · left
    exact ⟨_, hreach, allocStore, hsuccess, rfl⟩
  · exact Or.inr htrap

end Submission.HexDecodeStdio
