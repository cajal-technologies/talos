import HexDecodeStdio.DecodeWrapperStatus
import HexDecodeStdio.DecodeLoopReserveInvariant

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def decodeSuccessBlocks : Program := decodeSuccessAfterAlloc.drop 9
def decodeSuccessOuterBody : Program := firstBlockBody decodeSuccessBlocks
def decodeSuccessMiddleBody : Program := firstBlockBody decodeSuccessOuterBody
def decodeSuccessInnerBody : Program := firstBlockBody decodeSuccessMiddleBody
def decodeSuccessTail : Program := decodeSuccessBlocks.drop 1
def decodeSuccessOuterContinuation : Program := decodeSuccessOuterBody.drop 1
def decodeSuccessMiddleContinuation : Program := decodeSuccessMiddleBody.drop 1
def decodeSuccessAfterReserve : Program := decodeSuccessInnerBody.drop 13

theorem decodeWrapperReserveFacts (length capacity : UInt32)
    (hlower : 8 ≤ length.toNat)
    (hfits : length.toNat ≤ capacity.toNat)
    (hupper : length.toNat + 16 < 2 ^ 31) :
    (reserveRequired 1 length).toNat = length.toNat + 1 ∧
    length.toNat + 1 ≤ (reserveNewCapacity 1 length 8).toNat ∧
    (reserveNewCapacity 1 length 8).toNat < 2 ^ 31 ∧
    reallocatorCopyLen 8 (reserveNewCapacity 1 length 8) = 8 ∧
    (reserveNewCapacity 1 length 8).toNat ≤ capacity.toNat + 8 := by
  have hrequired : ((1 : UInt32) + length).toNat = length.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    · omega
    · norm_num [UInt32.size] at hupper ⊢
      omega
  have hdoubled : ((8 : UInt32) <<< 1).toNat = 16 := by decide
  have hdoubledEq : ((8 : UInt32) <<< 1) = 16 := by decide
  have hnew : (reserveNewCapacity 1 length 8).toNat =
      max (length.toNat + 1) 16 := by
    simp only [reserveNewCapacity, reserveCandidate, reserveRequired,
      reserveDoubled]
    split
    · rename_i hcandidate
      split
      · rename_i _
        have hn := UInt32.lt_iff_toNat_lt.mp hcandidate
        rw [hdoubledEq, hrequired] at hn
        norm_num at hn
        have h16 : (16 : UInt32).toNat = 16 := by decide
        rw [h16] at hn
        rw [hrequired]
        omega
      · rename_i hnotEight
        exfalso
        apply hnotEight
        apply UInt32.lt_iff_toNat_lt.mpr
        rw [hrequired]
        have h8 : (8 : UInt32).toNat = 8 := by decide
        rw [h8]
        omega
    · rename_i hnotRequired
      split
      · rw [hdoubled]
        symm
        apply max_eq_right
        by_contra hno
        apply hnotRequired
        apply UInt32.lt_iff_toNat_lt.mpr
        rw [hrequired, hdoubled]
        omega
      · rename_i hnotEight
        exfalso
        apply hnotEight
        decide
  change (1 + length).toNat = length.toNat + 1 ∧ _
  rw [hrequired, hnew]
  constructor
  · rfl
  constructor
  · exact Nat.le_max_left _ _
  constructor
  · omega
  constructor
  · simp only [reallocatorCopyLen]
    rw [if_neg]
    intro hlt
    have hn := UInt32.lt_iff_toNat_lt.mp hlt
    rw [hnew] at hn
    norm_num at hn ⊢
    have h8 : (8 : UInt32).toNat = 8 := by decide
    rw [h8] at hn
    omega
  · omega

def decodeSuccessOuterControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeSuccessOuterBody, continuation := decodeSuccessTail
    belowStack := [] }

def decodeSuccessMiddleControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeSuccessMiddleBody
    continuation := decodeSuccessOuterContinuation
    belowStack := [] }

def decodeSuccessInnerControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeSuccessInnerBody
    continuation := decodeSuccessMiddleContinuation
    belowStack := [] }

def decodeSuccessCopiedStore (store : MachineStore Universal.State)
    (destination source length : UInt32) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with mem :=
      (store.wasm.mem.copy destination.toNat source.toNat length.toNat) } }

def decodeSuccessLengthStore (store : MachineStore Universal.State)
    (length : UInt32) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with mem :=
      (store.wasm.mem.write32 (decodeStack + 20) length) } }

theorem decode_status_allocated_preserves_output
    (store allocStore : MachineStore Universal.State)
    (source capacity outLen bump : UInt32) (bytes : List UInt8)
    (hbytes : store.wasm.mem.readBytes source.toNat bytes.length = bytes)
    (hlen : outLen.toNat = bytes.length)
    (hfits : outLen.toNat ≤ capacity.toNat)
    (hsource : 1054000 ≤ source.toNat)
    (hend : source.toNat + capacity.toNat = bump.toNat)
    (hsuccess : ByteGrowSuccess
      (reserveFrameStore store (decodeStack - 16)) 0 1 8 bump allocStore) :
    (decodeStatusAllocatedStore allocStore bump).wasm.mem.readBytes
      source.toNat bytes.length = bytes := by
  simp only [decodeStatusAllocatedStore, reserveFinishStore,
    reserveVectorStore, pushGrowOkStore]
  rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  · exact (hsuccess.fresh_preserves_readBytes_disjoint source.toNat
      bytes.length (Or.inr (by omega))).trans (by
        change store.wasm.mem.readBytes source.toNat bytes.length = bytes
        exact hbytes)
  all_goals right
  all_goals apply le_trans (by decide) hsource

set_option maxRecDepth 100000 in
theorem decode_success_after_alloc_to_blocks
    (store : MachineStore Universal.State)
    (data capacity source outLen statusPtr : UInt32)
    (hfacts : DecodeStatusAllocFacts store statusPtr) :
    Reaches
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
              .i32 0, .i32 source], []⟩,
          decodeSuccessAfterAlloc, 0, [],
          [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
            decodeStatusControl1], []⟩, store⟩
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
              .i32 1, .i32 source], []⟩,
          decodeSuccessBlocks, 0, [],
          [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
            decodeStatusControl1], []⟩,
        decodeStatusReadyStore store statusPtr 0⟩ := by
  simp only [decodeSuccessAfterAlloc, decodeSuccessBlocks,
    decodeStatusBody4, decodeStatusBody3, decodeStatusBody2,
    decodeStatusBody1, firstBlockBody, decodeAfterCore, decodeAfterRead,
    func9, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    have hp := hfacts.pages_lower
    change 1048548 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show store.wasm.mem.read32 (decodeStack + 16) =
    store.wasm.mem.read32 (decodeStatusVector + 4) by rfl, hfacts.data]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store8 (address := statusPtr) (offset := 0)
    hfacts.pointer_bound)
  rw [setMemory_eq]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    have hp := hfacts.pages_lower
    change 1048552 ≤ (store.wasm.mem.write8 statusPtr 0).pages * 65536
    change 1048552 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  simp [decodeStatusReadyStore, Locals.set?, Locals.set]
  exact ⟨[], .refl _⟩

def decodeSuccessOutputStore (store : MachineStore Universal.State)
    (destination source length : UInt32) : MachineStore Universal.State :=
  decodeSuccessLengthStore
    (if length = 0 then store
      else decodeSuccessCopiedStore store (1 + destination) source length)
    (length + 1)

set_option maxRecDepth 100000 in
theorem decode_success_small_reaches_common
    (store : MachineStore Universal.State)
    (data capacity source outLen statusPtr : UInt32)
    (hfacts : DecodeStatusAllocFacts store statusPtr)
    (hsmall : outLen.toNat ≤ 7)
    (hfits : outLen.toNat ≤ capacity.toNat)
    (hsource : source.toNat + outLen.toNat ≤ store.wasm.mem.pages * 65536)
    (hdestination : (1 + statusPtr).toNat + outLen.toNat ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
              .i32 1, .i32 source], []⟩,
          decodeSuccessBlocks, 0, [],
          [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
            decodeStatusControl1], []⟩,
        decodeStatusReadyStore store statusPtr 0⟩
      (decodeCommonConfig
        (decodeSuccessOutputStore (decodeStatusReadyStore store statusPtr 0)
          statusPtr source outLen)
        data capacity outLen 1 source) := by
  let ready := decodeStatusReadyStore store statusPtr 0
  let copied := decodeSuccessCopiedStore ready (1 + statusPtr) source outLen
  have hcapacity : ready.wasm.mem.read32 (decodeStack + 12) = 8 := by
    change ((store.wasm.mem.write8 statusPtr 0).write32
      (decodeStack + 20) 1).read32 (decodeStack + 12) = 8
    rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))]
    rw [Mem.read32_write8_disjoint _ _ _ _ (Or.inl (by
      have hp := hfacts.pointer_lower
      change 1048544 ≤ statusPtr.toNat
      omega))]
    exact hfacts.capacity
  have hsmallWord : outLen ≤ (7 : UInt32) := by
    apply UInt32.le_iff_toNat_le.mpr
    simpa using hsmall
  simp only [decodeSuccessBlocks, decodeSuccessOuterBody,
    decodeSuccessMiddleBody, decodeSuccessInnerBody, firstBlockBody,
    decodeSuccessTail, decodeSuccessOuterContinuation,
    decodeSuccessMiddleContinuation, decodeSuccessAfterAlloc,
    decodeStatusBody4, decodeStatusBody3, decodeStatusBody2,
    decodeStatusBody1, decodeAfterCore, decodeAfterRead, func9, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    have hp := hfacts.pages_lower
    change 1048544 ≤ ready.wasm.mem.pages * 65536
    change 1048544 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hcapacity]
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.leU (result := 1) (by
    simpa using hsmallWord))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  by_cases hzero : outLen = 0
  · subst outLen
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.eqz (result := 1) rfl)
    apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
    simp [decodeSuccessOuterControl, decodeSuccessMiddleControl,
      decodeSuccessInnerControl]
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.add
    apply Reaches.prepend (Step.store32 (by
      have hp := hfacts.pages_lower
      change 1048552 ≤ ready.wasm.mem.pages * 65536
      change 1048552 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [setMemory_eq]
    let finished := decodeSuccessLengthStore ready 1
    by_cases hcapZero : capacity = 0
    · apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.eqz (result := 1) (by simp [hcapZero]))
      apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
      change Reaches _ (decodeCommonConfig finished data capacity 0 1 source)
      simp [decodeStatusControl1, decodeStatusControl2, decodeStatusControl3,
        decodeStatusControl4, decodeCommonConfig, decodeSuccessOutputStore,
        finished]
      exact ⟨[], .refl _⟩
    · apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcapZero]))
      apply Reaches.prepend Step.brIfZero
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend Step.const
      have hdealloc := dealloc_noop_reaches finished []
        [.i32 decodeStack, .i32 data, .i32 capacity, .i32 0,
          .i32 1, .i32 source] [.i32 1, .i32 capacity, .i32 source]
        [.br 3] 0 []
        [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
          decodeStatusControl1] [] (by
            simpa [finished, ready, decodeSuccessLengthStore,
              decodeStatusReadyStore] using hfacts.runtime_module)
      refine hdealloc.trans ?_
      apply Reaches.prepend (Step.br rfl)
      change Reaches _ (decodeCommonConfig finished data capacity 0 1 source)
      simp [decodeStatusControl1, decodeStatusControl2, decodeStatusControl3,
        decodeStatusControl4, decodeCommonConfig, decodeSuccessOutputStore,
        finished]
      exact ⟨[], .refl _⟩
  · apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.eqz (result := 0) (by simp [hzero]))
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.exitControl rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.eqz (result := 0) (by simp [hzero]))
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.load32 (by
      have hp := hfacts.pages_lower
      change 1048548 ≤ ready.wasm.mem.pages * 65536
      change 1048548 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [show ready.wasm.mem.read32 (decodeStack + 16) = statusPtr by
      change ((store.wasm.mem.write8 statusPtr 0).write32
        (decodeStack + 20) 1).read32 (decodeStack + 16) = statusPtr
      rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))]
      rw [Mem.read32_write8_disjoint _ _ _ _ (Or.inl (by
        have hp := hfacts.pointer_lower
        have hs : (decodeStack + 16).toNat + 4 = 1048548 := by decide
        rw [hs]
        omega))]
      exact hfacts.data]
    change Reaches
      ⟨.running ⟨⟨_, _, .i32 statusPtr :: _⟩, _, _, _, _, _⟩, ready⟩ _
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.add
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    have hdestination' : (1 + statusPtr).toNat + outLen.toNat ≤
        ready.wasm.mem.pages * 65536 := by
      change (1 + statusPtr).toNat + outLen.toNat ≤
        store.wasm.mem.pages * 65536
      exact hdestination
    have hsource' : source.toNat + outLen.toNat ≤
        ready.wasm.mem.pages * 65536 := by
      change source.toNat + outLen.toNat ≤
        store.wasm.mem.pages * 65536
      exact hsource
    apply Reaches.prepend (Step.memoryCopy32 hdestination' hsource')
    rw [setMemory_eq]
    let finished := decodeSuccessLengthStore copied (outLen + 1)
    apply Reaches.prepend (Step.exitControl rfl)
    simp
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.add
    apply Reaches.prepend (Step.store32 (by
      have hp := hfacts.pages_lower
      change 1048552 ≤ copied.wasm.mem.pages * 65536
      have hpages : copied.wasm.mem.pages = store.wasm.mem.pages := by rfl
      rw [hpages]
      omega))
    rw [setMemory_eq]
    have hcapNe : capacity ≠ 0 := by
      intro hz
      subst capacity
      simp at hfits
      exact hzero (UInt32.toNat_inj.mp hfits)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcapNe]))
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    have hdealloc := dealloc_noop_reaches finished []
      [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
        .i32 1, .i32 source] [.i32 1, .i32 capacity, .i32 source]
      [.br 3] 0 []
      [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
        decodeStatusControl1] [] (by
          simpa [finished, copied, ready, decodeSuccessLengthStore,
            decodeSuccessCopiedStore,
            decodeStatusReadyStore] using hfacts.runtime_module)
    refine hdealloc.trans ?_
    apply Reaches.prepend (Step.br rfl)
    simp [decodeStatusControl1, decodeStatusControl2, decodeStatusControl3,
      decodeStatusControl4, decodeCommonConfig, decodeSuccessOutputStore,
      decodeSuccessLengthStore, finished, copied, decodeSuccessCopiedStore,
      ready, hzero]
    exact ⟨[], .refl _⟩

theorem Mem.readBytes_succ (m : Mem) (off len : Nat) :
    m.readBytes off (len + 1) = m.bytes off :: m.readBytes (off + 1) len := by
  unfold Mem.readBytes
  rw [show len + 1 = 1 + len by omega, List.range_add]
  simp [Nat.add_assoc]

theorem decodeSuccessOutputStore_readBytes
    (store : MachineStore Universal.State)
    (destination source length : UInt32) (bytes : List UInt8)
    (hlength : length.toNat = bytes.length)
    (hnext : (1 + destination).toNat = destination.toNat + 1)
    (hsource : store.wasm.mem.readBytes source.toNat bytes.length = bytes)
    (hstatus : store.wasm.mem.read8 destination = 0)
    (hdestinationLower : 1048552 ≤ destination.toNat) :
    (decodeSuccessOutputStore store destination source length).wasm.mem.readBytes
      destination.toNat (bytes.length + 1) = 0 :: bytes := by
  by_cases hzero : length = 0
  · have hbytes : bytes = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← hlength]
      simp [hzero]
    subst bytes
    simp only [List.length_nil, Nat.zero_add]
    simp only [decodeSuccessOutputStore, hzero, if_true,
      decodeSuccessLengthStore]
    rw [Mem.readBytes_write32_disjoint]
    · simp [Mem.readBytes, Mem.read8] at hstatus ⊢
      exact hstatus
    · right
      change 1048552 ≤ destination.toNat
      exact hdestinationLower
  · simp only [decodeSuccessOutputStore, hzero, if_false,
      decodeSuccessLengthStore, decodeSuccessCopiedStore]
    rw [Mem.readBytes_write32_disjoint]
    · rw [Mem.readBytes_succ, hnext, ← hlength,
        Mem.readBytes_copy_destination, hlength, hsource]
      congr 1
      simp only [Mem.copy, Mem.read8]
      rw [if_neg]
      · exact hstatus
      · omega
    · right
      change 1048552 ≤ destination.toNat
      exact hdestinationLower

set_option maxRecDepth 100000 in
theorem decode_success_large_to_reserve
    (store : MachineStore Universal.State)
    (data capacity source outLen statusPtr : UInt32)
    (hfacts : DecodeStatusAllocFacts store statusPtr)
    (hlarge : 7 < outLen.toNat) :
    Reaches
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
              .i32 1, .i32 source], []⟩,
          decodeSuccessBlocks, 0, [],
          [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
            decodeStatusControl1], []⟩,
        decodeStatusReadyStore store statusPtr 0⟩
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
              .i32 1, .i32 source],
            [.i32 outLen, .i32 1, .i32 (decodeStack + 12)]⟩,
          [.call 5] ++ decodeSuccessAfterReserve, 0, [],
          [decodeSuccessInnerControl, decodeSuccessMiddleControl,
            decodeSuccessOuterControl, decodeStatusControl4,
            decodeStatusControl3, decodeStatusControl2,
            decodeStatusControl1], []⟩,
        decodeStatusReadyStore store statusPtr 0⟩ := by
  let ready := decodeStatusReadyStore store statusPtr 0
  have hcapacity : ready.wasm.mem.read32 (decodeStack + 12) = 8 := by
    change ((store.wasm.mem.write8 statusPtr 0).write32
      (decodeStack + 20) 1).read32 (decodeStack + 12) = 8
    rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))]
    rw [Mem.read32_write8_disjoint _ _ _ _ (Or.inl (by
      have hp := hfacts.pointer_lower
      change 1048544 ≤ statusPtr.toNat
      omega))]
    exact hfacts.capacity
  have hnotSmall : ¬ outLen ≤ (7 : UInt32) := by
    intro h
    have hn := UInt32.le_iff_toNat_le.mp h
    have h7 : (7 : UInt32).toNat = 7 := by decide
    rw [h7] at hn
    omega
  simp only [decodeSuccessBlocks, decodeSuccessOuterBody,
    decodeSuccessMiddleBody, decodeSuccessInnerBody, firstBlockBody,
    decodeSuccessAfterAlloc, decodeStatusBody4, decodeStatusBody3,
    decodeStatusBody2, decodeStatusBody1, decodeAfterCore, decodeAfterRead,
    func9, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    have hp := hfacts.pages_lower
    change 1048544 ≤ ready.wasm.mem.pages * 65536
    change 1048544 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hcapacity]
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.leU (result := 0) (by simpa using hnotSmall))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_success_after_reserve_reaches_common
    (store : MachineStore Universal.State)
    (data capacity source outLen pointer : UInt32)
    (hruntime : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpointer : store.wasm.mem.read32 (decodeStack + 16) = pointer)
    (hlength : store.wasm.mem.read32 (decodeStack + 20) = 1)
    (hnonzero : outLen ≠ 0)
    (hcapNe : capacity ≠ 0)
    (hsource : source.toNat + outLen.toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : (1 + pointer).toNat + outLen.toNat ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      (growResultFinal store []
        [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
          .i32 1, .i32 source] [] decodeSuccessAfterReserve 0 []
        [decodeSuccessInnerControl, decodeSuccessMiddleControl,
          decodeSuccessOuterControl, decodeStatusControl4,
          decodeStatusControl3, decodeStatusControl2,
          decodeStatusControl1] [])
      (decodeCommonConfig
        (decodeSuccessOutputStore store pointer source outLen)
        data capacity outLen 1 source) := by
  let copied := decodeSuccessCopiedStore store (1 + pointer) source outLen
  simp only [growResultFinal, decodeSuccessAfterReserve,
    decodeSuccessInnerBody, decodeSuccessMiddleBody, decodeSuccessOuterBody,
    decodeSuccessBlocks, firstBlockBody, decodeSuccessAfterAlloc,
    decodeStatusBody4, decodeStatusBody3, decodeStatusBody2,
    decodeStatusBody1, decodeAfterCore, decodeAfterRead, func9, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048552 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hlength]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.br rfl)
  simp [decodeSuccessInnerControl, decodeSuccessMiddleControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hnonzero]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048548 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hpointer]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.memoryCopy32 hdestination hsource)
  rw [setMemory_eq]
  let finished := decodeSuccessLengthStore copied (outLen + 1)
  apply Reaches.prepend (Step.exitControl rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.store32 (by
    change 1048552 ≤ copied.wasm.mem.pages * 65536
    change 1048552 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcapNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  have hdealloc := dealloc_noop_reaches finished []
    [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
      .i32 1, .i32 source] [.i32 1, .i32 capacity, .i32 source]
    [.br 3] 0 []
    [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
      decodeStatusControl1] [] (by
        simpa [finished, copied, decodeSuccessLengthStore,
          decodeSuccessCopiedStore] using hruntime)
  refine hdealloc.trans ?_
  apply Reaches.prepend (Step.br rfl)
  simp [decodeStatusControl1, decodeStatusControl2, decodeStatusControl3,
    decodeStatusControl4, decodeCommonConfig, decodeSuccessOutputStore,
    decodeSuccessLengthStore, finished, copied, decodeSuccessCopiedStore,
    hnonzero]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_success_small_wrapper_outcome
    (input bytes : List UInt8) (store : MachineStore Universal.State)
    (data capacity source outLen bump : UInt32)
    (hdecode : decode input = some bytes)
    (htag : store.wasm.mem.read32 decodeResultOut = capacity)
    (hpointer : store.wasm.mem.read32 (decodeResultOut + 4) = source)
    (hlengthField : store.wasm.mem.read32 (decodeResultOut + 8) = outLen)
    (hlength : outLen.toNat = bytes.length)
    (hfits : outLen.toNat ≤ capacity.toNat)
    (hcapacitySigned : capacity.toNat < 2 ^ 31)
    (hsourceBound : source.toNat + outLen.toNat ≤
      store.wasm.mem.pages * 65536)
    (hsourceRead : store.wasm.mem.readBytes source.toNat bytes.length = bytes)
    (hfacts : DecodeCoreStoreFacts store bump)
    (hplacement : bytes = [] ∨
      (1054000 ≤ source.toNat ∧
        source.toNat + capacity.toNat = bump.toNat))
    (hsmall : outLen.toNat ≤ 7) :
    DecodeTerminalOutcome input (decodeAfterCoreConfig store data) := by
  have htagNe : capacity ≠ 2147483648 := by
    intro h
    have hn : capacity.toNat = 2147483648 := by
      simpa using congrArg UInt32.toNat h
    omega
  have hprefix := decode_success_to_status_alloc store data capacity source
    outLen hfacts.pages_lower htag htagNe hpointer hlengthField
  have halloc := decode_status_alloc_reachesOrOOM store
    [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
      .i32 0, .i32 source] decodeSuccessAfterAlloc
    [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
      decodeStatusControl1] bump hfacts
  rcases halloc with ⟨middle, hreach, allocStore, hsuccess, rfl⟩ | htrap
  · left
    let allocated := decodeStatusAllocatedStore allocStore bump
    let statusPtr := allocatorPtr bump 1
    let ready := decodeStatusReadyStore allocated statusPtr 0
    let final := decodeSuccessOutputStore ready statusPtr source outLen
    have ha := decodeStatusAllocatedStore_facts store allocStore bump hfacts
      hsuccess
    have hblocks := decode_success_after_alloc_to_blocks allocated data capacity
      source outLen statusPtr ha
    have hstatusBound : statusPtr.toNat + 8 ≤
        allocated.wasm.mem.pages * 65536 := by
      by_cases hz : bump = 0
      · subst bump
        change (allocatorPtr 0 1).toNat + 8 ≤
          allocStore.wasm.mem.pages * 65536
        have hp : 17 ≤ allocStore.wasm.mem.pages :=
          le_trans hfacts.pages_lower hsuccess.pages_mono
        simp [allocatorPtr, allocatorBase]
        omega
      · change (allocatorPtr bump 1).toNat + 8 ≤
          allocStore.wasm.mem.pages * 65536
        rw [allocatorPtr_one_eq bump hz]
        exact hsuccess.fresh_eight_finish_bound hz (by
          have hb := hfacts.bump_signed
          norm_num [UInt32.size] at hb ⊢
          omega) (by
          change store.wasm.mem.pages < UInt32.size
          have hp := hfacts.pages_upper
          norm_num [UInt32.size]
          omega)
    have hnext : (1 + statusPtr).toNat = statusPtr.toNat + 1 := by
      by_cases hz : bump = 0
      · subst bump
        decide
      · dsimp only [statusPtr]
        rw [allocatorPtr_one_eq bump hz, UInt32.toNat_add]
        simp only [UInt32.toNat_ofNat]
        rw [Nat.mod_eq_of_lt]
        · have hb := hfacts.bump_signed
          norm_num [UInt32.size] at hb ⊢
          omega
        · have hb := hfacts.bump_signed
          norm_num [UInt32.size] at hb ⊢
          omega
    have hsourceAllocated : allocated.wasm.mem.readBytes source.toNat
        bytes.length = bytes := by
      rcases hplacement with rfl | ⟨hsourceLower, hend⟩
      · simp [Mem.readBytes]
      · exact decode_status_allocated_preserves_output store allocStore
          source capacity outLen bump bytes hsourceRead hlength hfits
          hsourceLower hend hsuccess
    have hsourceReady : ready.wasm.mem.readBytes source.toNat bytes.length =
        bytes := by
      rcases hplacement with hnil | ⟨hsourceLower, hend⟩
      · subst bytes
        simp [ready, decodeStatusReadyStore, Mem.readBytes]
      · have hbumpNe : bump ≠ 0 := by
          intro hz
          subst bump
          simp at hend
          omega
        have hsourceBefore : source.toNat + bytes.length ≤ statusPtr.toNat := by
          dsimp only [statusPtr]
          rw [allocatorPtr_one_eq bump hbumpNe, ← hend, ← hlength]
          omega
        simp only [ready, decodeStatusReadyStore]
        rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inr (by
          change 1048552 ≤ source.toNat
          omega))]
        rw [Mem.readBytes_write8_disjoint _ _ _ _ _ (Or.inl hsourceBefore)]
        exact hsourceAllocated
    have hstatusReady : ready.wasm.mem.read8 statusPtr = 0 := by
      simp only [ready, decodeStatusReadyStore]
      rw [Mem.read8_write32_disjoint_core _ _ _ _ (Or.inr (by
        dsimp only [statusPtr]
        have hp := ha.pointer_lower
        change 1048552 ≤ (allocatorPtr bump 1).toNat
        omega))]
      simp [Mem.read8, Mem.write8]
    have hsourceReadyBound : source.toNat + outLen.toNat ≤
        ready.wasm.mem.pages * 65536 := by
      change source.toNat + outLen.toNat ≤ allocStore.wasm.mem.pages * 65536
      exact le_trans hsourceBound (Nat.mul_le_mul_right 65536 (by
        change store.wasm.mem.pages ≤ allocStore.wasm.mem.pages
        exact hsuccess.pages_mono))
    have hdestinationReadyBound : (1 + statusPtr).toNat + outLen.toNat ≤
        ready.wasm.mem.pages * 65536 := by
      change (1 + statusPtr).toNat + outLen.toNat ≤
        allocated.wasm.mem.pages * 65536
      rw [hnext]
      omega
    have hsmallReach := decode_success_small_reaches_common allocated data
      capacity source outLen statusPtr ha hsmall hfits hsourceReadyBound
      hdestinationReadyBound
    have hfinalRead : final.wasm.mem.readBytes statusPtr.toNat
        ((0 :: bytes).length) = 0 :: bytes := by
      apply decodeSuccessOutputStore_readBytes ready statusPtr source outLen
        bytes hlength hnext hsourceReady hstatusReady
      have hp : 1048552 ≤ (allocatorPtr bump 1).toNat :=
        le_trans (by norm_num) ha.pointer_lower
      simpa [statusPtr] using hp
    have hreadyPointer : ready.wasm.mem.read32 (decodeStack + 16) =
        statusPtr := by
      simp only [ready, decodeStatusReadyStore]
      calc
        ((allocated.wasm.mem.write8 statusPtr 0).write32
            (decodeStack + 20) 1).read32 (decodeStack + 16) =
            (allocated.wasm.mem.write8 statusPtr 0).read32
              (decodeStack + 16) :=
          Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))
        _ = allocated.wasm.mem.read32 (decodeStack + 16) :=
          Mem.read32_write8_disjoint _ _ _ _ (Or.inl (by
            have hs : (decodeStack + 16).toNat + 4 = 1048548 := by decide
            rw [hs]
            have hp : 1048548 ≤ (allocatorPtr bump 1).toNat :=
              le_trans (by norm_num) ha.pointer_lower
            simpa [statusPtr] using hp))
        _ = statusPtr := by simpa [statusPtr] using ha.data
    have hcopiedPointer :
        (decodeSuccessCopiedStore ready (1 + statusPtr) source outLen).wasm.mem.read32
          (decodeStack + 16) = statusPtr := by
      simp only [decodeSuccessCopiedStore]
      rw [Mem.read32_copy_before _ _ _ _ _ (by
        rw [hnext]
        have hs : (decodeStack + 16).toNat + 4 = 1048548 := by decide
        rw [hs]
        have hp' : 1048548 ≤ (allocatorPtr bump 1).toNat :=
          le_trans (by norm_num) ha.pointer_lower
        have hp'' : 1048548 ≤ statusPtr.toNat := by
          simpa [statusPtr] using hp'
        omega)]
      exact hreadyPointer
    have hfinalPointer : final.wasm.mem.read32 (decodeStack + 16) = statusPtr := by
      simp only [final, decodeSuccessOutputStore, decodeSuccessLengthStore]
      split
      · rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))]
        exact hreadyPointer
      · rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))]
        exact hcopiedPointer
    have hfinalLength : final.wasm.mem.read32 (decodeStack + 20) =
        outLen + 1 := by
      exact Mem.read32_write32_same _ _ _
    have hresultLength : (0 :: bytes).length = (outLen + 1).toNat := by
      have hout : outLen.toNat + 1 < UInt32.size := by
        norm_num [UInt32.size]
        omega
      simp only [List.length_cons]
      rw [UInt32.toNat_add]
      norm_num only [UInt32.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hout]
      omega
    have hfinalPages : final.wasm.mem.pages = allocated.wasm.mem.pages := by
      simp only [final, decodeSuccessOutputStore, decodeSuccessLengthStore]
      split <;> rfl
    have hfinalBound : statusPtr.toNat + (outLen + 1).toNat ≤
        final.wasm.mem.pages * 65536 := by
      rw [hfinalPages]
      calc
        statusPtr.toNat + (outLen + 1).toNat =
            statusPtr.toNat + (0 :: bytes).length := by rw [hresultLength]
        _ ≤ statusPtr.toNat + 8 := by
          simp only [List.length_cons]
          rw [hlength] at hsmall
          omega
        _ ≤ allocated.wasm.mem.pages * 65536 := hstatusBound
    have hfinalRuntime : final.runtime = allocated.runtime := by
      simp only [final, decodeSuccessOutputStore, decodeSuccessLengthStore,
        ready, decodeStatusReadyStore]
      split <;> rfl
    have hfinalGlobal : globalAt? final 0 = some (.i32 decodeStack) := by
      have hg : final.wasm.globals.globals = allocated.wasm.globals.globals := by
        simp only [final, ready, decodeSuccessOutputStore,
          decodeSuccessLengthStore, decodeSuccessCopiedStore,
          decodeStatusReadyStore]
        split <;> rfl
      simp only [globalAt?, canonicalGlobalIndex_zero] at ha ⊢
      rw [hg]
      exact ha.global_eq
    have hfinalOutput : final.wasm.host.stdio.output = [] := by
      by_cases hz : outLen = 0 <;>
        simpa [final, ready, decodeSuccessOutputStore,
          decodeSuccessLengthStore, decodeSuccessCopiedStore,
          decodeStatusReadyStore, hz] using ha.output_eq
    have hterm := decode_common_terminates final data capacity outLen 1 source
      statusPtr (outLen + 1) (0 :: bytes)
      (by rw [hfinalRuntime]; exact ha.runtime_module)
      (by rw [hfinalRuntime]; exact ha.runtime_host)
      hfinalGlobal
      (by rw [hfinalPages]; exact ha.pages_lower)
      hfinalPointer hfinalLength hresultLength (by simp)
      (by rw [← hresultLength]; exact hfinalRead) hfinalBound hfinalOutput
    apply TerminatesWith.prependReaches (hprefix.trans (hreach.trans
      (hblocks.trans hsmallReach)))
    exact hterm.mono (by
      intro values finalStore hout
      have heven : input.length % 2 = 0 := by
        have hlenInput := decode_some_length input bytes hdecode
        omega
      simpa [decodeOutput, heven, hdecode] using hout)
  · right
    exact TrapsWith.prependReaches hprefix htrap

set_option maxRecDepth 100000 in
theorem decode_success_large_wrapper_outcome
    (input bytes : List UInt8) (store : MachineStore Universal.State)
    (data capacity source outLen bump : UInt32)
    (hdecode : decode input = some bytes)
    (htag : store.wasm.mem.read32 decodeResultOut = capacity)
    (hpointer : store.wasm.mem.read32 (decodeResultOut + 4) = source)
    (hlengthField : store.wasm.mem.read32 (decodeResultOut + 8) = outLen)
    (hlength : outLen.toNat = bytes.length)
    (hfits : outLen.toNat ≤ capacity.toNat)
    (hcapacitySigned : capacity.toNat < 2 ^ 31)
    (hsourceBound : source.toNat + outLen.toNat ≤
      store.wasm.mem.pages * 65536)
    (hsourceRead : store.wasm.mem.readBytes source.toNat bytes.length = bytes)
    (hfacts : DecodeCoreStoreFacts store bump)
    (hplacement : bytes = [] ∨
      (1054000 ≤ source.toNat ∧
        source.toNat + capacity.toNat = bump.toNat))
    (hlarge : 7 < outLen.toNat) :
    DecodeTerminalOutcome input (decodeAfterCoreConfig store data) := by
  have htagNe : capacity ≠ 2147483648 := by
    intro h
    have hn : capacity.toNat = 2147483648 := by
      simpa using congrArg UInt32.toNat h
    omega
  have hprefix := decode_success_to_status_alloc store data capacity source
    outLen hfacts.pages_lower htag htagNe hpointer hlengthField
  have halloc := decode_status_alloc_reachesOrOOM store
    [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
      .i32 0, .i32 source] decodeSuccessAfterAlloc
    [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
      decodeStatusControl1] bump hfacts
  rcases halloc with ⟨middle, hreach, allocStore, hsuccess, rfl⟩ | htrap
  · let allocated := decodeStatusAllocatedStore allocStore bump
    let statusPtr := allocatorPtr bump 1
    let ready := decodeStatusReadyStore allocated statusPtr 0
    have ha := decodeStatusAllocatedStore_facts store allocStore bump hfacts
      hsuccess
    have hblocks := decode_success_after_alloc_to_blocks allocated data capacity
      source outLen statusPtr ha
    have htoReserve := decode_success_large_to_reserve allocated data capacity
      source outLen statusPtr ha hlarge
    have hbytesNe : bytes ≠ [] := by
      intro hz
      rw [hz] at hlength
      simp at hlength
      omega
    rcases hplacement with hnil | ⟨hsourceLower, hend⟩
    · exact (hbytesNe hnil).elim
    have hbumpNe : bump ≠ 0 := by
      intro hz
      subst bump
      simp at hend
      omega
    have hstatusPtr : statusPtr = bump := by
      exact allocatorPtr_one_eq bump hbumpNe
    let statusBump := allocatorFinish 8 1 bump
    have hstatusBumpNat : statusBump.toNat = bump.toNat + 8 := by
      change (allocatorFinish 8 1 bump).toNat = bump.toNat + 8
      rw [allocatorFinish_one_eq_comm 8 bump hbumpNe, UInt32.toNat_add]
      simp only [UInt32.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by
        have hb := hfacts.bump_signed
        norm_num [UInt32.size] at hb ⊢
        omega)]
    have hreserveUpper : outLen.toNat + 16 < 2 ^ 31 := by
      have hb := hfacts.bump_signed
      omega
    obtain ⟨hrequired, hnewLower, hnewSigned, hcopy, hnewUpper⟩ :=
      decodeWrapperReserveFacts outLen capacity (by omega) hfits hreserveUpper
    let newCapacity := reserveNewCapacity 1 outLen 8
    have hnewUpper' : newCapacity.toNat ≤ capacity.toNat + 8 := by
      simpa [newCapacity] using hnewUpper
    have hnewSigned' : newCapacity.toNat < 2 ^ 31 := by
      simpa [newCapacity] using hnewSigned
    have hcopy' : reallocatorCopyLen 8 newCapacity = 8 := by
      simpa [newCapacity] using hcopy
    have hfinishNoWrap :
        65535 + (statusBump.toNat + newCapacity.toNat) < UInt32.size := by
      calc
        65535 + (statusBump.toNat + newCapacity.toNat) ≤
            65535 + (bump.toNat + 8 + (capacity.toNat + 8)) := by
          rw [hstatusBumpNat]
          omega
        _ < UInt32.size := by
          have hb := hfacts.bump_signed
          norm_num [UInt32.size] at hb ⊢
          omega
    have hstatusBumpNe : statusBump ≠ 0 := by
      intro hz
      have hn := congrArg UInt32.toNat hz
      rw [hstatusBumpNat] at hn
      simp at hn
    let newPtr := allocatorPtr statusBump 1
    have hnewPtr : newPtr = statusBump := allocatorPtr_one_eq _ hstatusBumpNe
    have hfinishNat : (allocatorFinish newCapacity 1 statusBump).toNat =
        statusBump.toNat + newCapacity.toNat := by
      rw [allocatorFinish_one_eq_comm newCapacity statusBump hstatusBumpNe,
        UInt32.toNat_add, Nat.mod_eq_of_lt]
      norm_num [UInt32.size] at hfinishNoWrap ⊢
      omega
    have hrequiredPagesNat :
        (allocatorRequiredPages newCapacity 1 statusBump).toNat =
          (65535 + (statusBump.toNat + newCapacity.toNat)) / 65536 := by
      have hadd : ((65535 : UInt32) +
          allocatorFinish newCapacity 1 statusBump).toNat =
          65535 + (statusBump.toNat + newCapacity.toNat) := by
        rw [UInt32.toNat_add, hfinishNat]
        simp only [UInt32.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hfinishNoWrap]
      rw [allocatorRequiredPages, UInt32.toNat_shiftRight, hadd]
      change (65535 + (statusBump.toNat + newCapacity.toNat)) >>> 16 = _
      rw [Nat.shiftRight_eq_div_pow]
    have hstatusBound : statusPtr.toNat + 8 ≤
        ready.wasm.mem.pages * 65536 := by
      change statusPtr.toNat + 8 ≤ allocated.wasm.mem.pages * 65536
      rw [hstatusPtr]
      exact hsuccess.fresh_eight_finish_bound hbumpNe (by
        have hb := hfacts.bump_signed
        norm_num [UInt32.size] at hb ⊢
        omega) (by
        change store.wasm.mem.pages < UInt32.size
        have hp := hfacts.pages_upper
        norm_num [UInt32.size]
        omega)
    have hsourceReady : ready.wasm.mem.readBytes source.toNat bytes.length =
        bytes := by
      have hsourceAllocated := decode_status_allocated_preserves_output store
        allocStore source capacity outLen bump bytes hsourceRead hlength hfits
        hsourceLower hend hsuccess
      simp only [ready, decodeStatusReadyStore]
      rw [Mem.readBytes_write32_disjoint _ _ _ _ _ (Or.inr (by
        have hs : (decodeStack + 20).toNat + 4 ≤ 1054000 := by decide
        exact hs.trans hsourceLower))]
      rw [Mem.readBytes_write8_disjoint _ _ _ _ _ (Or.inl (by
        change source.toNat + bytes.length ≤ (allocatorPtr bump 1).toNat
        rw [allocatorPtr_one_eq bump hbumpNe, ← hend, ← hlength]
        omega))]
      exact hsourceAllocated
    have hstatusReady : ready.wasm.mem.read8 statusPtr = 0 := by
      simp only [ready, decodeStatusReadyStore]
      rw [Mem.read8_write32_disjoint_core _ _ _ _ (Or.inr (by
        have hp := ha.pointer_lower
        have hp' : 1048552 ≤ statusPtr.toNat := by
          simpa [statusPtr] using le_trans (by norm_num) hp
        exact hp'))]
      simp [Mem.read8, Mem.write8]
    have hreadyBump : ready.wasm.mem.read32 1053960 = statusBump := by
      have hallocBump : allocStore.wasm.mem.read32 1053960 = statusBump := by
        simpa [statusBump] using hsuccess.read_bump (by
          rw [allocatorPtr_one_eq bump hbumpNe]
          omega)
      simp only [ready, decodeStatusReadyStore, allocated,
        decodeStatusAllocatedStore, reserveFinishStore, reserveVectorStore,
        pushGrowOkStore]
      rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inr (by decide)),
        Mem.read32_write8_disjoint _ _ _ _ (Or.inl (by
          change 1053964 ≤ (allocatorPtr bump 1).toNat
          rw [allocatorPtr_one_eq bump hbumpNe]
          omega)),
        Mem.read32_write32_disjoint _ _ _ _ (Or.inr (by decide)),
        Mem.read32_write32_disjoint _ _ _ _ (Or.inr (by decide)),
        Mem.read32_write32_disjoint _ _ _ _ (Or.inr (by decide)),
        Mem.read32_write32_disjoint _ _ _ _ (Or.inr (by decide)),
        Mem.read32_write32_disjoint _ _ _ _ (Or.inr (by decide))]
      exact hallocBump
    have hreadyGlobal : globalAt? ready 0 = some (.i32 decodeStack) := by
      change globalAt? allocated 0 = some (.i32 decodeStack)
      exact ha.global_eq
    have hreadyCapacity : ready.wasm.mem.read32 (decodeStack + 12) = 8 := by
      change ((allocated.wasm.mem.write8 statusPtr 0).write32
        (decodeStack + 20) 1).read32 (decodeStack + 12) = 8
      rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide)),
        Mem.read32_write8_disjoint _ _ _ _ (Or.inl (by
          have hp := ha.pointer_lower
          have hp' : 1048544 ≤ statusPtr.toNat := by
            simpa [statusPtr] using le_trans (by norm_num) hp
          exact hp'))]
      exact ha.capacity
    have hreadyData : ready.wasm.mem.read32 (decodeStack + 16) = statusPtr := by
      simp only [ready, decodeStatusReadyStore]
      rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide)),
        Mem.read32_write8_disjoint _ _ _ _ (Or.inl (by
          have hp := ha.pointer_lower
          have hp' : 1048548 ≤ statusPtr.toNat := by
            simpa [statusPtr] using le_trans (by norm_num) hp
          exact hp'))]
      exact ha.data
    have hfinishIf (hrequiredLe :
        allocatorRequiredPages newCapacity 1 statusBump ≤
          UInt32.ofNat ready.wasm.mem.pages) :
        (allocatorFinish newCapacity 1 statusBump).toNat ≤
          ready.wasm.mem.pages * 65536 := by
      have hn := UInt32.le_iff_toNat_le.mp hrequiredLe
      have hpagesSmall : ready.wasm.mem.pages < UInt32.size := by
        have hp : ready.wasm.mem.pages ≤ 65536 := by
          change allocated.wasm.mem.pages ≤ 65536
          exact ha.pages_upper
        norm_num [UInt32.size]
        omega
      rw [UInt32.toNat_ofNat_of_lt' hpagesSmall, hrequiredPagesNat] at hn
      exact ceil_pages_bound (by rw [hfinishNat]; exact hn)
    have hdestination (hrequiredLe :
        allocatorRequiredPages newCapacity 1 statusBump ≤
          UInt32.ofNat ready.wasm.mem.pages) :
        newPtr.toNat + (reallocatorCopyLen 8 newCapacity).toNat ≤
          ready.wasm.mem.pages * 65536 := by
      have hn := UInt32.le_iff_toNat_le.mp hrequiredLe
      have hpagesSmall : ready.wasm.mem.pages < UInt32.size := by
        have hp : ready.wasm.mem.pages ≤ 65536 := by
          change allocated.wasm.mem.pages ≤ 65536
          exact ha.pages_upper
        norm_num [UInt32.size]
        omega
      rw [UInt32.toNat_ofNat_of_lt' hpagesSmall, hrequiredPagesNat] at hn
      rw [hcopy', hnewPtr]
      norm_num
      apply le_trans (show statusBump.toNat + 8 ≤
        statusBump.toNat + newCapacity.toNat by
          have hn : 8 ≤ newCapacity.toNat := by
            have hl : outLen.toNat + 1 ≤ newCapacity.toNat := by
              simpa [newCapacity] using hnewLower
            omega
          omega)
      rw [← hfinishNat]
      exact hfinishIf hrequiredLe
    have hgrownCover : ∀ memory previousPages,
        ready.wasm.mem.grow
            (allocatorRequiredPages newCapacity 1 statusBump -
              UInt32.ofNat ready.wasm.mem.pages)
            (ready.wasm.memoryCap ready.runtime.currentModule 0) =
              some (memory, previousPages) →
        (allocatorRequiredPages newCapacity 1 statusBump).toNat ≤
          memory.pages := by
      intro memory previousPages hgrow
      have hm := (mem_grow_some_facts ready.wasm.mem memory
        (allocatorRequiredPages newCapacity 1 statusBump -
          UInt32.ofNat ready.wasm.mem.pages)
        (ready.wasm.memoryCap ready.runtime.currentModule 0) previousPages
        hgrow).2
      have hmono : ready.wasm.mem.pages ≤ memory.pages := by omega
      have hpagesNat : (UInt32.ofNat ready.wasm.mem.pages).toNat =
          ready.wasm.mem.pages := by
        apply UInt32.toNat_ofNat_of_lt'
        have hp : ready.wasm.mem.pages ≤ 65536 := by
          change allocated.wasm.mem.pages ≤ 65536
          exact ha.pages_upper
        norm_num [UInt32.size]
        omega
      by_cases hle : ready.wasm.mem.pages ≤
          (allocatorRequiredPages newCapacity 1 statusBump).toNat
      · have hleU : UInt32.ofNat ready.wasm.mem.pages ≤
            allocatorRequiredPages newCapacity 1 statusBump := by
          apply UInt32.le_iff_toNat_le.mpr
          rw [hpagesNat]
          exact hle
        have hsub := UInt32.toNat_sub_of_le
          (allocatorRequiredPages newCapacity 1 statusBump)
          (UInt32.ofNat ready.wasm.mem.pages) hleU
        rw [hsub, hpagesNat] at hm
        omega
      · exact le_trans (Nat.le_of_lt (lt_of_not_ge hle)) hmono
    have hgrown : ∀ memory previousPages,
        ready.wasm.mem.grow
            (allocatorRequiredPages newCapacity 1 statusBump -
              UInt32.ofNat ready.wasm.mem.pages)
            (ready.wasm.memoryCap ready.runtime.currentModule 0) =
              some (memory, previousPages) →
        statusPtr.toNat + (reallocatorCopyLen 8 newCapacity).toNat ≤
            memory.pages * 65536 ∧
        newPtr.toNat + (reallocatorCopyLen 8 newCapacity).toNat ≤
            memory.pages * 65536 := by
      intro memory previousPages hgrow
      have hm := (mem_grow_some_facts ready.wasm.mem memory
        (allocatorRequiredPages newCapacity 1 statusBump -
          UInt32.ofNat ready.wasm.mem.pages)
        (ready.wasm.memoryCap ready.runtime.currentModule 0) previousPages
        hgrow).2
      have hmono : ready.wasm.mem.pages ≤ memory.pages := by
        omega
      constructor
      · rw [hcopy']
        exact le_trans hstatusBound (Nat.mul_le_mul_right 65536 hmono)
      · rw [hcopy', hnewPtr]
        have hrequiredSmall :
            (allocatorRequiredPages newCapacity 1 statusBump).toNat < 65536 := by
          rw [hrequiredPagesNat]
          apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
          norm_num [UInt32.size] at hfinishNoWrap ⊢
          omega
        have hcover := hgrownCover memory previousPages hgrow
        apply le_trans (show statusBump.toNat + 8 ≤
          statusBump.toNat + newCapacity.toNat by
            have hl : outLen.toNat + 1 ≤ newCapacity.toNat := by
              simpa [newCapacity] using hnewLower
            omega)
        rw [← hfinishNat]
        have hceil : (allocatorFinish newCapacity 1 statusBump).toNat ≤
            (allocatorRequiredPages newCapacity 1 statusBump).toNat *
              65536 := by
          apply ceil_pages_bound
          rw [hfinishNat, ← hrequiredPagesNat]
        apply le_trans hceil
        exact Nat.mul_le_mul_right 65536 hcover
    have hreserve := reserve_call_reachesOrOOM ready []
      [.i32 decodeStack, .i32 data, .i32 capacity, .i32 outLen,
        .i32 1, .i32 source] [] decodeSuccessAfterReserve 0 []
      [decodeSuccessInnerControl, decodeSuccessMiddleControl,
        decodeSuccessOuterControl, decodeStatusControl4,
        decodeStatusControl3, decodeStatusControl2,
        decodeStatusControl1] [] (decodeStack + 12) 1 outLen 8 statusPtr
      decodeStack statusBump
      (by simpa [ready, decodeStatusReadyStore] using ha.runtime_module)
      (by simpa [ready, decodeStatusReadyStore] using ha.runtime_host)
      hreadyGlobal (by
        apply UInt32.le_iff_toNat_le.mpr
        rw [hrequired]
        omega)
      hreadyCapacity hreadyData hreadyBump
      (by
        change 1053964 ≤ ready.wasm.mem.pages * 65536
        have hp : 17 ≤ ready.wasm.mem.pages := by
          change 17 ≤ allocated.wasm.mem.pages
          exact ha.pages_lower
        omega)
      (by
        change ready.wasm.mem.pages ≤ 65536
        change allocated.wasm.mem.pages ≤ 65536
        exact ha.pages_upper)
      (UInt32.toInt32_not_negative_of_small _ hnewSigned')
      (by rw [allocatorPtr_one_eq statusBump hstatusBumpNe]
          exact hstatusBumpNe)
      (by
        change 1048528 ≤ ready.wasm.mem.pages * 65536
        have hp : 17 ≤ ready.wasm.mem.pages := by
          change 17 ≤ allocated.wasm.mem.pages
          exact ha.pages_lower
        omega)
      (by decide) (by decide) (by decide)
      (by
        have heq : (decodeStack + 12).toNat + 4 = 1048544 := by decide
        rw [heq]
        have hp : 17 ≤ ready.wasm.mem.pages := by
          change 17 ≤ allocated.wasm.mem.pages
          exact ha.pages_lower
        omega)
      (by
        have heq : (decodeStack + 12).toNat + 4 + 4 = 1048548 := by decide
        rw [heq]
        have hp : 17 ≤ ready.wasm.mem.pages := by
          change 17 ≤ allocated.wasm.mem.pages
          exact ha.pages_lower
        omega)
      (by simpa [newCapacity, hcopy] using hstatusBound)
      (by simpa [newCapacity] using hdestination)
      (by simpa [newCapacity] using hgrown)
    rcases hreserve with ⟨reservedConfig, hreserveReach, allocStore2,
        hfinish, hsuccess2, rfl⟩ | hreserveTrap
    · let postGrow := growResultOkStore allocStore2
        ((decodeStack - 16) + 4) newPtr newCapacity
      let reserved := reserveFinishStore postGrow (decodeStack + 12)
        newPtr newCapacity decodeStack
      let final := decodeSuccessOutputStore reserved newPtr source outLen
      have halloc2Pages : ready.wasm.mem.pages ≤ allocStore2.wasm.mem.pages := by
        simpa [reserveFrameStore] using hsuccess2.pages_mono
      have hreservedRuntime : reserved.runtime.currentModule = «module» := by
        change allocStore2.runtime.currentModule = «module»
        rw [hsuccess2.runtime_eq]
        simpa [reserveFrameStore, ready, decodeStatusReadyStore] using
          ha.runtime_module
      have hreservedPages : reserved.wasm.mem.pages = allocStore2.wasm.mem.pages := by
        rfl
      have hreservedGlobal : globalAt? reserved 0 =
          some (.i32 decodeStack) := by
        apply reserveFinishStore_global_zero
        rw [growResultOkStore_globalAt, hsuccess2.globalAt_eq]
        exact reserveFrameStore_global_zero ready (decodeStack - 16)
          decodeStack hreadyGlobal
      have hreadyLength : ready.wasm.mem.read32 (decodeStack + 20) = 1 := by
        exact Mem.read32_write32_same _ _ _
      have halloc2Length : allocStore2.wasm.mem.read32
          (decodeStack + 20) = 1 := by
        have hp := hsuccess2.realloc_preserves_read32_before
          (addr := decodeStack + 20) (by decide)
          (by rw [allocatorPtr_one_eq statusBump hstatusBumpNe]
              exact hstatusBumpNe)
          hcopy' (by decide) (by
            have hs : (decodeStack + 20).toNat + 4 = 1048552 := by decide
            rw [hs]
            rw [allocatorPtr_one_eq statusBump hstatusBumpNe,
              hstatusBumpNat]
            omega)
        simpa [reserveFrameStore] using hp.trans hreadyLength
      have hreservedLength : reserved.wasm.mem.read32
          (decodeStack + 20) = 1 := by
        simp only [reserved, postGrow, reserveFinishStore, reserveVectorStore,
          growResultOkStore]
        rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
          Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
          Mem.read32_write32_disjoint]
        · exact halloc2Length
        all_goals decide
      have hreservedPointer : reserved.wasm.mem.read32
          (decodeStack + 16) = newPtr := by
        simpa [reserved, postGrow] using reserveFinishStore_read_data postGrow
          (decodeStack + 12) newPtr newCapacity decodeStack
      have hsourceAlloc2 : allocStore2.wasm.mem.readBytes source.toNat
          bytes.length = bytes := by
        have hp := hsuccess2.realloc_preserves_readBytes_before (by decide)
          (by rw [allocatorPtr_one_eq statusBump hstatusBumpNe]
              exact hstatusBumpNe)
          hcopy' source.toNat bytes.length (by omega) (by
            rw [allocatorPtr_one_eq statusBump hstatusBumpNe,
              hstatusBumpNat, ← hend, ← hlength]
            omega)
        simpa [reserveFrameStore] using hp.trans hsourceReady
      have hsourceReserved : reserved.wasm.mem.readBytes source.toNat
          bytes.length = bytes := by
        simp only [reserved, postGrow, reserveFinishStore, reserveVectorStore,
          growResultOkStore]
        rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
          Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
          Mem.readBytes_write32_disjoint]
        · exact hsourceAlloc2
        all_goals right
        all_goals exact le_trans (by decide) hsourceLower
      have hstatusAlloc2 : allocStore2.wasm.mem.read8 newPtr = 0 := by
        have hp := hsuccess2.realloc_preserves_byte (by decide)
          (by rw [allocatorPtr_one_eq statusBump hstatusBumpNe]
              exact hstatusBumpNe)
          hcopy' 0 (by decide) (by simp) (by simp) (Or.inr (by
            have hl := ha.pointer_lower
            simpa [statusPtr] using le_trans (by norm_num) hl))
        have hp' : allocStore2.wasm.mem.read8 newPtr =
            ready.wasm.mem.read8 statusPtr := by
          simpa [newPtr, reserveFrameStore] using hp
        exact hp'.trans hstatusReady
      have hstatusReserved : reserved.wasm.mem.read8 newPtr = 0 := by
        have hnewLowerAddr : 1054008 ≤ newPtr.toNat := by
          rw [hnewPtr, hstatusBumpNat, ← hend]
          omega
        simp only [reserved, postGrow, reserveFinishStore, reserveVectorStore,
          growResultOkStore]
        rw [Mem.read8_write32_disjoint_core _ _ _ _
              (Or.inr (le_trans (by decide) hnewLowerAddr)),
          Mem.read8_write32_disjoint_core _ _ _ _
              (Or.inr (le_trans (by decide) hnewLowerAddr)),
          Mem.read8_write32_disjoint_core _ _ _ _
              (Or.inr (le_trans (by decide) hnewLowerAddr)),
          Mem.read8_write32_disjoint_core _ _ _ _
              (Or.inr (le_trans (by decide) hnewLowerAddr)),
          Mem.read8_write32_disjoint_core _ _ _ _
              (Or.inr (le_trans (by decide) hnewLowerAddr))]
        exact hstatusAlloc2
      have hfinishBound :
          (allocatorFinish newCapacity 1 statusBump).toNat ≤
            allocStore2.wasm.mem.pages * 65536 := by
        cases hsuccess2 with
        | freshNoGrow hzero => contradiction
        | freshGrow hzero => contradiction
        | reallocNoGrow hnonzero hfit =>
            simpa [reserveFrameStore] using hfinishIf hfit
        | reallocGrow hnonzero memory previousPages hgrow =>
            have hcover := hgrownCover memory previousPages hgrow
            have hceil :
                (allocatorFinish newCapacity 1 statusBump).toNat ≤
                  (allocatorRequiredPages newCapacity 1 statusBump).toNat *
                    65536 := by
              apply ceil_pages_bound
              rw [hfinishNat, ← hrequiredPagesNat]
            simpa [reallocatorResultStore_pages, allocatorGrownStore,
              reserveFrameStore] using
              le_trans hceil (Nat.mul_le_mul_right 65536 hcover)
      have hsourceReservedBound : source.toNat + outLen.toNat ≤
          reserved.wasm.mem.pages * 65536 := by
        rw [hreservedPages]
        exact le_trans (by
          change source.toNat + outLen.toNat ≤ ready.wasm.mem.pages * 65536
          exact le_trans hsourceBound (Nat.mul_le_mul_right 65536 (by
            change store.wasm.mem.pages ≤ ready.wasm.mem.pages
            exact le_trans hsuccess.pages_mono (by rfl))))
          (Nat.mul_le_mul_right 65536 halloc2Pages)
      have hnext : (1 + newPtr).toNat = newPtr.toNat + 1 := by
        rw [UInt32.toNat_add]
        simp only [UInt32.toNat_ofNat]
        rw [Nat.mod_eq_of_lt]
        · omega
        · rw [hnewPtr, hstatusBumpNat]
          have hb := hfacts.bump_signed
          norm_num [UInt32.size] at hb ⊢
          omega
      have hdestinationReservedBound : (1 + newPtr).toNat + outLen.toNat ≤
          reserved.wasm.mem.pages * 65536 := by
        rw [hreservedPages, hnext]
        calc
          newPtr.toNat + 1 + outLen.toNat ≤
              newPtr.toNat + newCapacity.toNat := by
            have hl : outLen.toNat + 1 ≤ newCapacity.toNat := by
              simpa [newCapacity] using hnewLower
            omega
          _ = (allocatorFinish newCapacity 1 statusBump).toNat := by
            rw [hfinishNat, hnewPtr]
          _ ≤ allocStore2.wasm.mem.pages * 65536 := hfinishBound
      have hafter := decode_success_after_reserve_reaches_common reserved data
        capacity source outLen newPtr hreservedRuntime (by
          rw [hreservedPages]
          exact le_trans (by
            change 17 ≤ ready.wasm.mem.pages
            change 17 ≤ allocated.wasm.mem.pages
            exact ha.pages_lower) halloc2Pages)
        hreservedPointer hreservedLength (by
          intro hz
          have hn := congrArg UInt32.toNat hz
          simp at hn
          omega)
        (by
          intro hz
          have hn := congrArg UInt32.toNat hz
          simp at hn
          omega)
        hsourceReservedBound hdestinationReservedBound
      have hfinalRead : final.wasm.mem.readBytes newPtr.toNat
          (0 :: bytes).length = 0 :: bytes := by
        apply decodeSuccessOutputStore_readBytes reserved newPtr source outLen
          bytes hlength hnext hsourceReserved hstatusReserved
        have hl : 1054008 ≤ newPtr.toNat := by
          rw [hnewPtr, hstatusBumpNat, ← hend]
          omega
        omega
      have hcopiedPointer :
          (decodeSuccessCopiedStore reserved (1 + newPtr) source outLen).wasm.mem.read32
            (decodeStack + 16) = newPtr := by
        simp only [decodeSuccessCopiedStore]
        rw [Mem.read32_copy_before _ _ _ _ _ (by
          rw [hnext]
          have hs : (decodeStack + 16).toNat + 4 = 1048548 := by decide
          rw [hs]
          have hl : 1054008 ≤ newPtr.toNat := by
            rw [hnewPtr, hstatusBumpNat, ← hend]
            omega
          omega)]
        exact hreservedPointer
      have hfinalPointer : final.wasm.mem.read32 (decodeStack + 16) =
          newPtr := by
        simp only [final, decodeSuccessOutputStore, decodeSuccessLengthStore]
        split
        · rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))]
          exact hreservedPointer
        · rw [Mem.read32_write32_disjoint _ _ _ _ (Or.inl (by decide))]
          exact hcopiedPointer
      have hfinalLength : final.wasm.mem.read32 (decodeStack + 20) =
          outLen + 1 := Mem.read32_write32_same _ _ _
      have hresultLength : (0 :: bytes).length = (outLen + 1).toNat := by
        have hout : outLen.toNat + 1 < UInt32.size := by
          norm_num [UInt32.size]
          omega
        simp only [List.length_cons]
        rw [UInt32.toNat_add]
        norm_num only [UInt32.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hout]
        omega
      have hfinalPages : final.wasm.mem.pages = allocStore2.wasm.mem.pages := by
        rw [← hreservedPages]
        simp only [final, decodeSuccessOutputStore, decodeSuccessLengthStore]
        split <;> rfl
      have hfinalBound : newPtr.toNat + (outLen + 1).toNat ≤
          final.wasm.mem.pages * 65536 := by
        rw [hfinalPages, ← hresultLength]
        simp only [List.length_cons]
        rw [← hlength]
        calc
          newPtr.toNat + (outLen.toNat + 1) ≤
              newPtr.toNat + newCapacity.toNat := by
            have hl : outLen.toNat + 1 ≤ newCapacity.toNat := by
              simpa [newCapacity] using hnewLower
            omega
          _ = (allocatorFinish newCapacity 1 statusBump).toNat := by
            rw [hfinishNat, hnewPtr]
          _ ≤ allocStore2.wasm.mem.pages * 65536 := hfinishBound
      have hfinalRuntime : final.runtime = reserved.runtime := by
        simp only [final, decodeSuccessOutputStore, decodeSuccessLengthStore]
        split <;> rfl
      have hfinalGlobal : globalAt? final 0 = some (.i32 decodeStack) := by
        have hg : final.wasm.globals.globals =
            reserved.wasm.globals.globals := by
          simp only [final, decodeSuccessOutputStore,
            decodeSuccessLengthStore, decodeSuccessCopiedStore]
          split <;> rfl
        simp only [globalAt?, canonicalGlobalIndex_zero] at hreservedGlobal ⊢
        rw [hg]
        exact hreservedGlobal
      have hfinalOutput : final.wasm.host.stdio.output = [] := by
        have hallocOutput : allocStore2.wasm.host.stdio.output = [] := by
          rw [hsuccess2.host_eq]
          change ready.wasm.host.stdio.output = []
          change allocated.wasm.host.stdio.output = []
          exact ha.output_eq
        by_cases hz : outLen = 0 <;>
          simpa [final, reserved, postGrow, decodeSuccessOutputStore,
            decodeSuccessLengthStore, decodeSuccessCopiedStore,
            reserveFinishStore, reserveVectorStore, growResultOkStore, hz]
            using hallocOutput
      have hterm := decode_common_terminates final data capacity outLen 1 source
        newPtr (outLen + 1) (0 :: bytes)
        (by rw [hfinalRuntime]; exact hreservedRuntime)
        (by
          rw [hfinalRuntime]
          change reserved.runtime.currentHost = Universal.envFor «module»
          change allocStore2.runtime.currentHost = Universal.envFor «module»
          rw [hsuccess2.runtime_eq]
          simpa [reserveFrameStore, ready, decodeStatusReadyStore] using
            ha.runtime_host)
        hfinalGlobal
        (by rw [hfinalPages]
            exact le_trans (by
              change 17 ≤ ready.wasm.mem.pages
              change 17 ≤ allocated.wasm.mem.pages
              exact ha.pages_lower) halloc2Pages)
        hfinalPointer hfinalLength hresultLength (by simp)
        (by rw [← hresultLength]; exact hfinalRead) hfinalBound hfinalOutput
      left
      apply TerminatesWith.prependReaches
        (hprefix.trans (hreach.trans (hblocks.trans (htoReserve.trans
          (hreserveReach.trans hafter)))))
      exact hterm.mono (by
        intro values finalStore hout
        have heven : input.length % 2 = 0 := by
          have hlenInput := decode_some_length input bytes hdecode
          omega
        simpa [decodeOutput, heven, hdecode] using hout)
    · right
      exact TrapsWith.prependReaches
        (hprefix.trans (hreach.trans (hblocks.trans htoReserve))) hreserveTrap
  · right
    exact TrapsWith.prependReaches hprefix htrap

theorem decode_success_wrapper_outcome
    (input bytes : List UInt8) (store : MachineStore Universal.State)
    (data capacity source outLen bump : UInt32)
    (hdecode : decode input = some bytes)
    (htag : store.wasm.mem.read32 decodeResultOut = capacity)
    (hpointer : store.wasm.mem.read32 (decodeResultOut + 4) = source)
    (hlengthField : store.wasm.mem.read32 (decodeResultOut + 8) = outLen)
    (hlength : outLen.toNat = bytes.length)
    (hfits : outLen.toNat ≤ capacity.toNat)
    (hcapacitySigned : capacity.toNat < 2 ^ 31)
    (hsourceBound : source.toNat + outLen.toNat ≤
      store.wasm.mem.pages * 65536)
    (hsourceRead : store.wasm.mem.readBytes source.toNat bytes.length = bytes)
    (hfacts : DecodeCoreStoreFacts store bump)
    (hplacement : bytes = [] ∨
      (1054000 ≤ source.toNat ∧
        source.toNat + capacity.toNat = bump.toNat)) :
    DecodeTerminalOutcome input (decodeAfterCoreConfig store data) := by
  by_cases hsmall : outLen.toNat ≤ 7
  · exact decode_success_small_wrapper_outcome input bytes store data
      capacity source outLen bump hdecode htag hpointer hlengthField hlength
      hfits hcapacitySigned hsourceBound hsourceRead hfacts hplacement hsmall
  · exact decode_success_large_wrapper_outcome input bytes store data
      capacity source outLen bump hdecode htag hpointer hlengthField hlength
      hfits hcapacitySigned hsourceBound hsourceRead hfacts hplacement (by omega)

end Submission.HexDecodeStdio
