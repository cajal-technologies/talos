import HexDecodeStdio.DecodeCoreCompose
import HexDecodeStdio.DecodeWrapperCommon
import HexDecodeStdio.ReserveOutcome
import HexDecodeStdio.PushOperational

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def firstBlockBody : Program → Program
  | .block _ _ body :: _ => body
  | _ => []

def decodeStatusBody1 : Program := firstBlockBody decodeAfterCore
def decodeStatusBody2 : Program := firstBlockBody decodeStatusBody1
def decodeStatusBody3 : Program := firstBlockBody decodeStatusBody2
def decodeStatusBody4 : Program := firstBlockBody decodeStatusBody3
def decodeStatusBody5 : Program := firstBlockBody decodeStatusBody4

def decodeStatusControl1 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeStatusBody1, continuation := decodeAfterStatus
    belowStack := [] }

def decodeStatusControl2 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeStatusBody2, continuation := decodeStatusBody1.drop 1
    belowStack := [] }

def decodeStatusControl3 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeStatusBody3, continuation := decodeStatusBody2.drop 1
    belowStack := [] }

def decodeStatusControl4 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeStatusBody4, continuation := decodeStatusBody3.drop 1
    belowStack := [] }

def decodeStatusControl5 : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := decodeStatusBody5, continuation := decodeStatusBody4.drop 1
    belowStack := [] }

def decodeErrorAfterAlloc : Program := decodeStatusBody5.drop 13
def decodeSuccessAfterAlloc : Program := (decodeStatusBody4.drop 1).drop 10

def decodeStatusAllocatedStore (allocStore : MachineStore Universal.State)
    (bump : UInt32) : MachineStore Universal.State :=
  reserveFinishStore
    (pushGrowOkStore allocStore ((decodeStack - 16) + 4)
      (allocatorPtr bump 1) 8)
    decodeStatusVector (allocatorPtr bump 1) 8 decodeStack

def decodeStatusReadyStore (store : MachineStore Universal.State)
    (pointer : UInt32) (status : UInt8) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with mem :=
      (store.wasm.mem.write8 pointer status).write32 (decodeStack + 20) 1 } }

structure DecodeStatusAllocFacts (store : MachineStore Universal.State)
    (pointer : UInt32) : Prop where
  runtime_module : store.runtime.currentModule = «module»
  runtime_host : store.runtime.currentHost = Universal.envFor «module»
  pages_lower : 17 ≤ store.wasm.mem.pages
  pages_upper : store.wasm.mem.pages ≤ 65536
  global_eq : globalAt? store 0 = some (.i32 decodeStack)
  capacity : store.wasm.mem.read32 decodeStatusVector = 8
  data : store.wasm.mem.read32 (decodeStatusVector + 4) = pointer
  length : store.wasm.mem.read32 (decodeStatusVector + 8) = 0
  output_eq : store.wasm.host.stdio.output = []
  pointer_lower : 1054000 ≤ pointer.toNat
  pointer_bound : pointer.toNat + 1 ≤ store.wasm.mem.pages * 65536

theorem decodeStatusAllocatedStore_facts
    (store allocStore : MachineStore Universal.State) (bump : UInt32)
    (hfacts : DecodeCoreStoreFacts store bump)
    (hsuccess : ByteGrowSuccess
      (reserveFrameStore store (decodeStack - 16)) 0 1 8 bump allocStore) :
    DecodeStatusAllocFacts (decodeStatusAllocatedStore allocStore bump)
      (allocatorPtr bump 1) := by
  let frame := decodeStack - 16
  let base := reserveFrameStore store frame
  let ptr := allocatorPtr bump 1
  let postGrow := pushGrowOkStore allocStore (frame + 4) ptr 8
  let finalStore := decodeStatusAllocatedStore allocStore bump
  have hmono := hsuccess.pages_mono
  have hruntime : allocStore.runtime = store.runtime := by
    exact hsuccess.runtime_eq.trans (by rfl)
  have hbaseGlobal : globalAt? base 0 = some (.i32 frame) :=
    reserveFrameStore_global_zero store frame decodeStack hfacts.global_eq
  have hallocGlobal : globalAt? allocStore 0 = some (.i32 frame) := by
    exact (hsuccess.globalAt_eq 0).trans hbaseGlobal
  have hpostGlobal : globalAt? postGrow 0 = some (.i32 frame) := by
    change globalAt? allocStore 0 = some (.i32 frame)
    exact hallocGlobal
  have hlength : finalStore.wasm.mem.read32 (decodeStatusVector + 8) = 0 := by
    simp only [finalStore, decodeStatusAllocatedStore, reserveFinishStore,
      reserveVectorStore, postGrow, pushGrowOkStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint]
    · exact (hsuccess.fresh_preserves_read32 (by decide)).trans
        hfacts.status_length
    all_goals decide
  have hptrBound : ptr.toNat + 1 ≤ finalStore.wasm.mem.pages * 65536 := by
    change ptr.toNat + 1 ≤ allocStore.wasm.mem.pages * 65536
    by_cases hz : bump = 0
    · subst bump
      change (allocatorPtr 0 1).toNat + 1 ≤ allocStore.wasm.mem.pages * 65536
      have hp : 17 ≤ allocStore.wasm.mem.pages :=
        le_trans hfacts.pages_lower hmono
      simp [allocatorPtr, allocatorBase]
      omega
    · have hfinish := hsuccess.fresh_eight_finish_bound hz (by
          have hbumpSigned := hfacts.bump_signed
          norm_num [UInt32.size] at hbumpSigned ⊢
          omega) (by
          change (reserveFrameStore store (decodeStack - 16)).wasm.mem.pages <
            UInt32.size
          change store.wasm.mem.pages < UInt32.size
          have hp := hfacts.pages_upper
          norm_num [UInt32.size]
          omega)
      rw [show ptr = bump by exact allocatorPtr_one_eq bump hz]
      omega
  refine {
    runtime_module := by
      change allocStore.runtime.currentModule = «module»
      rw [hruntime]
      exact hfacts.runtime_module
    runtime_host := by
      change allocStore.runtime.currentHost = Universal.envFor «module»
      rw [hruntime]
      exact hfacts.runtime_host
    pages_lower := by
      change 17 ≤ allocStore.wasm.mem.pages
      exact le_trans hfacts.pages_lower hmono
    pages_upper := by
      change allocStore.wasm.mem.pages ≤ 65536
      exact hsuccess.pages_le_cap hfacts.memory_cap hfacts.pages_upper
    global_eq := by
      change globalAt?
        (reserveFinishStore postGrow decodeStatusVector ptr 8 decodeStack) 0 =
          some (.i32 decodeStack)
      exact reserveFinishStore_global_zero postGrow decodeStatusVector ptr 8
        decodeStack frame hpostGlobal
    capacity := by
      change
        ((postGrow.wasm.mem.write32 decodeStatusVector 8).write32
          (decodeStatusVector + 4) ptr).read32 decodeStatusVector = 8
      rw [Mem.read32_write32_disjoint]
      · exact Mem.read32_write32_same _ _ _
      · left; decide
    data := by
      exact reserveFinishStore_read_data postGrow decodeStatusVector ptr 8
        decodeStack
    length := hlength
    output_eq := by
      change allocStore.wasm.host.stdio.output = []
      rw [hsuccess.host_eq]
      exact hfacts.output_eq
    pointer_lower := by
      rcases hfacts.bump_zero_or_lower with hz | hlower
      · subst bump
        simp [allocatorPtr, allocatorBase]
      · have hz : bump ≠ 0 := by
          intro hz
          subst bump
          simp at hlower
        change 1054000 ≤ (allocatorPtr bump 1).toNat
        rw [allocatorPtr_one_eq bump hz]
        exact hlower
    pointer_bound := hptrBound }

/-- The status-vector seed allocation, retaining the successful allocator
store needed to establish memory facts for the wrapper's remaining code. -/
theorem decode_status_alloc_reachesOrOOM
    (store : MachineStore Universal.State) (locals : List Value)
    (code : Program) (controls : List ControlFrame) (bump : UInt32)
    (hfacts : DecodeCoreStoreFacts store bump) :
    ReachesOrOOM
      ⟨.running ⟨⟨[], locals, [.i32 decodeStatusVector]⟩,
        [.call 62] ++ code, 0, [], controls, []⟩, store⟩
      (fun final => ∃ allocStore,
        ByteGrowSuccess (reserveFrameStore store (decodeStack - 16))
          0 1 8 bump allocStore ∧
        final = ⟨.running ⟨⟨[], locals, []⟩, code, 0, [], controls, []⟩,
          decodeStatusAllocatedStore allocStore bump⟩) := by
  let ptr := allocatorPtr bump 1
  have hptr : ptr ≠ 0 := by
    by_cases hz : bump = 0
    · simp [ptr, allocatorPtr, allocatorBase, hz]
    · simpa [ptr, allocatorPtr_one_eq bump hz] using hz
  rcases push_reserve_initial_outcome store [] locals [] code 0 [] controls []
      decodeStatusVector decodeStack bump hfacts.runtime_module
      hfacts.runtime_host hfacts.global_eq hfacts.status_capacity
      hfacts.status_pointer hfacts.bump_eq (by
        have hp := hfacts.pages_lower
        change 1053964 ≤ store.wasm.mem.pages * 65536
        omega) hfacts.pages_upper hptr (by
        have hp := hfacts.pages_lower
        change 1048528 ≤ store.wasm.mem.pages * 65536
        omega) (by decide) (by decide) (by decide) (by
        have hp := hfacts.pages_lower
        change 1048544 ≤ store.wasm.mem.pages * 65536
        omega) (by
        have hp := hfacts.pages_lower
        change 1048548 ≤ store.wasm.mem.pages * 65536
        omega) with ⟨allocStore, hsuccess, hreach⟩ | htrap
  · left
    exact ⟨_, hreach, allocStore, hsuccess, rfl⟩
  · exact Or.inr htrap

theorem decode_error_to_status_alloc
    (store : MachineStore Universal.State) (data bad : UInt32)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (htag : store.wasm.mem.read32 decodeResultOut = 2147483648)
    (hbad : store.wasm.mem.read32 (decodeResultOut + 4) = bad) :
    Reaches (decodeAfterCoreConfig store data)
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 2147483648, .i32 bad,
              .i32 0, .i32 0], [.i32 decodeStatusVector]⟩,
          [.call 62] ++ decodeErrorAfterAlloc, 0, [],
          [decodeStatusControl5, decodeStatusControl4, decodeStatusControl3,
            decodeStatusControl2, decodeStatusControl1], []⟩, store⟩ := by
  simp only [decodeAfterCoreConfig, decodeAfterCore, decodeAfterRead, func9,
    List.drop, decodeStatusBody1, decodeStatusBody2, decodeStatusBody3,
    decodeStatusBody4, decodeStatusBody5, firstBlockBody]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048556 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [htag]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 0) (by decide))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048560 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show decodeStack + 28 = decodeResultOut + 4 by decide, hbad]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [decodeErrorAfterAlloc, decodeStatusControl1, decodeStatusControl2,
    decodeStatusControl3, decodeStatusControl4, decodeStatusControl5,
    decodeAfterStatus, decodeAfterCore, decodeAfterRead, func9,
    decodeStatusBody1, decodeStatusBody2, decodeStatusBody3,
    decodeStatusBody4, decodeStatusBody5, firstBlockBody]
  exact ⟨[], .refl _⟩

theorem decode_success_to_status_alloc
    (store : MachineStore Universal.State)
    (data capacity pointer length : UInt32)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (htag : store.wasm.mem.read32 decodeResultOut = capacity)
    (htagNe : capacity ≠ 2147483648)
    (hpointer : store.wasm.mem.read32 (decodeResultOut + 4) = pointer)
    (hlength : store.wasm.mem.read32 (decodeResultOut + 8) = length) :
    Reaches (decodeAfterCoreConfig store data)
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 capacity, .i32 length,
              .i32 0, .i32 pointer], [.i32 decodeStatusVector]⟩,
          [.call 62] ++ decodeSuccessAfterAlloc, 0, [],
          [decodeStatusControl4, decodeStatusControl3, decodeStatusControl2,
            decodeStatusControl1], []⟩, store⟩ := by
  simp only [decodeAfterCoreConfig, decodeAfterCore, decodeAfterRead, func9,
    List.drop, decodeStatusBody1, decodeStatusBody2, decodeStatusBody3,
    decodeStatusBody4, decodeStatusBody5, firstBlockBody]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048556 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [htag]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 1) (by simp [htagNe]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048560 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show decodeStack + 28 = decodeResultOut + 4 by decide, hpointer]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048564 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show decodeStack + 32 = decodeResultOut + 8 by decide, hlength]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [decodeSuccessAfterAlloc, decodeStatusControl1, decodeStatusControl2,
    decodeStatusControl3, decodeStatusControl4, decodeAfterStatus,
    decodeAfterCore, decodeAfterRead, func9, decodeStatusBody1,
    decodeStatusBody2, decodeStatusBody3, decodeStatusBody4, firstBlockBody]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_error_odd_after_alloc_reaches
    (store : MachineStore Universal.State) (data bump : UInt32)
    (hfacts : DecodeStatusAllocFacts store (allocatorPtr bump 1)) :
    Reaches
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 2147483648,
              .i32 1114112, .i32 0, .i32 0], []⟩,
          decodeErrorAfterAlloc, 0, [],
          [decodeStatusControl5, decodeStatusControl4, decodeStatusControl3,
            decodeStatusControl2, decodeStatusControl1], []⟩, store⟩
      (decodeCommonConfig
        (decodeStatusReadyStore store (allocatorPtr bump 1) 1)
        data (allocatorPtr bump 1) 1114112 1 0) := by
  simp only [decodeErrorAfterAlloc, decodeStatusBody5, decodeStatusBody4,
    decodeStatusBody3, decodeStatusBody2, decodeStatusBody1,
    firstBlockBody, decodeAfterCore, decodeAfterRead, func9, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    have hp := hfacts.pages_lower
    change 1048548 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show store.wasm.mem.read32 (decodeStack + 16) =
      store.wasm.mem.read32 (decodeStatusVector + 4) by rfl,
    hfacts.data]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.gtU (result := 0) (by decide))
  apply Reaches.prepend (Step.select (selected := .i32 1) (by decide))
  apply Reaches.prepend (Step.brTable rfl)
  simp [decodeStatusControl1, decodeStatusControl2, decodeStatusControl3,
    decodeStatusControl4, decodeStatusControl5, decodeStatusBody1,
    decodeStatusBody2, decodeStatusBody3, decodeStatusBody4,
    decodeStatusBody5, firstBlockBody, decodeAfterStatus, decodeAfterCore,
    decodeAfterRead, func9]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store8 (address := allocatorPtr bump 1)
    (offset := 0) hfacts.pointer_bound)
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    have hp := hfacts.pages_lower
    change 1048552 ≤ (store.wasm.mem.write8 (allocatorPtr bump 1) 1).pages *
      65536
    change 1048552 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.br rfl)
  simp [decodeCommonConfig, decodeStatusReadyStore, decodeAfterStatus,
    decodeAfterCore, decodeAfterRead, func9, decodeStatusControl1,
    decodeStatusControl2, decodeStatusControl3, decodeStatusControl4,
    decodeStatusControl5, decodeStatusBody1, decodeStatusBody2,
    decodeStatusBody3, decodeStatusBody4, decodeStatusBody5, firstBlockBody]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_error_invalid_after_alloc_reaches
    (store : MachineStore Universal.State) (data bad bump : UInt32)
    (hbad : bad.toNat ≤ 255)
    (hfacts : DecodeStatusAllocFacts store (allocatorPtr bump 1)) :
    Reaches
      ⟨.running
        ⟨⟨[], [.i32 decodeStack, .i32 data, .i32 2147483648,
              .i32 bad, .i32 0, .i32 0], []⟩,
          decodeErrorAfterAlloc, 0, [],
          [decodeStatusControl5, decodeStatusControl4, decodeStatusControl3,
            decodeStatusControl2, decodeStatusControl1], []⟩, store⟩
      (decodeCommonConfig
        (decodeStatusReadyStore store (allocatorPtr bump 1) 2)
        data (allocatorPtr bump 1) bad (4293853185 + bad) 0) := by
  simp only [decodeErrorAfterAlloc, decodeStatusBody5, decodeStatusBody4,
    decodeStatusBody3, decodeStatusBody2, decodeStatusBody1,
    firstBlockBody, decodeAfterCore, decodeAfterRead, func9, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    have hp := hfacts.pages_lower
    change 1048548 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show store.wasm.mem.read32 (decodeStack + 16) =
      store.wasm.mem.read32 (decodeStatusVector + 4) by rfl,
    hfacts.data]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have hgt : 4293853185 + bad > bad := by
    apply UInt32.lt_iff_toNat_lt.mpr
    simp [UInt32.toNat_add]
    norm_num [UInt32.size] at hbad ⊢
    omega
  apply Reaches.prepend (Step.gtU (result := 1) (by simp [hgt]))
  apply Reaches.prepend (Step.select (selected := .i32 0) (by simp))
  apply Reaches.prepend (Step.brTable rfl)
  simp [decodeStatusControl1, decodeStatusControl2, decodeStatusControl3,
    decodeStatusControl4, decodeStatusControl5, decodeStatusBody1,
    decodeStatusBody2, decodeStatusBody3, decodeStatusBody4,
    decodeStatusBody5, firstBlockBody, decodeAfterStatus, decodeAfterCore,
    decodeAfterRead, func9]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store8 (address := allocatorPtr bump 1)
    (offset := 0) hfacts.pointer_bound)
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    have hp := hfacts.pages_lower
    change 1048552 ≤ (store.wasm.mem.write8 (allocatorPtr bump 1) 2).pages *
      65536
    change 1048552 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.br rfl)
  simp [decodeCommonConfig, decodeStatusReadyStore, decodeAfterStatus,
    decodeAfterCore, decodeAfterRead, func9, decodeStatusControl1,
    decodeStatusControl2, decodeStatusControl3, decodeStatusControl4,
    decodeStatusControl5, decodeStatusBody1, decodeStatusBody2,
    decodeStatusBody3, decodeStatusBody4, decodeStatusBody5, firstBlockBody]
  exact ⟨[], .refl _⟩

theorem decode_status_ready_terminates
    (store : MachineStore Universal.State)
    (data a b c d pointer : UInt32) (status : UInt8)
    (hfacts : DecodeStatusAllocFacts store pointer) :
    TerminatesWith
      (decodeCommonConfig (decodeStatusReadyStore store pointer status)
        data a b c d)
      (fun values final => values = [] ∧
        final.wasm.host.stdio.output = [status]) := by
  let ready := decodeStatusReadyStore store pointer status
  apply decode_common_terminates ready data a b c d pointer 1 [status]
  · simpa [ready, decodeStatusReadyStore] using hfacts.runtime_module
  · simpa [ready, decodeStatusReadyStore] using hfacts.runtime_host
  · change globalAt? store 0 = some (.i32 decodeStack)
    exact hfacts.global_eq
  · change 17 ≤ store.wasm.mem.pages
    exact hfacts.pages_lower
  · simp only [ready, decodeStatusReadyStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write8_disjoint]
    · exact hfacts.data
    · left
      have hp := hfacts.pointer_lower
      change 1048548 ≤ pointer.toNat
      omega
    · left; decide
  · simp [ready, decodeStatusReadyStore]
  · simp
  · simp
  · simp only [ready, decodeStatusReadyStore]
    rw [Mem.readBytes_write32_disjoint]
    · simpa using Mem.readBytes_write8_append store.wasm.mem pointer.toNat 0
        [] pointer status rfl (by simp [Mem.readBytes]) rfl
    · right
      have hp := hfacts.pointer_lower
      have hs : (decodeStack + 20).toNat = 1048548 := by decide
      rw [hs]
      omega
  · change pointer.toNat + 1 ≤ store.wasm.mem.pages * 65536
    exact hfacts.pointer_bound
  · simpa [ready, decodeStatusReadyStore] using hfacts.output_eq

def DecodeTerminalOutcome (input : List UInt8)
    (config : Config Universal.State) : Prop :=
  TerminatesWith config (fun values final => values = [] ∧
      final.wasm.host.stdio.output = decodeOutput input) ∨
    TrapsWith config (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true)

set_option maxRecDepth 100000 in
theorem decode_invalid_wrapper_outcome
    (input : List UInt8) (store : MachineStore Universal.State)
    (data bad bump : UInt32)
    (htag : store.wasm.mem.read32 decodeResultOut = 2147483648)
    (hbad : store.wasm.mem.read32 (decodeResultOut + 4) = bad)
    (hkind : (input.length % 2 = 1 ∧ bad = 1114112) ∨
      (input.length % 2 = 0 ∧ bad.toNat ≤ 255))
    (hdecode : decode input = none)
    (hfacts : DecodeCoreStoreFacts store bump) :
    DecodeTerminalOutcome input (decodeAfterCoreConfig store data) := by
  have hprefix := decode_error_to_status_alloc store data bad
    hfacts.pages_lower htag hbad
  have halloc := decode_status_alloc_reachesOrOOM store
    [.i32 decodeStack, .i32 data, .i32 2147483648, .i32 bad, .i32 0,
      .i32 0] decodeErrorAfterAlloc
    [decodeStatusControl5, decodeStatusControl4, decodeStatusControl3,
      decodeStatusControl2, decodeStatusControl1] bump hfacts
  rcases halloc with ⟨middle, hreach, allocStore, hsuccess, rfl⟩ | htrap
  · left
    let allocated := decodeStatusAllocatedStore allocStore bump
    have ha := decodeStatusAllocatedStore_facts store allocStore bump hfacts
      hsuccess
    rcases hkind with ⟨hodd, rfl⟩ | ⟨heven, hsmall⟩
    · have hstatus := decode_error_odd_after_alloc_reaches allocated data bump ha
      have hterm := decode_status_ready_terminates allocated data
        (allocatorPtr bump 1) 1114112 1 0 (allocatorPtr bump 1) 1 ha
      apply TerminatesWith.prependReaches (hprefix.trans (hreach.trans hstatus))
      exact hterm.mono (by
        intro values final h
        simpa [decodeOutput, hodd] using h)
    · have hstatus := decode_error_invalid_after_alloc_reaches allocated data bad
        bump hsmall ha
      have hterm := decode_status_ready_terminates allocated data
        (allocatorPtr bump 1) bad (4293853185 + bad) 0
        (allocatorPtr bump 1) 2 ha
      apply TerminatesWith.prependReaches (hprefix.trans (hreach.trans hstatus))
      exact hterm.mono (by
        intro values final h
        simp only [decodeOutput, heven, ↓reduceIte, hdecode]
        rcases h with ⟨rfl, hout⟩
        exact ⟨rfl, by simpa [hout]⟩)
  · right
    exact TrapsWith.prependReaches hprefix htrap

end Project.HexDecodeStdio
