import HexDecodeStdio.DecodeLoopReserveCompose
import HexDecodeStdio.DecodeLoopInvariantSteps
import HexDecodeStdio.DecodeLoopReturnOperational

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- Machine-state facts preserved by the decoder core and consumed by the
outer `decode` wrapper.  Keeping these facts beside the observable core result
lets the wrapper call the allocator and the universal stdio host without
reconstructing hidden execution history. -/
structure DecodeCoreStoreFacts (store : MachineStore Universal.State)
    (bump : UInt32) : Prop where
  runtime_module : store.runtime.currentModule = «module»
  runtime_host : store.runtime.currentHost = Universal.envFor «module»
  memory_cap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536
  pages_lower : 17 ≤ store.wasm.mem.pages
  pages_upper : store.wasm.mem.pages ≤ 65536
  global_eq : globalAt? store 0 = some (.i32 decodeStack)
  status_capacity : store.wasm.mem.read32 decodeStatusVector = 0
  status_pointer : store.wasm.mem.read32 (decodeStatusVector + 4) = 1
  status_length : store.wasm.mem.read32 (decodeStatusVector + 8) = 0
  input_eq : store.wasm.host.stdio.input = []
  output_eq : store.wasm.host.stdio.output = []
  oom_eq : store.wasm.host.oom.raised = false
  bump_eq : store.wasm.mem.read32 1053960 = bump
  bump_zero_or_lower : bump = 0 ∨ 1054000 ≤ bump.toNat
  bump_signed : bump.toNat < 2 ^ 31

theorem decodeLoopSuccessStore_core_facts
    (store : MachineStore Universal.State)
    (ptr capacity outLen bump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hhost : store.runtime.currentHost = Universal.envFor «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536)
    (hpagesLower : 17 ≤ store.wasm.mem.pages)
    (hpagesUpper : store.wasm.mem.pages ≤ 65536)
    (hglobal : globalAt? store 0 = some (.i32 coreFrame))
    (hstatusCapacity : store.wasm.mem.read32 decodeStatusVector = 0)
    (hstatusPointer : store.wasm.mem.read32 (decodeStatusVector + 4) = 1)
    (hstatusLength : store.wasm.mem.read32 (decodeStatusVector + 8) = 0)
    (hinput : store.wasm.host.stdio.input = [])
    (houtput : store.wasm.host.stdio.output = [])
    (hoom : store.wasm.host.oom.raised = false)
    (hbump : store.wasm.mem.read32 1053960 = bump)
    (hbumpBase : bump = 0 ∨ 1054000 ≤ bump.toNat)
    (hbumpSigned : bump.toNat < 2 ^ 31) :
    DecodeCoreStoreFacts (decodeLoopSuccessStore store ptr capacity outLen)
      bump := by
  have preserve (addr value : UInt32)
      (haddr : store.wasm.mem.read32 addr = value)
      (h8 : addr.toNat + 4 ≤ (decodeResultOut + 8).toNat ∨
        (decodeResultOut + 8).toNat + 4 ≤ addr.toNat)
      (h4 : addr.toNat + 4 ≤ (decodeResultOut + 4).toNat ∨
        (decodeResultOut + 4).toNat + 4 ≤ addr.toNat)
      (h0 : addr.toNat + 4 ≤ decodeResultOut.toNat ∨
        decodeResultOut.toNat + 4 ≤ addr.toNat) :
      (decodeLoopSuccessStore store ptr capacity outLen).wasm.mem.read32 addr =
        value := by
    simp only [decodeLoopSuccessStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ h0,
      Mem.read32_write32_disjoint _ _ _ _ h4,
      Mem.read32_write32_disjoint _ _ _ _ h8]
    exact haddr
  refine {
    runtime_module := hmod
    runtime_host := hhost
    memory_cap := hcap
    pages_lower := hpagesLower
    pages_upper := hpagesUpper
    global_eq := by
      have hzero : 0 < store.wasm.globals.globals.length := by
        apply (getElem?_eq_some_iff.mp (show
          store.wasm.globals.globals[0]? = some (.i32 coreFrame) by
            simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
      simpa only [decodeLoopSuccessStore, globalAt?, canonicalGlobalIndex_zero]
        using (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero)
    status_capacity := preserve decodeStatusVector 0 hstatusCapacity
      (by decide) (by decide) (by decide)
    status_pointer := preserve (decodeStatusVector + 4) 1 hstatusPointer
      (by decide) (by decide) (by decide)
    status_length := preserve (decodeStatusVector + 8) 0 hstatusLength
      (by decide) (by decide) (by decide)
    input_eq := hinput
    output_eq := houtput
    oom_eq := hoom
    bump_eq := preserve 1053960 bump hbump (by decide) (by decide) (by decide)
    bump_zero_or_lower := hbumpBase
    bump_signed := hbumpSigned }

theorem decodeInvalidCoreStore_core_facts
    (store : MachineStore Universal.State) (bad index bump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hhost : store.runtime.currentHost = Universal.envFor «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536)
    (hpagesLower : 17 ≤ store.wasm.mem.pages)
    (hpagesUpper : store.wasm.mem.pages ≤ 65536)
    (hglobal : globalAt? store 0 = some (.i32 coreFrame))
    (hstatusCapacity : store.wasm.mem.read32 decodeStatusVector = 0)
    (hstatusPointer : store.wasm.mem.read32 (decodeStatusVector + 4) = 1)
    (hstatusLength : store.wasm.mem.read32 (decodeStatusVector + 8) = 0)
    (hinput : store.wasm.host.stdio.input = [])
    (houtput : store.wasm.host.stdio.output = [])
    (hoom : store.wasm.host.oom.raised = false)
    (hbump : store.wasm.mem.read32 1053960 = bump)
    (hbumpBase : bump = 0 ∨ 1054000 ≤ bump.toNat)
    (hbumpSigned : bump.toNat < 2 ^ 31) :
    DecodeCoreStoreFacts (decodeInvalidCoreStore store bad index) bump := by
  have preserve (addr value : UInt32)
      (haddr : store.wasm.mem.read32 addr = value)
      (h8 : addr.toNat + 4 ≤ (decodeResultOut + 8).toNat ∨
        (decodeResultOut + 8).toNat + 4 ≤ addr.toNat)
      (h4 : addr.toNat + 4 ≤ (decodeResultOut + 4).toNat ∨
        (decodeResultOut + 4).toNat + 4 ≤ addr.toNat)
      (h0 : addr.toNat + 4 ≤ decodeResultOut.toNat ∨
        decodeResultOut.toNat + 4 ≤ addr.toNat) :
      (decodeInvalidCoreStore store bad index).wasm.mem.read32 addr = value := by
    simp only [decodeInvalidCoreStore]
    rw [Mem.read32_write32_disjoint _ _ _ _ h0,
      Mem.read32_write32_disjoint _ _ _ _ h4,
      Mem.read32_write32_disjoint _ _ _ _ h8]
    exact haddr
  refine {
    runtime_module := hmod
    runtime_host := hhost
    memory_cap := hcap
    pages_lower := hpagesLower
    pages_upper := hpagesUpper
    global_eq := by
      have hzero : 0 < store.wasm.globals.globals.length := by
        apply (getElem?_eq_some_iff.mp (show
          store.wasm.globals.globals[0]? = some (.i32 coreFrame) by
            simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
      simpa only [decodeInvalidCoreStore, globalAt?, canonicalGlobalIndex_zero]
        using (List.getElem?_set_eq_of_lt (.i32 decodeStack) hzero)
    status_capacity := preserve decodeStatusVector 0 hstatusCapacity
      (by decide) (by decide) (by decide)
    status_pointer := preserve (decodeStatusVector + 4) 1 hstatusPointer
      (by decide) (by decide) (by decide)
    status_length := preserve (decodeStatusVector + 8) 0 hstatusLength
      (by decide) (by decide) (by decide)
    input_eq := hinput
    output_eq := houtput
    oom_eq := hoom
    bump_eq := preserve 1053960 bump hbump (by decide) (by decide) (by decide)
    bump_zero_or_lower := hbumpBase
    bump_signed := hbumpSigned }

/-- Observable result of the core decoder after its Wasm call has returned.
For a failed decode we retain just enough of the error payload to justify the
outer wrapper's status dispatch: `1114112` denotes odd length, while an
ordinary invalid byte is masked to eight bits. -/
def DecodeCoreResult (input : List UInt8) (data : UInt32)
    (config : Config Universal.State) : Prop :=
  (∃ store capacity ptr outLen bytes,
      config = decodeAfterCoreConfig store data ∧
      decode input = some bytes ∧
      store.wasm.mem.read32 decodeResultOut = capacity ∧
      store.wasm.mem.read32 (decodeResultOut + 4) = ptr ∧
      store.wasm.mem.read32 (decodeResultOut + 8) = outLen ∧
      outLen.toNat = bytes.length ∧
      outLen.toNat ≤ capacity.toNat ∧
      capacity.toNat < 2 ^ 31 ∧
      ptr.toNat + outLen.toNat ≤ store.wasm.mem.pages * 65536 ∧
      store.wasm.mem.readBytes ptr.toNat bytes.length = bytes ∧
      ∃ bump, DecodeCoreStoreFacts store bump ∧
        (bytes = [] ∨ (1054000 ≤ ptr.toNat ∧
          ptr.toNat + capacity.toNat = bump.toNat))) ∨
    (∃ store bad,
      config = decodeAfterCoreConfig store data ∧
      decode input = none ∧
      store.wasm.mem.read32 decodeResultOut = 2147483648 ∧
      store.wasm.mem.read32 (decodeResultOut + 4) = bad ∧
      ((input.length % 2 = 1 ∧ bad = 1114112) ∨
        (input.length % 2 = 0 ∧ bad.toNat ≤ 255)) ∧
      ∃ bump, DecodeCoreStoreFacts store bump)

theorem decodeLoopSuccessStore_readBytes_above
    (store : MachineStore Universal.State) (ptr : UInt32)
    (capacity outLen : UInt32) (off count : Nat)
    (habove : 1048564 ≤ off) :
    (decodeLoopSuccessStore store ptr capacity outLen).wasm.mem.readBytes
        off count = store.wasm.mem.readBytes off count := by
  have h0 : decodeResultOut.toNat + 4 = 1048556 := by decide
  have h4 : (decodeResultOut + 4).toNat + 4 = 1048560 := by decide
  have h8 : (decodeResultOut + 8).toNat + 4 = 1048564 := by decide
  simp only [decodeLoopSuccessStore]
  rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  all_goals right
  all_goals omega

theorem decodeInvalidCoreStore_result_tag
    (store : MachineStore Universal.State) (bad index : UInt32) :
    (decodeInvalidCoreStore store bad index).wasm.mem.read32 decodeResultOut =
      2147483648 := by
  simp only [decodeInvalidCoreStore]
  exact Mem.read32_write32_same _ _ _

theorem decodeInvalidCoreStore_result_payload
    (store : MachineStore Universal.State) (bad index : UInt32) :
    (decodeInvalidCoreStore store bad index).wasm.mem.read32
      (decodeResultOut + 4) = bad := by
  simp only [decodeInvalidCoreStore]
  rw [Mem.read32_write32_disjoint]
  · exact Mem.read32_write32_same _ _ _
  · right; decide

theorem decodeLoopSuccessStore_result_fields
    (store : MachineStore Universal.State) (ptr capacity outLen : UInt32) :
    (decodeLoopSuccessStore store ptr capacity outLen).wasm.mem.read32
        decodeResultOut = capacity ∧
    (decodeLoopSuccessStore store ptr capacity outLen).wasm.mem.read32
        (decodeResultOut + 4) = ptr ∧
    (decodeLoopSuccessStore store ptr capacity outLen).wasm.mem.read32
        (decodeResultOut + 8) = outLen := by
  constructor
  · exact Mem.read32_write32_same _ _ _
  constructor
  · simp only [decodeLoopSuccessStore]
    rw [Mem.read32_write32_disjoint]
    · exact Mem.read32_write32_same _ _ _
    · right; decide
  · simp only [decodeLoopSuccessStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint]
    · exact Mem.read32_write32_same _ _ _
    · right; decide
    · right; decide

end Project.HexDecodeStdio
