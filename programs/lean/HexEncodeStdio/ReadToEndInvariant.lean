import HexEncodeStdio.ReadToEndStoreFacts
import HexEncodeStdio.EncodePrefixOperational
import HexEncodeStdio.Hex

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Pure arithmetic facts used by the recursive `read_to_end` invariant.  The
allocator is byte-aligned here, so after its distinguished initial bump the
next allocation begins exactly at the previous bump. -/

theorem allocatorPtr_one_eq (bump : UInt32) (hne : bump ≠ 0) :
    allocatorPtr bump 1 = bump := by
  simp [allocatorPtr, allocatorBase, hne]

theorem allocatorFinish_one_eq (size bump : UInt32) (hne : bump ≠ 0) :
    allocatorFinish size 1 bump = size + bump := by
  simp [allocatorFinish, allocatorPtr_one_eq bump hne]

theorem allocatorFinish_one_eq_comm (size bump : UInt32) (hne : bump ≠ 0) :
    allocatorFinish size 1 bump = bump + size := by
  rw [allocatorFinish_one_eq size bump hne]
  exact UInt32.add_comm _ _

theorem readToEndNewCapacity_toNat (capacity : UInt32)
    (hsmall : 2 * capacity.toNat + 32 < 2 ^ 31) :
    (readToEndNewCapacity capacity).toNat =
      max (capacity.toNat + 32) (2 * capacity.toNat) := by
  have hshift : (capacity <<< 1).toNat = 2 * capacity.toNat := by
    simp only [UInt32.toNat_shiftLeft, UInt32.reduceToNat]
    norm_num [Nat.shiftLeft_eq]
    omega
  have hadd : ((32 : UInt32) + capacity).toNat = 32 + capacity.toNat := by
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
    omega
  simp only [readToEndNewCapacity]
  split
  case isTrue h =>
    have hn := UInt32.lt_iff_toNat_lt.mp h
    rw [hshift, hadd] at hn
    rw [hadd, max_eq_left (by omega)]
    omega
  case isFalse h =>
    have hn : ((32 : UInt32) + capacity).toNat ≤
        (capacity <<< 1).toNat := by
      by_contra hn
      apply h
      apply UInt32.lt_iff_toNat_lt.mpr
      omega
    rw [hshift, hadd] at hn
    rw [hshift, max_eq_right (by omega)]

theorem readToEndNewCapacity_gt (capacity : UInt32)
    (hsmall : 2 * capacity.toNat + 32 < 2 ^ 31) :
    capacity.toNat < (readToEndNewCapacity capacity).toNat := by
  rw [readToEndNewCapacity_toNat capacity hsmall]
  exact lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)

theorem readToEndNewCapacity_le (capacity : UInt32)
    (hsmall : 2 * capacity.toNat + 32 < 2 ^ 31) :
    (readToEndNewCapacity capacity).toNat ≤
      2 * capacity.toNat + 32 := by
  rw [readToEndNewCapacity_toNat capacity hsmall]
  apply max_le
  · omega
  · omega

theorem readToEndNewCapacity_nonnegative (capacity : UInt32)
    (hsmall : 2 * capacity.toNat + 32 < 2 ^ 31) :
    ¬(readToEndNewCapacity capacity).toInt32 < (0 : UInt32).toInt32 := by
  apply UInt32.toInt32_not_negative_of_small
  rw [readToEndNewCapacity_toNat capacity hsmall]
  exact max_lt (by omega) (by omega)

theorem readToEndNewCapacity_ne_zero (capacity : UInt32)
    (hsmall : 2 * capacity.toNat + 32 < 2 ^ 31) :
    readToEndNewCapacity capacity ≠ 0 := by
  intro hz
  have := congrArg UInt32.toNat hz
  rw [readToEndNewCapacity_toNat capacity hsmall] at this
  simp at this

theorem Mem.grow_success_pages_le (mem memory : Mem) (delta : UInt32)
    (cap previous : Nat)
    (h : mem.grow delta cap = some (memory, previous)) :
    memory.pages ≤ cap := by
  simp only [Mem.grow] at h
  split at h
  next hle =>
    have heq := congrArg (fun pair => pair.1.pages) (Option.some.inj h)
    have heq' : memory.pages = mem.pages + delta.toNat := by
      simpa using heq.symm
    omega
  next => contradiction

theorem Mem.read32_copy_before (mem : Mem) (destination source length : Nat)
    (address : UInt32) (hbefore : address.toNat + 4 ≤ destination) :
    (mem.copy destination source length).read32 address = mem.read32 address := by
  simp only [Mem.read32, Mem.copy]
  rw [if_neg, if_neg, if_neg, if_neg]
  all_goals omega

@[simp] theorem allocatorBumpStore_memoryCap
    (store : MachineStore Universal.State) (finish : UInt32)
    (m : Module) (index : Nat) :
    (allocatorBumpStore store finish).wasm.memoryCap m index =
      store.wasm.memoryCap m index := by
  rfl

@[simp] theorem allocatorGrownStore_memoryCap
    (store : MachineStore Universal.State) (memory : Mem)
    (m : Module) (index : Nat) :
    (allocatorGrownStore store memory).wasm.memoryCap m index =
      store.wasm.memoryCap m index := by
  rfl

theorem ByteGrowSuccess.memoryCap_eq
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (m : Module) (index : Nat) :
    final.wasm.memoryCap m index = store.wasm.memoryCap m index := by
  cases h with
  | freshNoGrow => rfl
  | freshGrow => rfl
  | reallocNoGrow =>
      simp only [reallocatorResultStore]
      split <;> rfl
  | reallocGrow =>
      simp only [reallocatorResultStore]
      split <;> rfl

theorem ByteGrowSuccess.pages_le_cap
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536)
    (hpages : store.wasm.mem.pages ≤ 65536) :
    final.wasm.mem.pages ≤ 65536 := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative =>
      simpa [allocatorBumpStore] using hpages
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative =>
      have hm := Mem.grow_success_pages_le _ _ _ _ _ hgrow
      rw [hcap] at hm
      simpa [allocatorBumpStore, allocatorGrownStore] using hm
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore]
      split <;> simpa [allocatorBumpStore, Mem.copy] using hpages
  | reallocGrow hnonzero memory previousPages hgrow =>
      have hm := Mem.grow_success_pages_le _ _ _ _ _ hgrow
      rw [hcap] at hm
      simp only [reallocatorResultStore]
      split <;>
        simpa [allocatorBumpStore, allocatorGrownStore, Mem.copy] using hm

theorem ByteGrowSuccess.host_eq
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final) :
    final.wasm.host = store.wasm.host := by
  cases h with
  | freshNoGrow => rfl
  | freshGrow => rfl
  | reallocNoGrow =>
      simp only [reallocatorResultStore]
      split <;> rfl
  | reallocGrow =>
      simp only [reallocatorResultStore]
      split <;> rfl

theorem ByteGrowSuccess.read_bump
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (hbefore : 1053960 + 4 ≤ (allocatorPtr oldBump 1).toNat) :
    final.wasm.mem.read32 1053960 =
      allocatorFinish newCapacity 1 oldBump := by
  cases h with
  | freshNoGrow => simp [allocatorBumpStore]
  | freshGrow => simp [allocatorBumpStore, allocatorGrownStore]
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore]
      split
      · simp [allocatorBumpStore]
      · rw [Mem.read32_copy_before _ _ _ _ _ hbefore]
        simp [allocatorBumpStore]
  | reallocGrow hnonzero memory previousPages hgrow =>
      simp only [reallocatorResultStore]
      split
      · simp [allocatorBumpStore, allocatorGrownStore]
      · rw [Mem.read32_copy_before _ _ _ _ _ hbefore]
        simp [allocatorBumpStore, allocatorGrownStore]

def encodeAfterReadConfig (store : MachineStore Universal.State) :
    Config Universal.State :=
  { expr := .running
      ⟨⟨[], [.i32 1048544, .i32 0, .i32 0, .i32 0], []⟩,
        Project.HexStdio.func10.drop 9, 0, [], [], []⟩
    store := store }

abbrev encodeLocals : List Value :=
  [.i32 1048544, .i32 0, .i32 0, .i32 0]

def encodeReadLoopConfig (store : MachineStore Universal.State)
    (chunk capacity data length filled : UInt32) : Config Universal.State :=
  readToEndLoopConfig store [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] [] []
    1048564 readToEndStack chunk capacity data length filled

def encodeReadContinuedConfig (store : MachineStore Universal.State)
    (chunk capacity data length filled previousCount previousTarget
      previousBase previousSpare : UInt32) : Config Universal.State :=
  readToEndContinuedLoopConfig store [] encodeLocals [] (Project.HexStdio.func10.drop 9) 0 [] []
    [] 1048564 readToEndStack chunk capacity data length filled
    previousCount previousTarget previousBase previousSpare

/-- The semantic content of the generated `read_to_end` loop.  `prefix` is
the initialized vector prefix and `remaining` is precisely the unread host
suffix.  The allocator equations make successful growth strong enough to
re-establish the invariant without remembering its entire allocation history. -/
structure ReadToEndInv (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (capacity data length bump : UInt32) : Prop where
  split : consumed ++ remaining = input
  input_eq : store.wasm.host.stdio.input = remaining
  output_eq : store.wasm.host.stdio.output = []
  oom_eq : store.wasm.host.oom.raised = false
  runtime_entry : store.runtime.entry = ⟨0⟩
  runtime_module : store.runtime.currentModule = «module»
  runtime_host : store.runtime.currentHost = Universal.envFor «module»
  memory_cap : store.wasm.memoryCap store.runtime.currentModule 0 = 65536
  pages_lower : 17 ≤ store.wasm.mem.pages
  pages_upper : store.wasm.mem.pages ≤ 65536
  global_eq : globalAt? store 0 = some (.i32 readToEndStack)
  capacity_eq : store.wasm.mem.read32 (readToEndStack + 4) = capacity
  data_eq : store.wasm.mem.read32 (readToEndStack + 8) = data
  length_eq : store.wasm.mem.read32 (readToEndStack + 12) = length
  bump_eq : store.wasm.mem.read32 1053960 = bump
  table_eq : store.wasm.mem.readBytes 1048576 16 = Submission.Hex.asciiTable
  bytes_eq : store.wasm.mem.readBytes data.toNat consumed.length = consumed
  length_nat : length.toNat = consumed.length
  length_le_capacity : length.toNat ≤ capacity.toNat
  capacity_pos : 0 < capacity.toNat
  capacity_min : 8 ≤ capacity.toNat
  data_lower : 1054000 ≤ data.toNat
  data_capacity_bump : data.toNat + capacity.toNat = bump.toNat
  capacity_headroom : 2 * capacity.toNat + 32 ≤ bump.toNat
  bump_signed : bump.toNat < 2 ^ 31
  data_bound : data.toNat + capacity.toNat ≤ store.wasm.mem.pages * 65536

theorem ReadToEndInv.capacity_small
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    2 * capacity.toNat + 32 < 2 ^ 31 := by
  exact lt_of_le_of_lt h.capacity_headroom h.bump_signed

theorem ReadToEndInv.bump_ne_zero
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    bump ≠ 0 := by
  intro hz
  have hb := h.capacity_headroom
  rw [hz] at hb
  simp at hb

theorem ReadToEndInv.newCapacity_le_bump
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (readToEndNewCapacity capacity).toNat ≤ bump.toNat := by
  calc
    (readToEndNewCapacity capacity).toNat ≤
        2 * capacity.toNat + 32 :=
      readToEndNewCapacity_le capacity h.capacity_small
    _ ≤ bump.toNat := h.capacity_headroom

theorem ReadToEndInv.allocator_ptr
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    allocatorPtr bump 1 = bump :=
  allocatorPtr_one_eq bump h.bump_ne_zero

theorem ReadToEndInv.newCapacity_ne_zero
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    readToEndNewCapacity capacity ≠ 0 :=
  readToEndNewCapacity_ne_zero capacity h.capacity_small

theorem ReadToEndInv.copy_length
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    reallocatorCopyLen capacity (readToEndNewCapacity capacity) = capacity := by
  simp only [reallocatorCopyLen]
  rw [if_neg]
  intro hlt
  have hn := UInt32.lt_iff_toNat_lt.mp hlt
  have hgrow := readToEndNewCapacity_gt capacity h.capacity_small
  omega

theorem ReadToEndInv.finish_toNat
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat =
      bump.toNat + (readToEndNewCapacity capacity).toNat := by
  rw [allocatorFinish_one_eq_comm _ _ h.bump_ne_zero]
  simp only [UInt32.toNat_add]
  have hnew := h.newCapacity_le_bump
  have hsize : bump.toNat + (readToEndNewCapacity capacity).toNat <
      2 ^ 32 := by
    have hb := h.bump_signed
    norm_num at hb ⊢
    omega
  omega

theorem ReadToEndInv.allocator_first_ok
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    ¬allocatorBase bump + ((0xffffffff : UInt32) + 1) <
      (0xffffffff : UInt32) + 1 := by
  simp [allocatorBase, h.bump_ne_zero]

theorem ReadToEndInv.allocator_second_ok
    {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State}
    {capacity data length bump : UInt32}
    (h : ReadToEndInv input consumed remaining store capacity data length bump) :
    ¬allocatorFinish (readToEndNewCapacity capacity) 1 bump <
      allocatorPtr bump 1 := by
  rw [h.allocator_ptr]
  intro hlt
  have hn := UInt32.lt_iff_toNat_lt.mp hlt
  rw [h.finish_toNat] at hn
  omega

def ReadToEndSuccess (input : List UInt8)
    (config : Config Universal.State) : Prop :=
  ∃ store capacity data bump,
    config = encodeAfterReadConfig store ∧
    store.wasm.host.stdio.input = [] ∧
    store.wasm.host.stdio.output = [] ∧
    store.wasm.host.oom.raised = false ∧
    store.runtime.entry = ⟨0⟩ ∧
    store.runtime.currentModule = «module» ∧
    store.runtime.currentHost = Universal.envFor «module» ∧
    store.wasm.memoryCap store.runtime.currentModule 0 = 65536 ∧
    store.wasm.mem.pages ≤ 65536 ∧
    globalAt? store 0 = some (.i32 1048544) ∧
    store.wasm.mem.read32 1048564 = capacity ∧
    store.wasm.mem.read32 (1048564 + 4) = data ∧
    store.wasm.mem.read32 (1048564 + 8) =
      UInt32.ofNat input.length ∧
    store.wasm.mem.read32 1053960 = bump ∧
    store.wasm.mem.readBytes 1048576 16 = Submission.Hex.asciiTable ∧
    store.wasm.mem.readBytes data.toNat input.length = input ∧
    input.length ≤ capacity.toNat ∧
    8 ≤ capacity.toNat ∧
    2 * capacity.toNat + 32 < 2 ^ 31 ∧
    1054000 ≤ data.toNat ∧
    data.toNat + capacity.toNat = bump.toNat ∧
    bump.toNat < 2 ^ 31 ∧
    data.toNat + capacity.toNat ≤ store.wasm.mem.pages * 65536

end Submission.HexDecodeStdio
