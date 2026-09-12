import HexEncodeStdio.AllocatorMemoryCost
import HexEncodeStdio.ReallocatorOperational

/-! Initial-state success bridge for byte-aligned hex allocation.
The physical cap remains the generated module's ordinary 65,536 pages.
-/
namespace Project.HexEncodeStdio.AllocatorResourceCost

open Wasm Wasm.SmallStep Project.HexStdio

/-- The arithmetic decision made before constructing an allocation trace. -/
def classifyByteRequest (frontier size : Nat) : Option (UInt32 × UInt32) :=
  if frontier + size < 2147483648 then
    some (UInt32.ofNat frontier, UInt32.ofNat (frontier + size))
  else none

def requiredPages (finish : Nat) : Nat := (65535 + finish) / 65536

def grownMemory (memory : Mem) (finish : Nat) : Mem :=
  { memory with pages := max memory.pages (requiredPages finish) }

def finalStore (store : MachineStore Universal.State) (finish : Nat) : MachineStore Universal.State :=
  allocatorBumpStore (allocatorGrownStore store (grownMemory store.wasm.mem finish))
    (UInt32.ofNat finish)

theorem ptr_one (bump : UInt32) : allocatorPtr bump 1 = allocatorBase bump := by
  simp [allocatorPtr]

theorem finish_toNat (size bump : UInt32) (frontier : Nat)
    (hfrontier : (allocatorBase bump).toNat = frontier)
    (hfit : frontier + size.toNat < 2147483648) :
    (allocatorFinish size 1 bump).toNat = frontier + size.toNat := by
  simp only [allocatorFinish, ptr_one, UInt32.toNat_add, hfrontier]
  rw [Nat.mod_eq_of_lt (by norm_num; omega)]
  omega

theorem required_toNat (size bump : UInt32) (frontier : Nat)
    (hfrontier : (allocatorBase bump).toNat = frontier)
    (hfit : frontier + size.toNat < 2147483648) :
    (allocatorRequiredPages size 1 bump).toNat = requiredPages (frontier + size.toNat) := by
  have hend := finish_toNat size bump frontier hfrontier hfit
  rw [allocatorRequiredPages, UInt32.toNat_shiftRight, UInt32.toNat_add, hend]
  change ((65535 + (frontier + size.toNat)) % 4294967296) >>> 16 = _
  rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  rfl

theorem required_bound (finish : Nat) (hfit : finish < 2147483648) :
    requiredPages finish ≤ 32768 ∧ finish ≤ requiredPages finish * 65536 := by
  unfold requiredPages
  omega

theorem nonnegative (x : UInt32) (h : x.toNat < 2147483648) :
    ¬ x.toInt32 < (0 : UInt32).toInt32 := by
  rw [Int32.lt_iff_toInt_lt]
  have hx : x.toInt32.toInt = x.toNat := by
    apply BitVec.toInt_eq_toNat_of_lt
    change 2 * x.toNat < 2 ^ 32
    omega
  rw [hx, show ((0 : UInt32).toInt32).toInt = 0 by decide]
  omega

/-- The physical grow outcome is derived from the required pages and initial
cap, rather than assumed as a premise of the call certificate. -/
theorem grow_success (store : MachineStore Universal.State) (required : UInt32)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hrequired : required.toNat ≤ 32768)
    (hneed : ¬ required ≤ UInt32.ofNat store.wasm.mem.pages) :
    store.wasm.mem.grow (required - UInt32.ofNat store.wasm.mem.pages)
      (store.wasm.memoryCap store.runtime.currentModule 0) =
      some ({ store.wasm.mem with pages := required.toNat }, store.wasm.mem.pages) := by
  have hpagesWord : store.wasm.mem.pages < UInt32.size := lt_of_le_of_lt hpages (by decide)
  have hpagesNat := UInt32.toNat_ofNat_of_lt' hpagesWord
  have hneedNat : store.wasm.mem.pages < required.toNat := by
    have h := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hneed)
    simpa only [hpagesNat] using h
  have hle : UInt32.ofNat store.wasm.mem.pages ≤ required :=
    UInt32.le_iff_toNat_le.mpr (by rw [hpagesNat]; omega)
  have hdelta : (required - UInt32.ofNat store.wasm.mem.pages).toNat =
      required.toNat - store.wasm.mem.pages := by
    rw [UInt32.toNat_sub_of_le _ _ hle, hpagesNat]
  simp only [Mem.grow, hdelta, Nat.add_sub_of_le (Nat.le_of_lt hneedNat), hcap]
  rw [if_pos (hrequired.trans (by decide))]

/-- Complete actual call15 and original caller resumption, with a precise
post-store and all-prefix page bounds. All premises concern the initial store
and the natural endpoint of this request. -/
theorem allocator_byte_cost (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (size bump : UInt32) (frontier : Nat)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hread : store.wasm.mem.read32 1053960 = bump)
    (hcursor : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfrontier : (allocatorBase bump).toNat = frontier)
    (hfit : frontier + size.toNat < 2147483648) :
    ∃ trace, trace.length = (if requiredPages (frontier + size.toNat) ≤ store.wasm.mem.pages then 49 else 56) ∧
      CostedSteps CostedStdIO.work
        (AllocatorMemoryCost.callConfig store params localValues stack code arity remainder controls calls size 1)
        trace
        (AllocatorMemoryCost.returnConfig (finalStore store (frontier + size.toNat))
          params localValues stack code arity remainder controls calls (UInt32.ofNat frontier))
        (trace.length + 65536 * (requiredPages (frontier + size.toNat) - store.wasm.mem.pages)) ∧
      (∀ prefixTrace middle,
        Steps (AllocatorMemoryCost.callConfig store params localValues stack code arity remainder controls calls size 1)
          prefixTrace middle → prefixTrace.length ≤ trace.length →
        store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
          middle.store.wasm.mem.pages ≤ max store.wasm.mem.pages (requiredPages (frontier + size.toNat))) ∧
      ∀ kind ∈ trace, PrimaryMemoryKind kind := by
  have hfinishNat := finish_toNat size bump frontier hfrontier hfit
  have hrequired := required_toNat size bump frontier hfrontier hfit
  have hfinishWord : allocatorFinish size 1 bump = UInt32.ofNat (frontier + size.toNat) := by
    rw [← hfinishNat, UInt32.ofNat_toNat]
  have hptr : allocatorPtr bump 1 = UInt32.ofNat frontier := by
    rw [ptr_one, ← hfrontier, UInt32.ofNat_toNat]
  have hfirst : ¬ allocatorBase bump + ((0xffffffff : UInt32) + 1) < (0xffffffff : UInt32) + 1 := by simp
  have hsecond : ¬ allocatorFinish size 1 bump < allocatorPtr bump 1 := by
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le, hfinishNat, ptr_one, hfrontier]
    omega
  have hnegative := nonnegative (allocatorFinish size 1 bump) (by rw [hfinishNat]; exact hfit)
  have hpagesNat := UInt32.toNat_ofNat_of_lt' (lt_of_le_of_lt hpages (by decide : Module.memoryHardCap < UInt32.size))
  have hcompare : allocatorRequiredPages size 1 bump ≤ UInt32.ofNat store.wasm.mem.pages ↔
      requiredPages (frontier + size.toNat) ≤ store.wasm.mem.pages := by
    rw [UInt32.le_iff_toNat_le, hrequired, hpagesNat]
  by_cases henough : requiredPages (frontier + size.toNat) ≤ store.wasm.mem.pages
  · obtain ⟨trace, hlength, labels, steps⟩ := allocator_no_grow_steps_trace
      store params localValues stack code arity remainder controls calls size 1 bump hmodule
      hread hcursor hfirst hsecond hnegative (hcompare.mpr henough)
    have run := steps.growth_byteWork labels CostedStdIO.hostBytes
    refine ⟨trace, by rw [if_pos henough]; exact hlength, ?_, ?_, fun kind member => (labels kind member).primary⟩
    · simpa only [AllocatorMemoryCost.callConfig,AllocatorMemoryCost.returnConfig,
        List.cons_append,List.nil_append,CostedStdIO.work,finalStore, grownMemory, max_eq_left henough, allocatorGrownStore,
        hlength, Nat.sub_eq_zero_of_le henough, Nat.mul_zero, Nat.add_zero, hptr, hfinishWord,
        allocatorBumpStore,Mem.write32_pages,Nat.sub_self] using run
    · intro prefixTrace middle first bound
      have hp := steps.primary_pages_at_prefix first bound (fun kind member => (labels kind member).primary)
      simpa only [allocatorBumpStore,Mem.write32_pages,max_eq_left henough] using hp
  · have hneed := fun h => henough (hcompare.mp h)
    have hrequiredBound : (allocatorRequiredPages size 1 bump).toNat ≤ 32768 := by
      rw [hrequired]; exact (required_bound _ hfit).1
    have hgrow := grow_success store (allocatorRequiredPages size 1 bump) hcap hpages hrequiredBound hneed
    have hbefore : store.wasm.mem.pages ≤ (allocatorRequiredPages size 1 bump).toNat := by rw [hrequired]; omega
    have hresult : store.wasm.mem.pages.toUInt32 ≠ (0xffffffff : UInt32) := by
      intro hz
      have hh := congrArg UInt32.toNat hz
      rw [hpagesNat] at hh
      have : store.wasm.mem.pages ≤ 65536 := hpages
      change store.wasm.mem.pages = 4294967295 at hh
      omega
    obtain ⟨trace, hlength, labels, steps⟩ := allocator_grow_success_steps_trace
      store params localValues stack code arity remainder controls calls size 1 bump
      { store.wasm.mem with pages := (allocatorRequiredPages size 1 bump).toNat } store.wasm.mem.pages
      hmodule hread hcursor (hcursor.trans (Nat.mul_le_mul_right 65536 hbefore))
      hfirst hsecond hnegative hneed hgrow hresult
    have run := steps.growth_byteWork labels CostedStdIO.hostBytes
    refine ⟨trace, by rw [if_neg henough]; exact hlength, ?_, ?_, fun kind member => (labels kind member).primary⟩
    · simpa only [AllocatorMemoryCost.callConfig,AllocatorMemoryCost.returnConfig,
        List.cons_append,List.nil_append,CostedStdIO.work,finalStore, grownMemory, max_eq_right (Nat.le_of_not_ge henough),
        hrequired, hlength, hfinishWord, hptr,allocatorBumpStore,allocatorGrownStore,Mem.write32_pages] using run
    · intro prefixTrace middle first bound
      have hp := steps.primary_pages_at_prefix first bound (fun kind member => (labels kind member).primary)
      simpa only [hrequired,max_eq_right (Nat.le_of_not_ge henough),allocatorBumpStore,
        allocatorGrownStore,Mem.write32_pages] using hp

theorem classify_success (frontier size : Nat) (base finish : UInt32)
    (h : classifyByteRequest frontier size = some (base, finish)) :
    frontier + size < 2147483648 ∧ base = UInt32.ofNat frontier ∧
      finish = UInt32.ofNat (frontier + size) := by
  unfold classifyByteRequest at h
  split at h
  · have heq := Option.some.inj h
    exact ⟨by assumption, (Prod.mk.inj heq).1.symm, (Prod.mk.inj heq).2.symm⟩
  · contradiction

/-- Classifier form of the actual call certificate; no physical grow-success
premise or assumed future allocator execution remains. -/
theorem allocator_classified_cost (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (size bump : UInt32) (frontier : Nat) (base finish : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hread : store.wasm.mem.read32 1053960 = bump)
    (hcursor : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfrontier : (allocatorBase bump).toNat = frontier)
    (hclassify : classifyByteRequest frontier size.toNat = some (base, finish)) :
    ∃ trace, trace.length = (if requiredPages finish.toNat ≤ store.wasm.mem.pages then 49 else 56) ∧
      CostedSteps CostedStdIO.work
        (AllocatorMemoryCost.callConfig store params localValues stack code arity remainder controls calls size 1)
        trace
        (AllocatorMemoryCost.returnConfig (finalStore store finish.toNat)
          params localValues stack code arity remainder controls calls base)
        (trace.length + 65536 * (requiredPages finish.toNat - store.wasm.mem.pages)) ∧
      ∀ prefixTrace middle,
        Steps (AllocatorMemoryCost.callConfig store params localValues stack code arity remainder controls calls size 1)
          prefixTrace middle → prefixTrace.length ≤ trace.length →
        store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
          middle.store.wasm.mem.pages ≤ max store.wasm.mem.pages (requiredPages finish.toNat) := by
  obtain ⟨hfit, rfl, rfl⟩ := classify_success frontier size.toNat base finish hclassify
  have hend : frontier + size.toNat < UInt32.size := by norm_num [UInt32.size]; omega
  obtain ⟨trace, hlength, run, hpref, _⟩ :=
    allocator_byte_cost store params localValues stack code arity remainder controls calls
      size bump frontier hmodule hcap hpages hread hcursor hfrontier hfit
  refine ⟨trace, ?_⟩
  simpa only [UInt32.toNat_ofNat_of_lt' hend] using ⟨hlength,run,hpref⟩

@[simp] theorem finalStore_pages (store : MachineStore Universal.State) (finish : Nat) :
    (finalStore store finish).wasm.mem.pages = max store.wasm.mem.pages (requiredPages finish) := rfl

@[simp] theorem finalStore_cursor (store : MachineStore Universal.State) (finish : Nat) :
    (finalStore store finish).wasm.mem.read32 1053960 = UInt32.ofNat finish :=
  Mem.read32_write32_same _ _ _

theorem finalStore_cover (store : MachineStore Universal.State) (finish : Nat)
    (hfit : finish < 2147483648) :
    finish ≤ (finalStore store finish).wasm.mem.pages * 65536 :=
  (required_bound finish hfit).2.trans (Nat.mul_le_mul_right 65536 (Nat.le_max_right _ _))

theorem finalStore_frame (store : MachineStore Universal.State) (finish : Nat) :
    (finalStore store finish).runtime = store.runtime ∧
    (finalStore store finish).wasm.globals = store.wasm.globals ∧
    (finalStore store finish).wasm.host = store.wasm.host ∧
    (finalStore store finish).wasm.memoryCaps = store.wasm.memoryCaps ∧
    (finalStore store finish).wasm.globalIds = store.wasm.globalIds ∧
    (finalStore store finish).wasm.memoryIds = store.wasm.memoryIds :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Project.HexEncodeStdio.AllocatorResourceCost
