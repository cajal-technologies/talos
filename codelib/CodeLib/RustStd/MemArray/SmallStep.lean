import CodeLib.RustStd.MemArray
import CodeLib.SepLogic.SmallStepAdequacy

/-! Small-step ownership facts for consecutive memory arrays. -/

namespace Wasm.SepLogic

open Iris Std
open Wasm Wasm.SmallStep

/-- Walking `arrayAt` ownership reads back exactly its sequence of `u32` words. -/
theorem arrayAt_readWords32 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat) (obs : List StepKind) (threads : Nat)
    (base : UInt32) (output : List UInt32)
    (hfit : base.toNat + 4 * output.length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps obs threads ∗ arrayAt 0 base output ==∗
      stateInterp (GF := WasmHeapGF α) store steps obs threads ∗ arrayAt 0 base output ∗
      ⌜store.wasm.mem.readWords32 base output.length = output⌝ := by
  induction output generalizing base with
  | nil =>
    simp only [arrayAt, List.length_nil, Mem.readWords32]
    iintro ⟨Hstate, Hemp⟩
    imodintro
    isplitl_exacts [Hstate Hemp]
    ipureintro; trivial
  | cons x xs ih =>
    simp only [arrayAt, List.length_cons]
    simp only [List.length_cons, UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    have hfit' : (base + 4).toNat + 4 * xs.length ≤ UInt32.size := by
      simp only [UInt32.size]; omega
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    iintro ⟨Hstate, Hword, Hxs⟩
    imod stateInterp_pointsTo_u32_facts_frame store steps obs threads base x
      h1 h2 h3 $$ [$Hstate $Hword] with ⟨Hstate, Hword, %hfacts⟩
    imod ih (base + 4) hfit' $$ [$Hstate $Hxs] with ⟨Hstate, Hxs, %hread⟩
    imodintro
    isplitl_exact Hstate
    isplitl [Hword Hxs]
    · isplitl_exact Hword; iexact Hxs
    ipureintro
    simp only [Mem.readWords32, hfacts.1, hread]

/-- Ghost heap for a sequence of `u64` values at `base`, built by stamping 8-byte ghost cells. -/
def heap64Aux (heap : WasmHeapMap (Option UInt8)) (base : UInt32) :
    List UInt64 → WasmHeapMap (Option UInt8)
  | [] => heap
  | value :: values => heap64Aux (store64Heap heap 0 base value) (base + 8) values

theorem heap64Aux_agrees
    (heap : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32)
    (values : List UInt64)
    (hagree : heapAgreesWithMem heap (fun id => if id = 0 then some mem else none))
    (hfit : base.toNat + 8 * values.length < UInt32.size) :
    heapAgreesWithMem (heap64Aux heap base values)
      (fun id => if id = 0 then some (Mem.writeWords64 mem base values) else none) := by
  induction values generalizing heap mem base with
  | nil => simpa [heap64Aux, Mem.writeWords64]
  | cons value values ih =>
      simp only [heap64Aux, Mem.writeWords64, List.length_cons] at *
      simp only [UInt32.size] at hfit
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 base (by omega)
      apply ih
      · exact store64_sound0 heap mem base value h1 h2 h3 h4 h5 h6 h7 hagree
      · have h8 : (base + 8 : UInt32).toNat = base.toNat + 8 :=
          UInt32.add_ofNat_toNat_noWrap base 8 (by decide) (by omega)
        rw [h8]
        simp only [UInt32.size]; omega

theorem heap64Aux_inBounds
    (heap : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32)
    (values : List UInt64)
    (hinBounds : heapAddressesInBounds heap (fun id => if id = 0 then some mem else none))
    (hfit : base.toNat + 8 * values.length < UInt32.size)
    (hmem : base.toNat + 8 * values.length ≤ mem.pages * 65536) :
    heapAddressesInBounds (heap64Aux heap base values)
      (fun id => if id = 0 then some (Mem.writeWords64 mem base values) else none) := by
  induction values generalizing heap mem base with
  | nil => simpa [heap64Aux, Mem.writeWords64]
  | cons value values ih =>
      simp only [heap64Aux, Mem.writeWords64, List.length_cons] at *
      simp only [UInt32.size] at hfit
      have h8 : (base + 8 : UInt32).toNat = base.toNat + 8 :=
        UInt32.add_ofNat_toNat_noWrap base 8 (by decide) (by omega)
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 base (by omega)
      apply ih
      · exact store64_inBounds0 heap mem base value h1 h2 h3 h4 h5 h6 h7
          (by omega) hinBounds
      · rw [h8]
        simp only [UInt32.size]; omega
      · have : (mem.write64 base value).pages = mem.pages := rfl
        rw [h8, this]; omega

set_option maxHeartbeats 6000000 in
/-- Ownership of `heap64Aux heap base values` entails `array64At 0 base values`
plus ownership of the original `heap`. Generalized to any ghost heap type `α`. -/
theorem heap64Aux_pointsTo {α : Type} [WasmHeapGS α]
    (heap : WasmHeapMap (Option UInt8)) (base : UInt32)
    (values : List UInt64)
    (hdisjoint : ∀ address byte, get? heap address = some byte →
      address.addr.toNat < base.toNat)
    (hfit : base.toNat + 8 * values.length < UInt32.size) :
    ([∗map] address ↦ value ∈ heap64Aux heap base values,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      array64At 0 base values ∗
      ([∗map] address ↦ value ∈ heap,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) value) := by
  induction values generalizing heap base with
  | nil =>
      simp only [heap64Aux, array64At, BI.emp_sep.to_eq]
      iintro Hheap; iexact Hheap
  | cons value values ih =>
      simp only [heap64Aux, List.length_cons] at *
      simp only [UInt32.size] at hfit
      have hn (n : Nat) (hn : n ≤ 8) :
          (base + UInt32.ofNat n).toNat = base.toNat + n := by
        apply UInt32.add_ofNat_toNat_noWrap base n
        · omega
        · omega
      have hn8 := hn 8 (by omega)
      obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
        UInt32.addSteps8 base (by omega)
      have hget (n : Nat) (hnle : n < 8) :
          get? heap ⟨0, base + UInt32.ofNat n⟩ = none := by
        by_contra h
        obtain ⟨byte, hbyte⟩ := Option.ne_none_iff_exists.mp h
        have hlt := hdisjoint _ _ hbyte.symm
        simp only [] at hlt
        rw [hn n (by omega)] at hlt; omega
      have hget0 : get? heap ⟨0, base⟩ = none := by simpa using hget 0 (by omega)
      have hget1 := hget 1 (by omega)
      have hget2 := hget 2 (by omega)
      have hget3 := hget 3 (by omega)
      have hget4 := hget 4 (by omega)
      have hget5 := hget 5 (by omega)
      have hget6 := hget 6 (by omega)
      have hget7 := hget 7 (by omega)
      have hgetL1 : get? heap ⟨0, base + 1⟩ = none := by simpa using hget1
      have hgetL2 : get? heap ⟨0, base + 2⟩ = none := by simpa using hget2
      have hgetL3 : get? heap ⟨0, base + 3⟩ = none := by simpa using hget3
      have hgetL4 : get? heap ⟨0, base + 4⟩ = none := by simpa using hget4
      have hgetL5 : get? heap ⟨0, base + 5⟩ = none := by simpa using hget5
      have hgetL6 : get? heap ⟨0, base + 6⟩ = none := by simpa using hget6
      have hgetL7 : get? heap ⟨0, base + 7⟩ = none := by simpa using hget7
      have hne (i j : Nat) (hi : i ≤ 7) (hj : j ≤ 7) (hij : i ≠ j) :
          (⟨0, base + UInt32.ofNat i⟩ : MemoryKey) ≠ ⟨0, base + UInt32.ofNat j⟩ := by
        intro heq
        have heq' := congrArg MemoryKey.addr heq
        simp only [] at heq'
        have heq'' := congrArg UInt32.toNat heq'
        rw [hn i (by omega), hn j (by omega)] at heq''; omega
      have hneU (i j : UInt32) (hi : i.toNat ≤ 7) (hj : j.toNat ≤ 7)
          (hij : i ≠ j) : (⟨0, base + i⟩ : MemoryKey) ≠ ⟨0, base + j⟩ := by
        simpa only [UInt32.ofNat_toNat] using
          hne i.toNat j.toNat hi hj (fun h => hij (UInt32.toNat_inj.mp h))
      have hbaseNe (n : UInt32) (hn : n.toNat ≤ 7) (hpos : 0 < n.toNat) :
          (⟨0, base⟩ : MemoryKey) ≠ ⟨0, base + n⟩ := by
        have h := hneU 0 n (by decide) hn (by
          intro heq
          have := congrArg UInt32.toNat heq
          exact hpos.ne' this.symm)
        simpa using h
      have hdisjoint' : ∀ address byte,
          get? (store64Heap heap 0 base value) address = some byte →
          address.addr.toNat < (base + 8).toNat := by
        intro address byte haddress
        change address.addr.toNat < (base + UInt32.ofNat 8).toNat
        rw [hn8]
        by_cases h7 : address = ⟨0, base + 7⟩
        · subst address; simp only []; rw [hl7]; omega
        by_cases h6 : address = ⟨0, base + 6⟩
        · subst address; simp only []; rw [hl6]; omega
        by_cases h5 : address = ⟨0, base + 5⟩
        · subst address; simp only []; rw [hl5]; omega
        by_cases h4 : address = ⟨0, base + 4⟩
        · subst address; simp only []; rw [hl4]; omega
        by_cases h3 : address = ⟨0, base + 3⟩
        · subst address; simp only []; rw [hl3]; omega
        by_cases h2 : address = ⟨0, base + 2⟩
        · subst address; simp only []; rw [hl2]; omega
        by_cases h1 : address = ⟨0, base + 1⟩
        · subst address; simp only []; rw [hl1]; omega
        by_cases h0 : address = ⟨0, base⟩
        · subst address; simp only []; omega
        simp only [store64Heap, get?_insert_ne (Ne.symm h7),
          get?_insert_ne (Ne.symm h6), get?_insert_ne (Ne.symm h5),
          get?_insert_ne (Ne.symm h4), get?_insert_ne (Ne.symm h3),
          get?_insert_ne (Ne.symm h2), get?_insert_ne (Ne.symm h1),
          get?_insert_ne (Ne.symm h0)] at haddress
        have hlt := hdisjoint address byte haddress
        omega
      have hfit' : (base + 8).toNat + 8 * values.length < UInt32.size := by
        change (base + UInt32.ofNat 8).toNat + 8 * values.length < UInt32.size
        rw [hn8]
        simp only [UInt32.size]; omega
      iintro Hheap
      ihave ⟨Hvalues, Hstored⟩ := ih (store64Heap heap 0 base value) (base + 8)
        hdisjoint' hfit' $$ Hheap
      ihave ⟨Hword, Hheap⟩ := store64Heap_pointsTo heap 0 base value
        hget0
        (by simpa only [get?_insert_ne (hbaseNe 1 (by decide) (by decide))]
          using hgetL1)
        (by
          simp only [get?_insert_ne (hneU 1 2 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 2 (by decide) (by decide))]
          exact hgetL2)
        (by
          simp only [get?_insert_ne (hneU 2 3 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 3 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 3 (by decide) (by decide))]
          exact hgetL3)
        (by
          simp only [get?_insert_ne (hneU 3 4 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 4 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 4 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 4 (by decide) (by decide))]
          exact hgetL4)
        (by
          simp only [get?_insert_ne (hneU 4 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 3 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 5 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 5 (by decide) (by decide))]
          exact hgetL5)
        (by
          simp only [get?_insert_ne (hneU 5 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 4 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 3 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 6 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 6 (by decide) (by decide))]
          exact hgetL6)
        (by
          simp only [get?_insert_ne (hneU 6 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 5 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 4 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 3 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 2 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hneU 1 7 (by decide) (by decide) (by decide)),
            get?_insert_ne (hbaseNe 7 (by decide) (by decide))]
          exact hgetL7) $$ Hstored
      simp only [array64At]
      isplitl [Hword Hvalues]
      · isplitl_exact Hword
        · iexact Hvalues
      · iexact Hheap

/-- Walking `array64At` ownership reads back exactly the sequence of `u64` words. -/
theorem array64At_words [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat) (obs : List StepKind)
    (threads : Nat) (base : UInt32) (output : List UInt64)
    (hfit : base.toNat + 8 * output.length < UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps obs threads ∗
      array64At 0 base output ==∗
    stateInterp (GF := WasmHeapGF α) store steps obs threads ∗
      array64At 0 base output ∗
      ⌜Mem.readWords64 store.wasm.mem base output.length = output⌝ := by
  induction output generalizing base with
  | nil =>
      simp only [array64At, List.length_nil, Mem.readWords64]
      iintro ⟨Hstate, Hempty⟩
      imodintro
      isplitl_exacts [Hstate Hempty]
      · ipureintro; trivial
  | cons value output ih =>
      simp only [array64At, List.length_cons] at *
      have hroom : base.toNat + 8 ≤ 4294967296 := by
        simp only [UInt32.size] at hfit; omega
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 base hroom
      have h8 : (base + 8).toNat = base.toNat + 8 :=
        UInt32.add_ofNat_toNat_noWrap base 8 (by decide) (by
          simp only [UInt32.size] at hfit ⊢; omega)
      iintro ⟨Hstate, Hword, Houtput⟩
      imod stateInterp_pointsTo_u64_facts_frame store steps obs threads
        base value h1 h2 h3 h4 h5 h6 h7 $$
        [$Hstate $Hword] with ⟨Hstate, Hword, %hword⟩
      have hfit' : (base + 8).toNat + 8 * output.length < UInt32.size := by
        rw [h8]
        simp only [UInt32.size] at hfit ⊢; omega
      imod ih (base + 8) hfit' $$ [$Hstate $Houtput] with
        ⟨Hstate, Houtput, %hrest⟩
      imodintro
      isplitl_exact Hstate
      isplitl [Hword Houtput]
      · isplitl_exact Hword
        · iexact Houtput
      · ipureintro
        simp only [Mem.readWords64]
        rw [hword.1]; exact congrArg (value :: ·) hrest

/-- `array64At` ownership implies the array fits within the memory page. -/
theorem array64At_capacity [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (base : UInt32) (values : List UInt64)
    (hfit : base.toNat + 8 * values.length < UInt32.size)
    (hbaseBound : base.toNat ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      array64At 0 base values ==∗
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      array64At 0 base values ∗
      ⌜base.toNat + 8 * values.length ≤
        store.wasm.mem.pages * 65536⌝ := by
  by_cases hempty : values = []
  · subst values
    iintro ⟨Hstate, Harray⟩
    imodintro
    isplitl_exacts [Hstate Harray]
    · ipureintro
      simpa using hbaseBound
  · have hlength : 0 < values.length := by
      cases values with
      | nil => contradiction
      | cons value values => simp
    let k := values.length - 1
    have hk : k < values.length := by simp [k, hlength]
    let address := base + 8 * UInt32.ofNat k
    have haddress : address.toNat = base.toNat + 8 * k := Mem.words64_slotAddr_toNat base k (by
        simp only [UInt32.size] at hfit; omega)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 address (by
      simp only [UInt32.size] at hfit ⊢
      rw [haddress]; omega)
    iintro ⟨Hstate, Harray⟩
    ihave ⟨Hword, Hrestore⟩ := array64At_get 0 base values k hk $$ Harray
    imod stateInterp_pointsTo_u64_facts_frame
      store steps observations threads address values[k]
      h1 h2 h3 h4 h5 h6 h7 $$ [$Hstate $Hword] with
      ⟨Hstate, Hword, %hfacts⟩
    imodintro
    isplitl_exact Hstate
    isplitl [Hrestore Hword]
    · iapply_exact Hrestore with Hword
    · ipureintro
      rw [haddress] at hfacts
      dsimp only [k] at hfacts; omega

end Wasm.SepLogic
