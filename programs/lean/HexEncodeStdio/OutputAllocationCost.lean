import HexEncodeStdio.ExportResourceCost
import HexEncodeStdio.ReserveResourceCost
import HexEncodeStdio.ReadToEndResourceCost

/-! # Output allocation after the complete physical reader

The input frontier bound closes the allocator's signed-address guard. The
actual reserve proof then selects and performs physical growth, retaining the
generated encoder continuation and the same successful allocation witness.
-/

namespace Project.HexEncodeStdio.OutputAllocationCost

open Wasm Wasm.SmallStep Project.HexStdio
open ReadToEndResourceCost ExportResourceCost

def outputCapacity (input : List UInt8) : UInt32 :=
  reserveNewCapacity 0 (UInt32.ofNat input.length <<< 1) 0

def allocatedStore (input : List UInt8) (store : MachineStore Universal.State)
    (bump : UInt32) : MachineStore Universal.State :=
  ReserveResourceCost.allocationStore
    (reserveFrameStore (encodeAllocFrameStore store) (1048512 - 16))
    0 1 (outputCapacity input) bump

def reservedStore (input : List UInt8) (store : MachineStore Universal.State)
    (bump : UInt32) : MachineStore Universal.State :=
  ReserveResourceCost.finalStore (encodeAllocFrameStore store)
    1048516 0 (UInt32.ofNat input.length <<< 1) 0 1 1048512 bump

def reservedConfig (input : List UInt8) (store : MachineStore Universal.State)
    (pointer bump : UInt32) : Config Universal.State :=
  growResultFinal (reservedStore input store bump)
    [.i32 1048564, .i32 pointer, .i32 (UInt32.ofNat input.length)]
    [.i32 1048512, .i32 (pointer + UInt32.ofNat input.length), .i32 0,
      .i32 0, .i32 0, .i32 0]
    [] [] 0 [] encodeReserveControls (encodeMainCalls store pointer)

theorem outputCapacity_toNat (input : List UInt8) (hne : input ≠ [])
    (hfit : InputFits input.length) :
    (outputCapacity input).toNat = max 8 (2 * input.length) := by
  have hsmall := input_fits_output input.length hfit
  have hsigned : 2 * input.length < 2 ^ 31 := by
    dsimp only [InputFits, completeFrontierBound] at hfit
    omega
  rw [outputCapacity, encode_allocation_capacity input hne hsigned]
  apply UInt32.toNat_ofNat_of_lt'
  change max 8 (2 * input.length) < UInt32.size
  norm_num [UInt32.size] at hsmall ⊢
  omega

/-- From the reader's actual return through the complete output reserve.
Only the input-size and retained initial frontier bounds supplement the
existing concrete reader postcondition. -/
theorem after_read_reserve_cost (input : List UInt8)
    (store : MachineStore Universal.State) (hne : input ≠ [])
    (hfit : InputFits input.length)
    (hread : ReadToEndSuccess input (encodeAfterReadConfig store))
    (hfrontier : (store.wasm.mem.read32 1053960).toNat ≤ inputFrontierBound input.length) :
    ∃ inputCapacity pointer bump trace,
      store.wasm.mem.read32 1048552 = inputCapacity ∧
      store.wasm.mem.read32 1048556 = pointer ∧
      store.wasm.mem.read32 1053960 = bump ∧
      trace.length ≤ 179 ∧
      CostedSteps CostedStdIO.work (encodeAfterReadConfig store) trace
        (reservedConfig input store pointer bump)
        (trace.length + 65536 *
          (AllocatorResourceCost.requiredPages
            ((allocatorBase bump).toNat + (outputCapacity input).toNat) - store.wasm.mem.pages)) ∧
      ByteGrowSuccess (reserveFrameStore (encodeAllocFrameStore store) (1048512 - 16))
        0 1 (outputCapacity input) bump (allocatedStore input store bump) ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  rcases hread with ⟨readStore, capacity, pointer, bump, hconfig,
    _, _, _, _, hmodule, hhost, hcap, hpagesUpper, hglobal, hcapacity, hpointer,
    hlength, hbump, _, _, hlengthCapacity, hcapacityMin, _, hdataLower,
    hdataBump, hbumpSmall, hdataBound⟩
  have heq : store = readStore := congrArg Config.store hconfig
  subst readStore
  have hpages : 17 ≤ store.wasm.mem.pages := by omega
  have hlengthNat : (UInt32.ofNat input.length).toNat = input.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size]
    omega
  have hlengthNe : UInt32.ofNat input.length ≠ 0 := by
    intro hz
    rw [hz, UInt32.toNat_zero] at hlengthNat
    exact hne (List.eq_nil_of_length_eq_zero hlengthNat.symm)
  have hbumpNe : bump ≠ 0 := by
    intro hz
    rw [hz, UInt32.toNat_zero] at hdataBump
    omega
  have hcapacityNat := outputCapacity_toNat input hne hfit
  have hfinish : (allocatorBase bump).toNat + (outputCapacity input).toNat < 2147483648 := by
    rw [hbump] at hfrontier
    simp only [allocatorBase, if_neg hbumpNe]
    rw [hcapacityNat]
    dsimp only [InputFits, completeFrontierBound] at hfit
    omega
  let encoded := encodeAllocFrameStore store
  have encodeGlobal : globalAt? encoded 0 = some (.i32 1048512) := by
    have hzero := (getElem?_eq_some_iff.mp (show store.wasm.globals.globals[0]? =
      some (.i32 1048544) by simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
    simp [encoded, encodeAllocFrameStore, globalAt?, canonicalGlobalIndex_zero, hzero]
  have encodeCapacity : encoded.wasm.mem.read32 1048516 = 0 := by
    simp [encoded, encodeAllocFrameStore, Mem.read32, Mem.write32, Mem.write64]; decide
  have encodePointer : encoded.wasm.mem.read32 (1048516 + 4) = 1 := by
    simp [encoded, encodeAllocFrameStore, Mem.read32, Mem.write32, Mem.write64]; decide
  have encodeBump : encoded.wasm.mem.read32 1053960 = bump := by
    dsimp only [encoded, encodeAllocFrameStore]
    rw [Mem.read32_write64_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)]
    exact hbump
  obtain ⟨reserveTrace, reserveLength, reserveRun, success, reserveLabels⟩ :=
    ReserveResourceCost.reserve_cost encoded
      [.i32 1048564, .i32 pointer, .i32 (UInt32.ofNat input.length)]
      [.i32 1048512, .i32 (pointer + UInt32.ofNat input.length), .i32 0, .i32 0, .i32 0, .i32 0]
      [] [] 0 [] encodeReserveControls (encodeMainCalls store pointer)
      1048516 0 (UInt32.ofNat input.length <<< 1) 0 1 1048512 bump
      hmodule hcap hpagesUpper encodeGlobal (by simp [reserveRequired])
      encodeCapacity encodePointer encodeBump
      (by change 1053964 ≤ store.wasm.mem.pages * 65536; omega) hfinish
      (by change 0 < (outputCapacity input).toNat; rw [hcapacityNat]; omega)
      (by change 1 ≤ store.wasm.mem.pages * 65536; omega)
      (by change 1048512 ≤ store.wasm.mem.pages * 65536; omega)
      (by decide) (by decide)
      (by change 1048524 ≤ store.wasm.mem.pages * 65536; omega)
  have dispatch := after_read_to_encode_cost store pointer (UInt32.ofNat input.length)
    hpointer hlength hpages
  have setup := encode_call_to_reserve_cost store pointer (UInt32.ofNat input.length)
    hmodule hglobal hlengthNe hpages
  have run := (dispatch.trans setup).trans reserveRun
  refine ⟨capacity, pointer, bump, afterReadTrace ++ allocationSetupTrace ++ reserveTrace,
    hcapacity, hpointer, hbump, ?_, ?_, success, ?_⟩
  · simp only [List.length_append, show afterReadTrace.length = 8 from rfl,
      show allocationSetupTrace.length = 27 from rfl]
    simp at reserveLength
    omega
  · simpa only [List.length_append, show afterReadTrace.length = 8 from rfl,
      show allocationSetupTrace.length = 27 from rfl, UInt32.toNat_zero, Nat.add_zero,
      Nat.add_assoc, reservedConfig, reservedStore, outputCapacity, encoded, encodeAllocFrameStore,
      Mem.write32_pages, Mem.write64_pages] using run
  · intro kind member
    simp only [List.mem_append] at member
    rcases member with (dispatch | setup) | reserve
    · exact afterReadTrace_primary kind dispatch
    · exact allocationSetupTrace_primary kind setup
    · cases kind <;> first | exact reserveLabels _ reserve | trivial

end Project.HexEncodeStdio.OutputAllocationCost
