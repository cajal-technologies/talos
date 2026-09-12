import HexEncodeStdio.OutputAllocationCost
import HexEncodeStdio.EncodeFunctionResourceCost

/-! Physical postconditions of the actual output reserve, ready for the
complete generated encoder and its original caller continuation. -/

namespace Project.HexEncodeStdio.OutputAllocationResources

open Wasm Wasm.SmallStep Project.HexStdio
open OutputAllocationCost ReadToEndResourceCost EncodeResourceCost

structure Facts (input : List UInt8) (store : MachineStore Universal.State)
    (inputCapacity inputPtr inputBump : UInt32) : Prop where
  runtime_eq : (reservedStore input store inputBump).runtime = store.runtime
  host_eq : (reservedStore input store inputBump).wasm.host = store.wasm.host
  global_eq : globalAt? (reservedStore input store inputBump) 0 = some (.i32 1048512)
  capacity_eq : (reservedStore input store inputBump).wasm.mem.read32 1048516 = outputCapacity input
  output_eq : (reservedStore input store inputBump).wasm.mem.read32 1048520 = allocatorPtr inputBump 1
  zero_eq : (reservedStore input store inputBump).wasm.mem.read32 1048524 = 0
  input_capacity_eq : (reservedStore input store inputBump).wasm.mem.read32 1048552 = inputCapacity
  input_capacity_ne : inputCapacity ≠ 0
  input_ptr_eq : (reservedStore input store inputBump).wasm.mem.read32 1048556 = inputPtr
  input_length_eq : (reservedStore input store inputBump).wasm.mem.read32 1048560 = UInt32.ofNat input.length
  input_bytes : (reservedStore input store inputBump).wasm.mem.readBytes inputPtr.toNat input.length = input
  table_bytes : (reservedStore input store inputBump).wasm.mem.readBytes 1048576 16 = Hex.asciiTable
  table_ascii : AsciiTable (reservedStore input store inputBump).wasm.mem
  capacity_nat : (outputCapacity input).toNat = max 8 (2 * input.length)
  pointer_eq : allocatorPtr inputBump 1 = inputBump
  length_nat : (UInt32.ofNat input.length).toNat = input.length
  source_lower : 1048592 ≤ inputPtr.toNat
  output_lower : 1048592 ≤ (allocatorPtr inputBump 1).toNat
  source_physical : inputPtr.toNat + input.length ≤ (reservedStore input store inputBump).wasm.mem.pages * 65536
  source_noWrap : inputPtr.toNat + input.length < UInt32.size
  output_physical : (allocatorPtr inputBump 1).toNat + 2 * input.length ≤
    (reservedStore input store inputBump).wasm.mem.pages * 65536
  output_noWrap : (allocatorPtr inputBump 1).toNat + 2 * input.length < UInt32.size
  finish_signed : inputBump.toNat + (outputCapacity input).toNat < 2 ^ 31
  pages_eq : (reservedStore input store inputBump).wasm.mem.pages = max store.wasm.mem.pages
    (AllocatorResourceCost.requiredPages (inputBump.toNat + (outputCapacity input).toNat))
  pages_bound : (reservedStore input store inputBump).wasm.mem.pages ≤ max store.wasm.mem.pages
    (AllocatorResourceCost.requiredPages (completeFrontierBound input.length))

/-- Reading the known sixteen bytes establishes the generated ASCII dispatch
condition at every lookup address. -/
theorem ascii_of_bytes (memory : Mem)
    (h : memory.readBytes 1048576 16 = Hex.asciiTable) : AsciiTable memory := by
  intro i hi
  have hbyte := congrArg (fun bytes : List UInt8 => bytes[i]?) h
  simp only [Mem.readBytes, List.getElem?_map, List.getElem?_range, hi,
    Option.map_some] at hbyte
  interval_cases i <;>
    simp [Hex.asciiTable, Mem.read8] at hbyte ⊢ <;>
    simp_all

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem reserved_facts (input : List UInt8) (store : MachineStore Universal.State)
    (inputCapacity inputPtr inputBump : UInt32)
    (hinput : input ≠ []) (hfit : InputFits input.length)
    (hcapacityArg : store.wasm.mem.read32 1048552 = inputCapacity)
    (hptrArg : store.wasm.mem.read32 1048556 = inputPtr)
    (hbumpArg : store.wasm.mem.read32 1053960 = inputBump)
    (hread : ReadToEndSuccess input (encodeAfterReadConfig store))
    (hfrontier : inputBump.toNat ≤ inputFrontierBound input.length)
    (halloc : ByteGrowSuccess
      (reserveFrameStore (encodeAllocFrameStore store) (1048512 - 16))
      0 1 (outputCapacity input) inputBump (allocatedStore input store inputBump)) :
    Facts input store inputCapacity inputPtr inputBump := by
  let allocStore := allocatedStore input store inputBump
  rcases hread with ⟨readStore, capacity, data, bump, hconfig,
    hhostInput, hhostOutput, hoom, hentry, hmod, henv, hmemCap, hpages,
    hglobal, hcapacity, hptr, hlength, hbump, htable, hinputBytes,
    hlengthCap, hcapacityMin, hcapacitySmall, hdataLower,
    hdataBump, hbumpSmall, hdataBound⟩
  simp only [encodeAfterReadConfig] at hconfig
  have hstore : readStore = store := by
    simpa using (congrArg Config.store hconfig).symm
  subst readStore
  have hcapacityWitness : capacity = inputCapacity := hcapacity.symm.trans hcapacityArg
  have hptrWitness : data = inputPtr := hptr.symm.trans hptrArg
  have hbumpWitness : bump = inputBump := hbump.symm.trans hbumpArg
  rw [hcapacityWitness] at hlengthCap hcapacityMin hcapacitySmall hdataBump hdataBound
  rw [hptrWitness] at hdataLower hinputBytes hdataBump hdataBound
  rw [hbumpWitness] at hbumpSmall hdataBump
  let outputCapacity := reserveNewCapacity 0
    (UInt32.ofNat input.length <<< 1) 0
  let output := allocatorPtr inputBump 1
  let finalStore := encodeOutputStore allocStore output outputCapacity
  have hinputLen : (UInt32.ofNat input.length).toNat = input.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size]
    omega
  have hinputBumpNe : inputBump ≠ 0 := by
    intro hz
    have hzNat := congrArg UInt32.toNat hz
    simp only [UInt32.toNat_zero] at hzNat
    omega
  have houtput : output = inputBump := allocatorPtr_one_eq _ hinputBumpNe
  have hcapacityEq : outputCapacity =
      UInt32.ofNat (Project.HexEncodeStdio.TotalEncodeLoop.encodeCapacityNat input) :=
    encode_allocation_capacity input hinput (by omega)
  have hcapacityNat : outputCapacity.toNat =
      max 8 (2 * input.length) := by
    rw [hcapacityEq, UInt32.toNat_ofNat_of_lt' (by
      change max 8 (2 * input.length) < UInt32.size
      norm_num [UInt32.size]
      omega)]
  have hbasePages :
      (reserveFrameStore (encodeAllocFrameStore store)
        (1048512 - 16)).wasm.mem.pages < UInt32.size := by
    simpa [reserveFrameStore, encodeAllocFrameStore, UInt32.size] using
      (show store.wasm.mem.pages < 4294967296 by omega)
  have hfinishBound := halloc.fresh_finish_bound hbasePages
  have hfinishNat : (allocatorFinish outputCapacity 1 inputBump).toNat =
      output.toNat + outputCapacity.toNat := by
    have hcapLe : outputCapacity.toNat ≤ 2 * inputCapacity.toNat := by
      rw [hcapacityNat]
      omega
    have hsum : output.toNat + outputCapacity.toNat < UInt32.size := by
      rw [houtput]
      norm_num [UInt32.size] at hbumpSmall hcapacitySmall ⊢
      omega
    rw [allocatorFinish_one_eq_comm outputCapacity inputBump hinputBumpNe]
    simp only [UInt32.toNat_add]
    rw [Nat.mod_eq_of_lt (by simpa [houtput] using hsum), houtput]
  have hlimitSmall : output.toNat + 2 * input.length < UInt32.size := by
    rw [houtput]
    norm_num [UInt32.size] at hbumpSmall hcapacitySmall ⊢
    omega
  have hlimitBound : output.toNat + 2 * input.length ≤
      finalStore.wasm.mem.pages * 65536 := by
    have hcapLe : 2 * input.length ≤ outputCapacity.toNat := by
      rw [hcapacityNat]
      omega
    have hleft : output.toNat + 2 * input.length ≤
        (allocatorFinish outputCapacity 1 inputBump).toNat := by
      rw [hfinishNat]
      omega
    have hright : (allocatorFinish outputCapacity 1 inputBump).toNat ≤
        finalStore.wasm.mem.pages * 65536 := by
      simpa [outputCapacity, finalStore, encodeOutputStore, OutputAllocationCost.outputCapacity, allocStore] using hfinishBound
    exact le_trans hleft hright
  have hallocRuntime : allocStore.runtime = store.runtime := by
    have hr := halloc.runtime_eq
    simpa [reserveFrameStore, encodeAllocFrameStore] using hr
  have hfinalRuntime : finalStore.runtime.currentModule = «module» := by
    change allocStore.runtime.currentModule = «module»
    rw [hallocRuntime]
    exact hmod
  have hfinalEnv : finalStore.runtime.currentHost = Universal.envFor «module» := by
    change allocStore.runtime.currentHost = Universal.envFor «module»
    rw [hallocRuntime]
    exact henv
  have hfinalHost : finalStore.wasm.host = store.wasm.host := by
    change allocStore.wasm.host = store.wasm.host
    exact halloc.host_eq
  have hfinalGlobal : globalAt? finalStore 0 = some (.i32 1048512) := by
    simp only [finalStore, encodeOutputStore, reserveFinishStore,
      reserveVectorStore, globalAt?, canonicalGlobalIndex_zero]
    apply List.getElem?_set_self
    have hlen : allocStore.wasm.globals.globals.length =
        store.wasm.globals.globals.length := by
      simp [allocStore, OutputAllocationCost.allocatedStore, ReserveResourceCost.allocationStore,
        AllocatorResourceCost.finalStore, allocatorBumpStore, allocatorGrownStore,
        reserveFrameStore, encodeAllocFrameStore]
    simp only [growResultOkStore]
    rw [hlen]
    exact (getElem?_eq_some_iff.mp hglobal).1
  have hfinalTable : finalStore.wasm.mem.readBytes 1048576 16 =
      Project.HexEncodeStdio.Hex.asciiTable := by
    rw [encodeOutputStore_preserves_bytes allocStore output outputCapacity
      1048576 16 (by decide)]
    rw [halloc.fresh_preserves_bytes 1048576 16 (Or.inl (by decide))]
    simp only [reserveFrameStore, encodeAllocFrameStore]
    rw [Mem.readBytes_write64_disjoint, Mem.readBytes_write32_disjoint]
    · exact htable
    all_goals decide
  have hfinalInput : finalStore.wasm.mem.readBytes inputPtr.toNat input.length =
      input := by
    rw [encodeOutputStore_preserves_bytes allocStore output outputCapacity
      inputPtr.toNat input.length (by omega)]
    rw [halloc.fresh_preserves_bytes inputPtr.toNat input.length
      (Or.inr (by omega))]
    simp only [reserveFrameStore, encodeAllocFrameStore]
    rw [Mem.readBytes_write64_disjoint, Mem.readBytes_write32_disjoint]
    · exact hinputBytes
    · right
      exact le_trans (by decide) hdataLower
    · right
      exact le_trans (by decide) hdataLower
  have hfinalCapacity : finalStore.wasm.mem.read32 1048516 = outputCapacity := by
    simp only [finalStore, encodeOutputStore, reserveFinishStore,
      reserveVectorStore, growResultOkStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write32_same]
    decide
  have hfinalOutput : finalStore.wasm.mem.read32 1048520 = output := by
    simp only [finalStore, encodeOutputStore, reserveFinishStore,
      reserveVectorStore, growResultOkStore]
    exact Mem.read32_write32_same _ _ _
  have hfinalZero : finalStore.wasm.mem.read32 1048524 = 0 := by
    simp only [finalStore, encodeOutputStore, reserveFinishStore,
      reserveVectorStore, growResultOkStore]
    rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
      Mem.read32_write32_disjoint]
    · rw [halloc.fresh_preserves_read32 (by decide)]
      simp only [reserveFrameStore, encodeAllocFrameStore]
      rw [Mem.read32_write64_disjoint, Mem.read32_write32_same]
      decide
    all_goals decide
  have hfinalInputCapacity : finalStore.wasm.mem.read32 1048552 =
      inputCapacity := by
    rw [encodeOutputStore_preserves_read32 allocStore output outputCapacity
      1048552 (by decide)]
    rw [halloc.fresh_preserves_read32 (by decide)]
    simp only [reserveFrameStore, encodeAllocFrameStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hcapacityArg
    all_goals decide
  have hfinalInputPtr : finalStore.wasm.mem.read32 1048556 = inputPtr := by
    rw [encodeOutputStore_preserves_read32 allocStore output outputCapacity
      1048556 (by decide)]
    rw [halloc.fresh_preserves_read32 (by decide)]
    simp only [reserveFrameStore, encodeAllocFrameStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hptrArg
    all_goals decide
  have hfinalInputLen : finalStore.wasm.mem.read32 1048560 =
      UInt32.ofNat input.length := by
    rw [encodeOutputStore_preserves_read32 allocStore output outputCapacity
      1048560 (by decide)]
    rw [halloc.fresh_preserves_read32 (by decide)]
    simp only [reserveFrameStore, encodeAllocFrameStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hlength
    all_goals decide
  have hinputEnd : inputPtr.toNat + input.length ≤ output.toNat := by
    rw [houtput]
    have hcap : input.length ≤ inputCapacity.toNat := by omega
    have hadd := hdataBump
    omega
  have hstackEnd : 1048516 + 76 ≤ inputPtr.toNat := by omega
  have hfinalEq : finalStore = reservedStore input store inputBump := rfl
  have hsourcePhysical : inputPtr.toNat + input.length ≤ finalStore.wasm.mem.pages * 65536 := by
    have hp : store.wasm.mem.pages ≤ finalStore.wasm.mem.pages := halloc.pages_mono
    have hphysical := hdataBound
    have hn := hlengthCap
    omega
  have hsourceWrap : inputPtr.toNat + input.length < UInt32.size := by
    have hb := hbumpSmall
    norm_num [UInt32.size] at hb ⊢
    omega
  have pages : finalStore.wasm.mem.pages = max store.wasm.mem.pages
      (AllocatorResourceCost.requiredPages (inputBump.toNat + outputCapacity.toNat)) := by
    change allocStore.wasm.mem.pages = _
    dsimp only [allocStore, OutputAllocationCost.allocatedStore]
    rw [ReserveResourceCost.allocationStore_pages]
    simp only [allocatorBase, if_neg hinputBumpNe]
    rfl
  have pageBound : finalStore.wasm.mem.pages ≤ max store.wasm.mem.pages
      (AllocatorResourceCost.requiredPages (completeFrontierBound input.length)) := by
    rw [pages]
    have hfinish : inputBump.toNat + outputCapacity.toNat ≤ completeFrontierBound input.length := by
      rw [hcapacityNat]
      unfold completeFrontierBound
      omega
    have hr : AllocatorResourceCost.requiredPages (inputBump.toNat + outputCapacity.toNat) ≤
        AllocatorResourceCost.requiredPages (completeFrontierBound input.length) := by
      unfold AllocatorResourceCost.requiredPages
      omega
    omega
  refine ⟨hallocRuntime, hfinalHost, hfinalGlobal, hfinalCapacity, hfinalOutput, hfinalZero,
    hfinalInputCapacity, ?_, hfinalInputPtr, hfinalInputLen, hfinalInput, hfinalTable,
    ascii_of_bytes _ hfinalTable, hcapacityNat, houtput, hinputLen, ?_, ?_,
    hsourcePhysical, hsourceWrap, hlimitBound, hlimitSmall, ?_, pages, pageBound⟩
  · intro hz
    rw [hz, UInt32.toNat_zero] at hcapacityMin
    omega
  · omega
  · change 1048592 ≤ output.toNat
    rw [houtput]
    omega
  · change inputBump.toNat + outputCapacity.toNat < 2 ^ 31
    rw [hcapacityNat]
    dsimp only [InputFits, completeFrontierBound] at hfit
    omega

/-- The reserve wrapper restores exactly the runtime needed by the encoder's
saved caller frame. -/
theorem reserved_config_eq (input : List UInt8) (store : MachineStore Universal.State)
    (inputCapacity inputPtr inputBump : UInt32) (facts : Facts input store inputCapacity inputPtr inputBump) :
    reservedConfig input store inputPtr inputBump =
      EncodeFunctionResourceCost.afterAllocationConfig (reservedStore input store inputBump)
        inputPtr (UInt32.ofNat input.length) := by
  simp only [reservedConfig, EncodeFunctionResourceCost.afterAllocationConfig,
    growResultFinal, EncodeResourceCost.encodeLocals, encodeMainCalls, facts.runtime_eq]

end Project.HexEncodeStdio.OutputAllocationResources
