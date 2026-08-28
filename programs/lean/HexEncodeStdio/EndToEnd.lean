import HexEncodeStdio.ReadToEndInitial
import HexEncodeStdio.EncodeAllocOperational
import HexEncodeStdio.PrefixMemory
import HexEncodeStdio.TotalMain
import HexEncodeStdio.TotalEncodeFunction
import HexEncodeStdio.OutcomeBridge

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std FromMathlib
open Wasm.SepLogic

theorem ByteGrowSuccess.fresh_finish_bound
    {store final : MachineStore Universal.State}
    {oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store 0 oldPtr newCapacity oldBump final)
    (hpages : store.wasm.mem.pages < UInt32.size) :
    (allocatorFinish newCapacity 1 oldBump).toNat ≤
      final.wasm.mem.pages * 65536 := by
  have required_eq (hsmall :
      (allocatorFinish newCapacity 1 oldBump).toNat < 2 ^ 31) :
      (allocatorRequiredPages newCapacity 1 oldBump).toNat =
        (65535 + (allocatorFinish newCapacity 1 oldBump).toNat) / 65536 := by
    have hadd :
        ((65535 : UInt32) + allocatorFinish newCapacity 1 oldBump).toNat =
          65535 + (allocatorFinish newCapacity 1 oldBump).toNat := by
      simp only [UInt32.toNat_add, UInt32.reduceToNat]
      rw [Nat.mod_eq_of_lt]
      norm_num at hsmall ⊢
      omega
    rw [allocatorRequiredPages, UInt32.toNat_shiftRight, hadd]
    change (65535 + (allocatorFinish newCapacity 1 oldBump).toNat) >>> 16 = _
    rw [Nat.shiftRight_eq_div_pow]
  cases h with
  | freshNoGrow hzero hfit hnonnegative =>
      have hsmall := UInt32.toNat_lt_signed_limit_of_not_negative _ hnonnegative
      apply ceil_pages_bound
      rw [← required_eq hsmall]
      have hn := UInt32.le_iff_toNat_le.mp hfit
      rw [UInt32.toNat_ofNat_of_lt' hpages] at hn
      simpa [allocatorBumpStore] using hn
  | freshGrow hzero memory previousPages hnotfit hgrow hnonnegative =>
      have hsmall := UInt32.toNat_lt_signed_limit_of_not_negative _ hnonnegative
      have hfacts := mem_grow_some_facts store.wasm.mem memory
        (allocatorRequiredPages newCapacity 1 oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0)
        previousPages hgrow
      apply ceil_pages_bound
      rw [← required_eq hsmall]
      simp only [allocatorBumpStore, allocatorGrownStore, Mem.write32_pages]
      rw [hfacts.2]
      have hgtU : UInt32.ofNat store.wasm.mem.pages <
          allocatorRequiredPages newCapacity 1 oldBump := by
        exact UInt32.not_le.mp hnotfit
      have hgt := UInt32.lt_iff_toNat_lt.mp hgtU
      rw [UInt32.toNat_sub_of_le _ _ (Nat.le_of_lt hgtU),
        UInt32.toNat_ofNat_of_lt' hpages]
      rw [UInt32.toNat_ofNat_of_lt' hpages] at hgt
      omega
  | reallocNoGrow hnonzero => contradiction
  | reallocGrow hnonzero => contradiction

def encodeOutputStore (allocStore : MachineStore Universal.State)
    (output outputCapacity : UInt32) : MachineStore Universal.State :=
  reserveFinishStore
    (growResultOkStore allocStore ((1048512 - 16) + 4) output outputCapacity)
    1048516 output outputCapacity 1048512

theorem encodeOutputStore_preserves_bytes
    (allocStore : MachineStore Universal.State) (output outputCapacity : UInt32)
    (off len : Nat) (hbelow : 1048528 ≤ off) :
    (encodeOutputStore allocStore output outputCapacity).wasm.mem.readBytes off len =
      allocStore.wasm.mem.readBytes off len := by
  simp only [encodeOutputStore, reserveFinishStore, reserveVectorStore,
    growResultOkStore]
  rw [Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint, Mem.readBytes_write32_disjoint,
    Mem.readBytes_write32_disjoint]
  all_goals right; exact le_trans (by decide) hbelow

theorem encodeOutputStore_preserves_read32
    (allocStore : MachineStore Universal.State) (output outputCapacity addr : UInt32)
    (hbelow : 1048528 ≤ addr.toNat) :
    (encodeOutputStore allocStore output outputCapacity).wasm.mem.read32 addr =
      allocStore.wasm.mem.read32 addr := by
  simp only [encodeOutputStore, reserveFinishStore, reserveVectorStore,
    growResultOkStore]
  rw [Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint, Mem.read32_write32_disjoint,
    Mem.read32_write32_disjoint]
  all_goals right; exact le_trans (by decide) hbelow

theorem encode_allocation_capacity (input : List UInt8)
    (hpos : input ≠ []) (hsmall : 2 * input.length < 2 ^ 31) :
    reserveNewCapacity 0 (UInt32.ofNat input.length <<< 1) 0 =
      UInt32.ofNat (Submission.TotalEncodeLoop.encodeCapacityNat input) := by
  have hlen : input.length < UInt32.size := by
    norm_num [UInt32.size] at hsmall ⊢
    omega
  have hdouble : 2 * input.length < UInt32.size := by
    norm_num [UInt32.size] at hsmall ⊢
    omega
  have hshift : (UInt32.ofNat input.length <<< 1).toNat =
      2 * input.length := by
    simp only [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat_of_lt' hlen,
      UInt32.reduceToNat, Nat.shiftLeft_eq]
    norm_num
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have haddPos : (0 : UInt32) < UInt32.ofNat input.length <<< 1 := by
    apply UInt32.lt_iff_toNat_lt.mpr
    rw [hshift]
    simpa [List.length_pos_iff] using hpos
  apply UInt32.toNat_inj.mp
  simp only [reserveNewCapacity, reserveCandidate, reserveRequired,
    reserveDoubled, UInt32.zero_add, UInt32.zero_shiftLeft]
  rw [if_pos haddPos]
  split
  next hgt =>
    rw [UInt32.toNat_ofNat_of_lt' (by
      change max 8 (2 * input.length) < UInt32.size
      norm_num [UInt32.size]
      omega)]
    change (UInt32.ofNat input.length <<< 1).toNat =
      max 8 (2 * input.length)
    rw [max_eq_right]
    · exact hshift
    · have hn := UInt32.lt_iff_toNat_lt.mp hgt
      simpa [hshift] using Nat.le_of_lt hn
  next hngt =>
    rw [UInt32.toNat_ofNat_of_lt' (by
      change max 8 (2 * input.length) < UInt32.size
      norm_num [UInt32.size]
      omega)]
    change (8 : UInt32).toNat = max 8 (2 * input.length)
    rw [max_eq_left]
    · decide
    · have hn : ¬(8 : UInt32).toNat <
          (UInt32.ofNat input.length <<< 1).toNat := by
        exact hngt
      simpa [hshift] using Nat.le_of_not_gt hn

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 1048576 in
theorem read_to_end_nonempty_outcome (input : List UInt8) (hinput : input ≠ []) :
    ReachesOrOOM (encodeInitialConfig input) (ReadToEndSuccess input) := by
  let bytes := input.take 32
  have hbytes : bytes = input.take 32 := rfl
  have hbytesNe : bytes ≠ [] := by
    cases input with
    | nil => exact (hinput rfl).elim
    | cons byte rest => simp [bytes]
  have hprefix := encode_to_read_to_end input
  have hfirst := read_to_end_first_outcome (encodeFrameStore input)
    [] encodeLocals [] (func10.drop 9) 0 [] [] []
    (by rfl) (by rfl) (by
      simp [encodeFrameStore, encodeInitialStore, globalAt?,
        canonicalGlobalIndex_zero]
      decide) (by rfl) (by
      simp [encodeFrameStore, encodeInitialStore, Mem.read32]
      decide)
  apply ReachesOrOOM.prependReaches hprefix
  apply ReachesOrOOM.bind hfirst
  intro first hfirstPost
  have hstoreInput :
      (encodeFrameStore input).wasm.host.stdio.input = input := rfl
  rw [hstoreInput, ← hbytes] at hfirstPost
  simp only [hbytesNe, ↓reduceIte] at hfirstPost
  rcases hfirstPost with ⟨allocStore, hsuccess, rfl⟩
  let count := UInt32.ofNat bytes.length
  let capacity := reserveNewCapacity 0 count 0
  let data := allocatorPtr 0 1
  let bump := allocatorFinish capacity 1 0
  let framed := readToEndFrameStore (encodeFrameStore input) readToEndStack
  let after := readAdapterResultStore
    (readChunkFrameStore framed firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let reserved := reserveFinishStore
    (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
      data capacity)
    readToEndVector data capacity firstChunkFrame
  let finalStore := readChunkFinishedStore
    (readChunkCopiedStore reserved data firstChunkBuffer count)
    readToEndResult readToEndVector count 0 readToEndStack
  have hinv : ReadToEndInv input bytes (input.drop bytes.length) finalStore
      capacity data count bump := by
    apply first_nonempty_read_invariant input bytes allocStore hbytes hbytesNe
    exact hsuccess
  have htoLoop := read_to_end_after_first_nonempty_to_loop finalStore
    [] encodeLocals [] (func10.drop 9) 0 [] [] [] 1048564 readToEndStack
    capacity data count
    (by
      simp [finalStore, readChunkFinishedStore, Mem.read8, Mem.write32,
        Mem.write8])
    (by
      simp only [finalStore, readChunkFinishedStore]
      rw [Mem.read32_write32_disjoint, Mem.read32_write8_disjoint]
      · exact Mem.read32_write32_same _ _ _
      all_goals decide)
    (by
      intro hz
      have := hinv.length_nat
      rw [hz] at this
      simp at this
      exact hbytesNe (List.eq_nil_of_length_eq_zero this.symm))
    hinv.capacity_eq hinv.data_eq hinv.length_eq
    (by have hp := hinv.pages_lower; change 1048529 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048536 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048520 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048524 ≤ _; omega)
    (by have hp := hinv.pages_lower; change 1048528 ≤ _; omega)
  have hentryEq : finalStore.runtime.entry =
      (encodeFrameStore input).runtime.entry := by
    change allocStore.runtime.entry = (encodeFrameStore input).runtime.entry
    rw [hsuccess.runtime_eq]
    rfl
  rw [hentryEq] at htoLoop
  apply ReachesOrOOM.prependReaches htoLoop
  exact read_to_end_loop_outcome input bytes (input.drop bytes.length)
    finalStore capacity data count bump 8192 hinv
    (by
      intro hz
      have := hinv.length_nat
      rw [hz] at this
      simp at this
      exact hbytesNe (List.eq_nil_of_length_eq_zero this.symm))
    (by decide)

set_option maxHeartbeats 1200000 in
theorem encode_reserve_after_read
    (input : List UInt8) (config : Config Universal.State)
    (hinput : input ≠ []) (hsuccess : ReadToEndSuccess input config) :
    ReachesOrOOM config (fun final =>
      ∃ (store : MachineStore Universal.State)
        (inputCapacity inputPtr inputBump : UInt32)
        (allocStore : MachineStore Universal.State),
        ReadToEndSuccess input (encodeAfterReadConfig store) ∧
        store.wasm.mem.read32 1048564 = inputCapacity ∧
        store.wasm.mem.read32 (1048564 + 4) = inputPtr ∧
        store.wasm.mem.read32 1053960 = inputBump ∧
        ByteGrowSuccess
          (reserveFrameStore (encodeAllocFrameStore store) (1048512 - 16))
          0 1
          (reserveNewCapacity 0 (UInt32.ofNat input.length <<< 1) 0)
          inputBump allocStore ∧
        final = growResultFinal
          (reserveFinishStore
            (growResultOkStore allocStore ((1048512 - 16) + 4)
              (allocatorPtr inputBump 1)
              (reserveNewCapacity 0 (UInt32.ofNat input.length <<< 1) 0))
            1048516 (allocatorPtr inputBump 1)
              (reserveNewCapacity 0 (UInt32.ofNat input.length <<< 1) 0)
            1048512)
          [.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)]
          [.i32 1048512,
            .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
            .i32 0, .i32 0]
          [] [] 0 [] encodeReserveControls (encodeMainCalls store inputPtr)) := by
  rcases hsuccess with ⟨store, inputCapacity, inputPtr, inputBump, rfl,
    hhostInput, hhostOutput, hoom, hentry, hmod, henv, hmemCap, hpages,
    hglobal, hcapacity, hptr, hlength, hbump, htable, hinputBytes,
    hlengthCap, hcapacityMin, hcapacitySmall, hdataLower,
    hdataBump, hbumpSmall, hdataBound⟩
  let length := UInt32.ofNat input.length
  let additional := length <<< 1
  let encodeStore := encodeAllocFrameStore store
  have hlengthNat : length.toNat = input.length := by
    apply UInt32.toNat_ofNat_of_lt'
    norm_num [UInt32.size]
    omega
  have hadditionalNat : additional.toNat = 2 * input.length := by
    simp only [additional, UInt32.toNat_shiftLeft, hlengthNat,
      UInt32.reduceToNat, Nat.shiftLeft_eq]
    norm_num
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hinputBumpNe : inputBump ≠ 0 := by
    intro hz
    have hzNat := congrArg UInt32.toNat hz
    simp only [UInt32.toNat_zero] at hzNat
    omega
  have hallocPtr : allocatorPtr inputBump 1 = inputBump :=
    allocatorPtr_one_eq inputBump hinputBumpNe
  have hbumpBound : inputBump.toNat ≤ store.wasm.mem.pages * 65536 := by
    omega
  have hnewCapacity := encode_allocation_capacity input hinput (by omega)
  have hmain := main_after_read_to_encode_call store 1048544 inputCapacity
    inputPtr length hcapacity hptr hlength
    (by change 1048572 ≤ store.wasm.mem.pages * 65536; omega)
    (by change 1048576 ≤ store.wasm.mem.pages * 65536; omega)
  apply ReachesOrOOM.prependReaches hmain
  have hencode := encode_call_to_reserve store inputPtr length hmod hglobal
    (by
      intro hz
      have hzNat := congrArg UInt32.toNat hz
      rw [hlengthNat] at hzNat
      simp only [UInt32.toNat_zero] at hzNat
      have hpos : 0 < input.length := List.length_pos_iff.mpr hinput
      omega)
    (by
      have hp : 1048576 ≤ store.wasm.mem.pages * 65536 := by
        exact le_trans (by omega) hdataBound
      omega)
  apply ReachesOrOOM.prependReaches hencode
  have hreserve := reserve_call_reachesOrOOM encodeStore
    [.i32 1048552, .i32 inputPtr, .i32 length]
    [.i32 1048512, .i32 (inputPtr + length), .i32 0, .i32 0, .i32 0,
      .i32 0]
    [] [] 0 [] encodeReserveControls (encodeMainCalls store inputPtr)
    1048516 0 additional 0 1 1048512 inputBump
    (by simpa [encodeStore, encodeAllocFrameStore] using hmod)
    (by simpa [encodeStore, encodeAllocFrameStore] using henv)
    (by
      simp [encodeStore, encodeAllocFrameStore, globalAt?,
        canonicalGlobalIndex_zero] at hglobal ⊢
      have hz := (getElem?_eq_some_iff.mp hglobal).1
      exact List.getElem?_set_eq_of_lt (.i32 1048512) hz)
    (by simp [reserveRequired])
    (by simp [encodeStore, encodeAllocFrameStore, Mem.read32, Mem.write64,
      Mem.write32] <;> decide)
    (by simp [encodeStore, encodeAllocFrameStore, Mem.read32, Mem.write64,
      Mem.write32] <;> decide)
    (by
      simp only [encodeStore, encodeAllocFrameStore]
      rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
      · exact hbump
      all_goals decide)
    (by change 1053964 ≤ store.wasm.mem.pages * 65536; omega)
    (by simpa [encodeStore, encodeAllocFrameStore] using hpages)
    (by
      rw [hnewCapacity]
      apply UInt32.toInt32_not_negative_of_small
      rw [UInt32.toNat_ofNat_of_lt']
      · simp [Submission.TotalEncodeLoop.encodeCapacityNat]
        omega
      · change max 8 (2 * input.length) < UInt32.size
        norm_num [UInt32.size]
        omega)
    (by simpa [hallocPtr] using hinputBumpNe)
    (by change 1048512 ≤ store.wasm.mem.pages * 65536; omega)
    (by decide) (by decide) (by bv_decide)
    (by change 1048520 ≤ store.wasm.mem.pages * 65536; omega)
    (by change 1048524 ≤ store.wasm.mem.pages * 65536; omega)
    (by
      rw [show reallocatorCopyLen 0
          (reserveNewCapacity 0 additional 0) = 0 by
        simp [reallocatorCopyLen]]
      simp only [UInt32.toNat_one, UInt32.toNat_zero, Nat.add_zero]
      change 1 ≤ store.wasm.mem.pages * 65536
      omega)
    (by
      intro _
      have hcopy : reallocatorCopyLen 0
          (reserveNewCapacity 0 additional 0) = 0 := by
        simp [reallocatorCopyLen]
      rw [hcopy, hallocPtr]
      simpa [encodeStore, encodeAllocFrameStore] using hbumpBound)
    (by
      intro memory previousPages hgrow
      have hfacts := mem_grow_some_facts encodeStore.wasm.mem memory
        (allocatorRequiredPages
            (reserveNewCapacity 0 additional 0) 1 inputBump -
          UInt32.ofNat encodeStore.wasm.mem.pages)
        (encodeStore.wasm.memoryCap encodeStore.runtime.currentModule 0)
        previousPages hgrow
      have hmono : store.wasm.mem.pages ≤ memory.pages := by
        simpa [encodeStore, encodeAllocFrameStore] using
          (show encodeStore.wasm.mem.pages ≤ memory.pages by omega)
      have hcopy : reallocatorCopyLen 0
          (reserveNewCapacity 0 additional 0) = 0 := by
        simp [reallocatorCopyLen]
      rw [hcopy]
      simp only [UInt32.toNat_zero, Nat.add_zero]
      constructor
      · have hpagesPos : 1 ≤ store.wasm.mem.pages * 65536 := by omega
        exact le_trans hpagesPos (Nat.mul_le_mul_right 65536 hmono)
      · rw [hallocPtr]
        exact le_trans hbumpBound (Nat.mul_le_mul_right 65536 hmono))
  apply hreserve.bind
  intro final hfinal
  rcases hfinal with ⟨allocStore, halloc, rfl⟩
  apply ReachesOrOOM.refl
  exact ⟨store, inputCapacity, inputPtr, inputBump, allocStore,
    ⟨_, inputCapacity, inputPtr, inputBump, rfl, hhostInput, hhostOutput,
      hoom, hentry, hmod, henv, hmemCap, hpages, hglobal, hcapacity, hptr, hlength,
      hbump, htable, hinputBytes, hlengthCap, hcapacityMin, hcapacitySmall,
      hdataLower, hdataBump, hbumpSmall, hdataBound⟩,
    hcapacity, hptr, hbump, halloc, rfl⟩

set_option maxHeartbeats 1200000 in
private theorem main_after_encode_finishes {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    (input : List UInt8) (store : MachineStore Universal.State)
    (inputCapacity inputPtr output outputCapacity : UInt32)
    (hinput : input ≠ [])
    (hhostOutput : store.wasm.host.stdio.output = [])
    (hcapacityNat : outputCapacity.toNat = max 8 (2 * input.length))
    (hlimitSmall : output.toNat + 2 * input.length < UInt32.size)
    (hinputCapacityNe : inputCapacity ≠ 0) :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn store.wasm.host ∗
      globalPointsToAt 0 0 (.i32 1048544) ∗
      pointsTo_u32 0 (1048544 + 8) outputCapacity ∗
      pointsTo_u32 0 (1048544 + 12) output ∗
      pointsTo_u32 0 (1048544 + 16) (UInt32.ofNat (encode input).length) ∗
      pointsTo_u32 0 (1048544 + 20) inputCapacity ∗
      pointsTo_u32 0 (1048544 + 24) inputPtr ∗
      pointsTo_u32 0 (1048544 + 28) (UInt32.ofNat input.length) ∗
      pointsToBytes 0 inputPtr input ∗
      pointsToBytes 0 output (encode input) ∗
      (⟨0, (1048544 : UInt32) - 16⟩ ↦w
        u32Byte Submission.TotalIterator.sentinel 0) ∗
      pointsTo_u32 0 (((1048544 : UInt32) - 16) + 4)
        (inputPtr + UInt32.ofNat input.length) ⊢
    WP (.running
      ⟨⟨[], [.i32 1048544, .i32 inputPtr, .i32 0, .i32 0], []⟩,
        Project.HexStdio.func10.drop 18, 0, [], [], []⟩ :
        Expr Universal.State) @ Stuckness.NotStuck; ⊤
      [{ fun values => iprop% ∀ (final : MachineStore Universal.State)
        (_observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) final 0 [] 0 -∗
          ⌜values = [] ∧ final.wasm.host.stdio.output = encode input⌝ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hglobal, Hcap, Hptr, Hlen,
    HinputCap, HinputPtr, HinputLen, Hinput, Hencoded, HwriteTag, Hcursor⟩
  iapply (Submission.TotalMain.func10_after_encode_nonempty
    (s := Stuckness.NotStuck) (E := ⊤)
    (Φ := fun values => iprop% ∀ (final : MachineStore Universal.State)
      (_observations : List StepKind),
      stateInterp (GF := WasmHeapGF Universal.State) final 0 [] 0 -∗
        ⌜values = [] ∧ final.wasm.host.stdio.output = encode input⌝)
    1048544 inputPtr inputCapacity output outputCapacity input (encode input)
    store.wasm.host (u32Byte Submission.TotalIterator.sentinel 0)
    (inputPtr + UInt32.ofNat input.length)
    rfl (List.length_pos_iff.mpr hinput)
    (by
      apply UInt32.toNat_ofNat_of_lt'
      simp [encode]
      norm_num [UInt32.size] at hlimitSmall ⊢
      omega)
    (by simp [encode, List.length_pos_iff, hinput])
    (by simpa [encode, Nat.mul_comm] using hlimitSmall)
    (by decide) (by decide)
    (by
      intro hz
      have hzNat := congrArg UInt32.toNat hz
      rw [hcapacityNat] at hzNat
      simp at hzNat)
    hinputCapacityNe) $$
    [$Hruntime $Henv $Hhost $Hglobal $Hcap $Hptr $Hlen $HinputCap
      $HinputPtr $HinputLen $Hinput $Hencoded $HwriteTag $Hcursor]
  iintro Hruntime Henv Hhost Hglobal
  iapply twp_finish
    (locals := ⟨[], [.i32 1048544, .i32 inputPtr, .i32 inputCapacity,
      .i32 outputCapacity], []⟩)
    (values := []) (arity := 0) (remainder := [])
  iapply twp.value rfl
  iintro %doneStore %observations Hstate
  imod Submission.TotalHost.stateInterp_host_set_expected doneStore 0 [] 0
    (Submission.TotalWrite.afterWrite store.wasm.host (encode input))
    (Submission.TotalWrite.afterWrite store.wasm.host (encode input)) $$
    [$Hstate $Hhost] with ⟨%hhostPhysical, Hstate, Hhost⟩
  ipureintro
  constructor
  · rfl
  · rw [hhostPhysical]
    simp [Submission.TotalWrite.afterWrite, hhostOutput]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000000 in
private theorem encode_function_finishes {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    (input : List UInt8) (store finalStore : MachineStore Universal.State)
    (inputCapacity inputPtr output outputCapacity : UInt32)
    (out : List UInt8)
    (hinput : input ≠ [])
    (houtLen : out.length = 2 * input.length)
    (hentry : store.runtime.entry = ⟨0⟩)
    (hhostOutput : store.wasm.host.stdio.output = [])
    (hcapacityEq : outputCapacity =
      UInt32.ofNat (Submission.TotalEncodeLoop.encodeCapacityNat input))
    (hcapacityNat : outputCapacity.toNat = max 8 (2 * input.length))
    (hlimitSmall : output.toNat + 2 * input.length < UInt32.size)
    (hinputEnd : inputPtr.toNat + input.length ≤ output.toNat)
    (hinputCapacityNe : inputCapacity ≠ 0) :
    (hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn store.wasm.host ∗
      pointsTo_u32 0 1048544 (finalStore.wasm.mem.read32 1048544) ∗
      pointsTo_u32 0 1048548 (finalStore.wasm.mem.read32 1048548) ∗
      pointsTo_u32 0 1048564 inputCapacity ∗
      pointsTo_u32 0 1048568 inputPtr ∗
      pointsTo_u32 0 1048572 (UInt32.ofNat input.length)) ∗
      runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      globalPointsToAt 0 0 (.i32 1048512) ∗
      pointsTo_u32 0 (1048512 + 4)
        (UInt32.ofNat (Submission.TotalEncodeLoop.encodeCapacityNat input)) ∗
      pointsTo_u32 0 (1048512 + 8) output ∗
      pointsTo_u32 0 (1048512 + 12) 0 ∗
      pointsTo_u32 0 (1048512 + 16)
        (finalStore.wasm.mem.read32 1048528) ∗
      pointsTo_u32 0 (1048512 + 20)
        (finalStore.wasm.mem.read32 1048532) ∗
      pointsTo_u32 0 (1048512 + 24)
        (finalStore.wasm.mem.read32 1048536) ∗
      pointsTo_u32 0 (1048512 + 28)
        (finalStore.wasm.mem.read32 1048540) ∗
      pointsTo_u64 0 (1048552 + 0)
        ((finalStore.wasm.mem.read32 1048552).toUInt64 |||
          ((finalStore.wasm.mem.read32 1048556).toUInt64 <<< 32)) ∗
      pointsTo_u32 0 (1048552 + 8)
        (finalStore.wasm.mem.read32 1048560) ∗
      pointsToBytes 0 inputPtr input ∗
      pointsToBytes 0 1048576 Submission.Hex.asciiTable ∗
      pointsToBytes 0 output out ⊢
    WP (.running
      ⟨⟨[.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)],
          [.i32 1048512,
            .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
            .i32 0, .i32 0], []⟩,
        Project.HexStdio.func6.drop 16, 0, [], [],
        encodeMainCalls store inputPtr⟩ : Expr Universal.State)
      @ Stuckness.NotStuck; ⊤
      [{ fun values => iprop% ∀ (final : MachineStore Universal.State)
        (_observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) final 0 [] 0 -∗
          ⌜values = [] ∧ final.wasm.host.stdio.output = encode input⌝ }] := by
  let R : IProp (WasmHeapGF Universal.State) := iprop(
    hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
    hostStateOwn store.wasm.host ∗
    pointsTo_u32 0 1048544 (finalStore.wasm.mem.read32 1048544) ∗
    pointsTo_u32 0 1048548 (finalStore.wasm.mem.read32 1048548) ∗
    pointsTo_u32 0 1048564 inputCapacity ∗
    pointsTo_u32 0 1048568 inputPtr ∗
    pointsTo_u32 0 1048572 (UInt32.ofNat input.length))
  iintro ⟨HR, Hruntime0, HglobalAt, HcapCall, HoutputPtrCall, HzeroCall,
    H3Call, H4Call, H5Call, H6Call, HresultPairCall, HresultLenCall,
    Hinput, Htable, Hout⟩
  iapply (Submission.TotalEncodeFunction.func6_after_alloc_nonempty
    (s := Stuckness.NotStuck) (E := ⊤)
    (Φ := fun values => iprop% ∀ (final : MachineStore Universal.State)
      (_observations : List StepKind),
      stateInterp (GF := WasmHeapGF Universal.State) final 0 [] 0 -∗
        ⌜values = [] ∧ final.wasm.host.stdio.output = encode input⌝)
    1048552 inputPtr 1048512 output input out
    (finalStore.wasm.mem.read32 1048528)
    (finalStore.wasm.mem.read32 1048532)
    (finalStore.wasm.mem.read32 1048536)
    (finalStore.wasm.mem.read32 1048540)
    ((finalStore.wasm.mem.read32 1048552).toUInt64 |||
      ((finalStore.wasm.mem.read32 1048556).toUInt64 <<< 32))
    (finalStore.wasm.mem.read32 1048560) R
    hinput houtLen (by omega) (by decide) (by
      have hpos : 0 < input.length := List.length_pos_iff.mpr hinput
      omega)
    (by decide) (arity := 0) (remainder := []) (controls := [])
    (calls := encodeMainCalls store inputPtr)) $$
    [$HR $Hruntime0 $HglobalAt $HcapCall $HoutputPtrCall $HzeroCall
      $H3Call $H4Call $H5Call $H6Call $HresultPairCall $HresultLenCall
      $Hinput $Htable $Hout]
  iintro HR Hruntime Hglobal HcapResult HptrResult HlenResult Hsentinel
    Hcursor Hinput Htable Hencoded %finalLocals
  isimp only [R] at HR
  icases HR with ⟨Henv, Hhost, H7, H8, HinputCap, HinputPtr, HinputLen⟩
  simp only [encodeMainCalls]
  rw [hentry]
  iapply Submission.TotalIterator.hdtwp_returnFromCallFallthrough' $$ Hruntime
  iintro Hruntime
  simp only [List.take_zero, List.nil_append]
  ihave HsentinelAt : pointsTo_u32 0 ((1048544 : UInt32) - 16)
      Submission.TotalIterator.sentinel $$ [Hsentinel]
  · rw [show (1048544 : UInt32) - 16 = 1048512 + 16 by decide]
    iexact Hsentinel
  ihave HcursorAt : pointsTo_u32 0 (((1048544 : UInt32) - 16) + 4)
      (inputPtr + UInt32.ofNat input.length) $$ [Hcursor]
  · rw [show ((1048544 : UInt32) - 16) + 4 = 1048512 + 20 by decide]
    iexact Hcursor
  ihave HsentinelBytes := (pointsTo_u32_as_bytes 0
    ((1048544 : UInt32) - 16) Submission.TotalIterator.sentinel).mp $$ HsentinelAt
  isimp only [pointsToBytes] at HsentinelBytes
  icases HsentinelBytes with ⟨HwriteTag, _HsentinelRest⟩
  ihave HglobalMain : globalPointsToAt 0 0 (.i32 1048544) $$ [Hglobal]
  · rw [show (1048512 : UInt32) + 32 = 1048544 by decide]
    iexact Hglobal
  ihave HcapMain : pointsTo_u32 0 ((1048544 : UInt32) + 8)
      outputCapacity $$ [HcapResult]
  · rw [show (1048544 : UInt32) + 8 = 1048552 by decide,
      hcapacityEq]
    iexact HcapResult
  ihave HptrMain : pointsTo_u32 0 ((1048544 : UInt32) + 12)
      output $$ [HptrResult]
  · rw [show (1048544 : UInt32) + 12 = 1048556 by decide,
      ← show (1048552 : UInt32) + 4 = 1048556 by decide]
    iexact HptrResult
  ihave HlenMain : pointsTo_u32 0 ((1048544 : UInt32) + 16)
      (UInt32.ofNat (encode input).length) $$ [HlenResult]
  · rw [show (1048544 : UInt32) + 16 = 1048560 by decide,
      ← show (1048552 : UInt32) + 8 = 1048560 by decide]
    iexact HlenResult
  ihave HinputCapMain : pointsTo_u32 0 ((1048544 : UInt32) + 20)
      inputCapacity $$ [HinputCap]
  · rw [show (1048544 : UInt32) + 20 = 1048564 by decide]
    iexact HinputCap
  ihave HinputPtrMain : pointsTo_u32 0 ((1048544 : UInt32) + 24)
      inputPtr $$ [HinputPtr]
  · rw [show (1048544 : UInt32) + 24 = 1048568 by decide]
    iexact HinputPtr
  ihave HinputLenMain : pointsTo_u32 0 ((1048544 : UInt32) + 28)
      (UInt32.ofNat input.length) $$ [HinputLen]
  · rw [show (1048544 : UInt32) + 28 = 1048572 by decide]
    iexact HinputLen
  iapply (main_after_encode_finishes input store inputCapacity inputPtr output
    outputCapacity hinput hhostOutput hcapacityNat hlimitSmall
    hinputCapacityNe) $$
    [$Hruntime $Henv $Hhost $HglobalMain $HcapMain $HptrMain $HlenMain
      $HinputCapMain $HinputPtrMain $HinputLenMain $Hinput $Hencoded
      $HwriteTag $HcursorAt]

set_option maxRecDepth 100000000 in
private theorem split_output_memory {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    (input : List UInt8) (finalStore : MachineStore Universal.State)
    (output : UInt32)
    (hlimitSmall : output.toNat + 2 * input.length < UInt32.size) :
    pointsToBytes 0 0
        (Submission.Grow.bytesAt finalStore.wasm.mem 0
          (output.toNat + 2 * input.length)) ⊢
      pointsToBytes 0 0
          (Submission.Grow.bytesAt finalStore.wasm.mem 0 output.toNat) ∗
        pointsToBytes 0 output
          (Submission.Grow.bytesAt finalStore.wasm.mem output
            (2 * input.length)) := by
  iintro Hbytes
  ihave HoutputDecomp : pointsToBytes 0 0
      (Submission.Grow.bytesAt finalStore.wasm.mem 0 output.toNat ++
        (Submission.Grow.bytesAt finalStore.wasm.mem output
            (2 * input.length) ++
          Submission.Grow.bytesAt finalStore.wasm.mem
            (output + UInt32.ofNat (2 * input.length)) 0)) $$ [Hbytes]
  · have heq : Submission.Grow.bytesAt finalStore.wasm.mem 0
        (output.toNat + 2 * input.length) =
        Submission.Grow.bytesAt finalStore.wasm.mem 0 output.toNat ++
          (Submission.Grow.bytesAt finalStore.wasm.mem output
              (2 * input.length) ++
            Submission.Grow.bytesAt finalStore.wasm.mem
              (output + UInt32.ofNat (2 * input.length)) 0) := by
        simpa using Submission.FullMemory.full_bytes_decompose
          finalStore.wasm.mem output (2 * input.length)
          (output.toNat + 2 * input.length) (by omega) hlimitSmall
    rw [← heq]
    iexact Hbytes
  ihave HoutputSplit := (pointsToBytes_append 0 0
      (Submission.Grow.bytesAt finalStore.wasm.mem 0 output.toNat)
      (Submission.Grow.bytesAt finalStore.wasm.mem output (2 * input.length) ++
        Submission.Grow.bytesAt finalStore.wasm.mem
          (output + UInt32.ofNat (2 * input.length)) 0)).mp $$ HoutputDecomp
  icases HoutputSplit with ⟨HbeforeOutput, HoutputRest⟩
  ihave HoutputRest' : pointsToBytes 0 output
      (Submission.Grow.bytesAt finalStore.wasm.mem output (2 * input.length) ++
        Submission.Grow.bytesAt finalStore.wasm.mem
          (output + UInt32.ofNat (2 * input.length)) 0) $$ [HoutputRest]
  · simp only [Submission.Grow.bytesAt_length, UInt32.ofNat_toNat,
      UInt32.zero_add]
    iexact HoutputRest
  ihave HoutputSplit := (pointsToBytes_append 0 output
      (Submission.Grow.bytesAt finalStore.wasm.mem output (2 * input.length))
      (Submission.Grow.bytesAt finalStore.wasm.mem
        (output + UInt32.ofNat (2 * input.length)) 0)).mp $$ HoutputRest'
  icases HoutputSplit with ⟨HoutputBytes, _HafterOutput⟩
  isplitl [HbeforeOutput]
  · iexact HbeforeOutput
  · iexact HoutputBytes

set_option maxRecDepth 100000000 in
private theorem split_input_memory {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    (input : List UInt8) (finalStore : MachineStore Universal.State)
    (inputPtr output : UInt32)
    (hlimitSmall : output.toNat + 2 * input.length < UInt32.size)
    (hinputEnd : inputPtr.toNat + input.length ≤ output.toNat) :
    pointsToBytes 0 0
        (Submission.Grow.bytesAt finalStore.wasm.mem 0 output.toNat) ⊢
      pointsToBytes 0 0
          (Submission.Grow.bytesAt finalStore.wasm.mem 0 inputPtr.toNat) ∗
        pointsToBytes 0 inputPtr
          (Submission.Grow.bytesAt finalStore.wasm.mem inputPtr input.length) := by
  iintro HbeforeOutput
  ihave HinputDecomp : pointsToBytes 0 0
      (Submission.Grow.bytesAt finalStore.wasm.mem 0 inputPtr.toNat ++
        (Submission.Grow.bytesAt finalStore.wasm.mem inputPtr input.length ++
          Submission.Grow.bytesAt finalStore.wasm.mem
            (inputPtr + UInt32.ofNat input.length)
            (output.toNat - (inputPtr.toNat + input.length)))) $$ [HbeforeOutput]
  · rw [← Submission.FullMemory.full_bytes_decompose finalStore.wasm.mem
      inputPtr input.length output.toNat hinputEnd
      (lt_of_le_of_lt (Nat.le_add_right _ _) hlimitSmall)]
    iexact HbeforeOutput
  ihave HinputSplit := (pointsToBytes_append 0 0
      (Submission.Grow.bytesAt finalStore.wasm.mem 0 inputPtr.toNat)
      (Submission.Grow.bytesAt finalStore.wasm.mem inputPtr input.length ++
        Submission.Grow.bytesAt finalStore.wasm.mem
          (inputPtr + UInt32.ofNat input.length)
          (output.toNat - (inputPtr.toNat + input.length)))).mp $$ HinputDecomp
  icases HinputSplit with ⟨HbeforeInput, HinputRest⟩
  ihave HinputRest' : pointsToBytes 0 inputPtr
      (Submission.Grow.bytesAt finalStore.wasm.mem inputPtr input.length ++
        Submission.Grow.bytesAt finalStore.wasm.mem
          (inputPtr + UInt32.ofNat input.length)
          (output.toNat - (inputPtr.toNat + input.length))) $$ [HinputRest]
  · simp only [Submission.Grow.bytesAt_length, UInt32.ofNat_toNat,
      UInt32.zero_add]
    iexact HinputRest
  ihave HinputSplit := (pointsToBytes_append 0 inputPtr
      (Submission.Grow.bytesAt finalStore.wasm.mem inputPtr input.length)
      (Submission.Grow.bytesAt finalStore.wasm.mem
        (inputPtr + UInt32.ofNat input.length)
        (output.toNat - (inputPtr.toNat + input.length)))).mp $$ HinputRest'
  icases HinputSplit with ⟨HinputBytes, _Hgap⟩
  isplitl [HbeforeInput]
  · iexact HbeforeInput
  · iexact HinputBytes

set_option maxRecDepth 10000000 in
private theorem split_memory_segment {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    (mem : Mem) (limit start : UInt32) (len : Nat)
    (hsegment : start.toNat + len ≤ limit.toNat) :
    pointsToBytes 0 0
        (Submission.Grow.bytesAt mem 0 limit.toNat) ⊢
      pointsToBytes 0 start
        (Submission.Grow.bytesAt mem start len) := by
  iintro Hbytes
  ihave Hdecomp : pointsToBytes 0 0
      (Submission.Grow.bytesAt mem 0 start.toNat ++
        (Submission.Grow.bytesAt mem start len ++
          Submission.Grow.bytesAt mem (start + UInt32.ofNat len)
            (limit.toNat - (start.toNat + len)))) $$ [Hbytes]
  · rw [← Submission.FullMemory.full_bytes_decompose mem start len
      limit.toNat hsegment (UInt32.toNat_lt_size limit)]
    iexact Hbytes
  ihave Hsplit := (pointsToBytes_append 0 0
      (Submission.Grow.bytesAt mem 0 start.toNat)
      (Submission.Grow.bytesAt mem start len ++
        Submission.Grow.bytesAt mem (start + UInt32.ofNat len)
          (limit.toNat - (start.toNat + len)))).mp $$ Hdecomp
  icases Hsplit with ⟨_Hbefore, Hrest⟩
  ihave Hrest' : pointsToBytes 0 start
      (Submission.Grow.bytesAt mem start len ++
        Submission.Grow.bytesAt mem (start + UInt32.ofNat len)
          (limit.toNat - (start.toNat + len))) $$ [Hrest]
  · simp only [Submission.Grow.bytesAt_length, UInt32.ofNat_toNat,
      UInt32.zero_add]
    iexact Hrest
  ihave Hsplit := (pointsToBytes_append 0 start
      (Submission.Grow.bytesAt mem start len)
      (Submission.Grow.bytesAt mem (start + UInt32.ofNat len)
        (limit.toNat - (start.toNat + len)))).mp $$ Hrest'
  icases Hsplit with ⟨Hsegment, _Hafter⟩
  iexact Hsegment

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 100000000 in
private theorem split_encode_memory {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    (input : List UInt8) (finalStore : MachineStore Universal.State)
    (inputPtr output : UInt32)
    (hlimitSmall : output.toNat + 2 * input.length < UInt32.size)
    (hinputEnd : inputPtr.toNat + input.length ≤ output.toNat)
    (hstackEnd : 1048516 + 76 ≤ inputPtr.toNat) :
    pointsToBytes 0 0
        (Submission.Grow.bytesAt finalStore.wasm.mem 0
          (output.toNat + 2 * input.length)) ⊢
      pointsToBytes 0 1048516
          (Submission.Grow.bytesAt finalStore.wasm.mem 1048516 76) ∗
        pointsToBytes 0 inputPtr
          (Submission.Grow.bytesAt finalStore.wasm.mem inputPtr input.length) ∗
        pointsToBytes 0 output
          (Submission.Grow.bytesAt finalStore.wasm.mem output
            (2 * input.length)) := by
  iintro Hbytes
  ihave HoutputSplit := split_output_memory input finalStore output
    hlimitSmall $$ Hbytes
  icases HoutputSplit with ⟨HbeforeOutput, HoutputBytes⟩
  ihave HinputSplit := split_input_memory input finalStore inputPtr output
    hlimitSmall hinputEnd $$ HbeforeOutput
  icases HinputSplit with ⟨HbeforeInput, HinputBytes⟩
  ihave HstackTable := split_memory_segment finalStore.wasm.mem inputPtr
    1048516 76 hstackEnd $$ HbeforeInput
  isplitl [HstackTable]
  · iexact HstackTable
  · isplitl [HinputBytes]
    · iexact HinputBytes
    · iexact HoutputBytes

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000000 in
private theorem encode_prefix_finishes {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    (input : List UInt8) (store finalStore : MachineStore Universal.State)
    (inputCapacity inputPtr output outputCapacity : UInt32)
    (hinput : input ≠ [])
    (hentry : store.runtime.entry = ⟨0⟩)
    (hhostOutput : store.wasm.host.stdio.output = [])
    (hcapacityEq : outputCapacity =
      UInt32.ofNat (Submission.TotalEncodeLoop.encodeCapacityNat input))
    (hcapacityNat : outputCapacity.toNat = max 8 (2 * input.length))
    (hlimitSmall : output.toNat + 2 * input.length < UInt32.size)
    (hfinalRuntimeEq : finalStore.runtime = store.runtime)
    (hinputCapacityNe : inputCapacity ≠ 0)
    (hfinalRuntime : finalStore.runtime.currentModule = «module»)
    (hfinalEnv : finalStore.runtime.currentHost = Universal.envFor «module»)
    (hfinalHost : finalStore.wasm.host = store.wasm.host)
    (hfinalTable : finalStore.wasm.mem.readBytes 1048576 16 =
      Submission.Hex.asciiTable)
    (hfinalInput :
      finalStore.wasm.mem.readBytes inputPtr.toNat input.length = input)
    (hfinalCapacity : finalStore.wasm.mem.read32 1048516 = outputCapacity)
    (hfinalOutput : finalStore.wasm.mem.read32 1048520 = output)
    (hfinalZero : finalStore.wasm.mem.read32 1048524 = 0)
    (hfinalInputCapacity :
      finalStore.wasm.mem.read32 1048564 = inputCapacity)
    (hfinalInputPtr : finalStore.wasm.mem.read32 1048568 = inputPtr)
    (hfinalInputLen : finalStore.wasm.mem.read32 1048572 =
      UInt32.ofNat input.length)
    (hinputEnd : inputPtr.toNat + input.length ≤ output.toNat)
    (hstackEnd : 1048516 + 76 ≤ inputPtr.toNat) :
    pointsToBytes 0 0
        (Submission.Grow.bytesAt finalStore.wasm.mem 0
          (output.toNat + 2 * input.length)) ∗
      ([∗map] index ↦ value ∈
        (insert (∅ : WasmGlobalMap Value)
          (⟨0, 0⟩ : GlobalKey) (.i32 1048512)),
        globalPointsTo index value) ∗
      runtimeModuleOwn finalStore.runtime.entry
        finalStore.runtime.currentModule ∗
      hostEnvOwn finalStore.runtime.entry.id finalStore.runtime.currentHost ∗
      hostStateOwn finalStore.wasm.host ⊢
    WP (.running
      ⟨⟨[.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)],
          [.i32 1048512,
            .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
            .i32 0, .i32 0], []⟩,
        Project.HexStdio.func6.drop 16, 0, [], [],
        encodeMainCalls store inputPtr⟩ : Expr Universal.State)
      @ Stuckness.NotStuck; ⊤
      [{ fun values => iprop% ∀ (final : MachineStore Universal.State)
        (_observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) final 0 [] 0 -∗
          ⌜values = [] ∧ final.wasm.host.stdio.output = encode input⌝ }] := by
  let body : Config Universal.State :=
    ⟨.running
      ⟨⟨[.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)],
          [.i32 1048512,
            .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
            .i32 0, .i32 0], []⟩,
        Project.HexStdio.func6.drop 16, 0, [], [],
        encodeMainCalls store inputPtr⟩,
      finalStore⟩
  let globalσ : WasmGlobalMap Value :=
    insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 1048512)
  iintro ⟨Hbytes, Hglobals, Hruntime, Henv, Hhost⟩
  ihave HglobalAt : globalPointsToAt 0 0 (.i32 1048512) $$ [Hglobals]
  · rw [globalPointsToAt_eq]
    iapply (BI.BigSepM.bigSepM_singleton (M := WasmGlobalMap)).mp
    rw [PartialMap.singleton]
    iexact Hglobals
  ihave Hmemory := split_encode_memory input finalStore inputPtr output
    hlimitSmall hinputEnd hstackEnd $$ Hbytes
  icases Hmemory with ⟨HstackTable, HinputBytes, HoutputBytes⟩
  ihave HstackTableSplit := (Submission.PrefixMemory.bytesAt_split
      finalStore.wasm.mem 1048516 60 16 (by decide)).mp $$ HstackTable
  icases HstackTableSplit with ⟨Hstack, HtableBytes⟩
  ihave Htable : pointsToBytes 0 1048576 Submission.Hex.asciiTable $$ [HtableBytes]
  · rw [show (1048516 : UInt32) + UInt32.ofNat 60 = 1048576 by decide]
    rw [Submission.FullMemory.bytesAt_eq_readBytes finalStore.wasm.mem
      1048576 16 (by decide),
      show (1048576 : UInt32).toNat = 1048576 by decide, hfinalTable]
    iexact HtableBytes
  ihave Hinput : pointsToBytes 0 inputPtr input $$ [HinputBytes]
  · rw [Submission.FullMemory.bytesAt_eq_readBytes finalStore.wasm.mem
      inputPtr input.length (by omega), hfinalInput]
    iexact HinputBytes
  let out := Submission.Grow.bytesAt finalStore.wasm.mem output
    (2 * input.length)
  ihave Hout : pointsToBytes 0 output out $$ [HoutputBytes]
  · iexact HoutputBytes
  have houtLen : out.length = 2 * input.length := by
    simp [out]
  ihave Hwords := Submission.PrefixMemory.bytesAt_words
    finalStore.wasm.mem 1048516 15 (by decide) $$ Hstack
  isimp only [Submission.PrefixMemory.wordsAt, arrayAt] at Hwords
  isimp only [UInt32.reduceAdd] at Hwords
  icases Hwords with ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9,
    H10, H11, H12, H13, H14⟩
  icases H14 with ⟨H14, _Hemp⟩
  ihave Hcap : pointsTo_u32 0 1048516 outputCapacity $$ [H0]
  · rw [hfinalCapacity]
    iexact H0
  ihave HoutputPtr : pointsTo_u32 0 1048520 output $$ [H1]
  · rw [hfinalOutput]
    iexact H1
  ihave Hzero : pointsTo_u32 0 1048524 0 $$ [H2]
  · rw [hfinalZero]
    iexact H2
  ihave HinputCap : pointsTo_u32 0 1048564 inputCapacity $$ [H12]
  · rw [hfinalInputCapacity]
    iexact H12
  ihave HinputPtr : pointsTo_u32 0 1048568 inputPtr $$ [H13]
  · rw [hfinalInputPtr]
    iexact H13
  ihave HinputLen : pointsTo_u32 0 1048572
      (UInt32.ofNat input.length) $$ [H14]
  · rw [hfinalInputLen]
    iexact H14
  ihave HpairCells : pointsTo_u32 0 1048552
      (finalStore.wasm.mem.read32 1048552) ∗
      pointsTo_u32 0 (1048552 + 4)
        (finalStore.wasm.mem.read32 1048556) $$ [H9 H10]
  · isplitl [H9]
    · iexact H9
    · rw [show (1048552 : UInt32) + 4 = 1048556 by decide]
      iexact H10
  ihave HresultPair := Submission.Helpers.pointsTo_u64_pair_join
    0 1048552 (finalStore.wasm.mem.read32 1048552)
      (finalStore.wasm.mem.read32 1048556) $$ HpairCells
  let R : IProp (WasmHeapGF Universal.State) := iprop(
    hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
    hostStateOwn store.wasm.host ∗
    pointsTo_u32 0 1048544 (finalStore.wasm.mem.read32 1048544) ∗
    pointsTo_u32 0 1048548 (finalStore.wasm.mem.read32 1048548) ∗
    pointsTo_u32 0 1048564 inputCapacity ∗
    pointsTo_u32 0 1048568 inputPtr ∗
    pointsTo_u32 0 1048572 (UInt32.ofNat input.length))
  ihave HR : R $$ [Henv Hhost H7 H8 HinputCap HinputPtr HinputLen]
  · unfold R
    isplitl [Henv]
    · rw [← show body.store.runtime.entry.id = 0 by
          change finalStore.runtime.entry.id = 0
          rw [hfinalRuntimeEq, hentry]]
      rw [← show body.store.runtime.currentHost = Universal.envFor
          Project.HexStdio.«module» by simpa [body] using hfinalEnv]
      iexact Henv
    · isplitl [Hhost]
      · rw [← show body.store.wasm.host = store.wasm.host by
            simpa [body] using hfinalHost]
        iexact Hhost
      · iframe
  ihave Hruntime0 : runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» $$ [Hruntime]
  · rw [← hentry]
    rw [← show body.store.runtime.currentModule = Project.HexStdio.«module» by
      simpa [body] using hfinalRuntime]
    rw [← show body.store.runtime.entry = store.runtime.entry by
      change finalStore.runtime.entry = store.runtime.entry
      rw [hfinalRuntimeEq]]
    iexact Hruntime
  ihave HcapCall : pointsTo_u32 0 ((1048512 : UInt32) + 4)
      (UInt32.ofNat (Submission.TotalEncodeLoop.encodeCapacityNat input)) $$ [Hcap]
  · rw [show (1048512 : UInt32) + 4 = 1048516 by decide,
      ← hcapacityEq]
    iexact Hcap
  ihave HoutputPtrCall : pointsTo_u32 0 ((1048512 : UInt32) + 8)
      output $$ [HoutputPtr]
  · rw [show (1048512 : UInt32) + 8 = 1048520 by decide]
    iexact HoutputPtr
  ihave HzeroCall : pointsTo_u32 0 ((1048512 : UInt32) + 12) 0 $$ [Hzero]
  · rw [show (1048512 : UInt32) + 12 = 1048524 by decide]
    iexact Hzero
  ihave H3Call : pointsTo_u32 0 ((1048512 : UInt32) + 16)
      (finalStore.wasm.mem.read32 1048528) $$ [H3]
  · rw [show (1048512 : UInt32) + 16 = 1048528 by decide]
    iexact H3
  ihave H4Call : pointsTo_u32 0 ((1048512 : UInt32) + 20)
      (finalStore.wasm.mem.read32 1048532) $$ [H4]
  · rw [show (1048512 : UInt32) + 20 = 1048532 by decide]
    iexact H4
  ihave H5Call : pointsTo_u32 0 ((1048512 : UInt32) + 24)
      (finalStore.wasm.mem.read32 1048536) $$ [H5]
  · rw [show (1048512 : UInt32) + 24 = 1048536 by decide]
    iexact H5
  ihave H6Call : pointsTo_u32 0 ((1048512 : UInt32) + 28)
      (finalStore.wasm.mem.read32 1048540) $$ [H6]
  · rw [show (1048512 : UInt32) + 28 = 1048540 by decide]
    iexact H6
  ihave HresultPairCall : pointsTo_u64 0 ((1048552 : UInt32) + 0)
      ((finalStore.wasm.mem.read32 1048552).toUInt64 |||
        ((finalStore.wasm.mem.read32 1048556).toUInt64 <<< 32)) $$ [HresultPair]
  · simp only [UInt32.add_zero]
    iexact HresultPair
  ihave HresultLenCall : pointsTo_u32 0 ((1048552 : UInt32) + 8)
      (finalStore.wasm.mem.read32 1048560) $$ [H11]
  · rw [show (1048552 : UInt32) + 8 = 1048560 by decide]
    iexact H11
  iapply (encode_function_finishes input store finalStore inputCapacity
    inputPtr output outputCapacity out hinput houtLen hentry hhostOutput
    hcapacityEq hcapacityNat hlimitSmall hinputEnd hinputCapacityNe) $$
    [$HR $Hruntime0 $HglobalAt $HcapCall $HoutputPtrCall $HzeroCall
      $H3Call $H4Call $H5Call $H6Call $HresultPairCall $HresultLenCall
      $Hinput $Htable $Hout]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000000 in
private theorem encode_after_alloc_finish
    (input : List UInt8)
    (store finalStore : MachineStore Universal.State)
    (inputCapacity inputPtr output outputCapacity : UInt32)
    (hinput : input ≠ [])
    (hentry : store.runtime.entry = ⟨0⟩)
    (hhostOutput : store.wasm.host.stdio.output = [])
    (hcapacityEq : outputCapacity =
      UInt32.ofNat (Submission.TotalEncodeLoop.encodeCapacityNat input))
    (hcapacityNat : outputCapacity.toNat = max 8 (2 * input.length))
    (hlimitSmall : output.toNat + 2 * input.length < UInt32.size)
    (hlimitBound :
      output.toNat + 2 * input.length ≤ finalStore.wasm.mem.pages * 65536)
    (hfinalRuntimeEq : finalStore.runtime = store.runtime)
    (hinputCapacityNe : inputCapacity ≠ 0)
    (hglobalAgreeArg : globalHeapAgrees
      (insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 1048512))
      finalStore.wasm.globals)
    (hwfStore : store.runtime.entry.id < store.runtime.instances.size)
    (hfinalRuntime : finalStore.runtime.currentModule = «module»)
    (hfinalEnv :
      finalStore.runtime.currentHost = Universal.envFor «module»)
    (hfinalHost : finalStore.wasm.host = store.wasm.host)
    (hfinalTable : finalStore.wasm.mem.readBytes 1048576 16 =
      Submission.Hex.asciiTable)
    (hfinalInput :
      finalStore.wasm.mem.readBytes inputPtr.toNat input.length = input)
    (hfinalCapacity :
      finalStore.wasm.mem.read32 1048516 = outputCapacity)
    (hfinalOutput : finalStore.wasm.mem.read32 1048520 = output)
    (hfinalZero : finalStore.wasm.mem.read32 1048524 = 0)
    (hfinalInputCapacity :
      finalStore.wasm.mem.read32 1048564 = inputCapacity)
    (hfinalInputPtr : finalStore.wasm.mem.read32 1048568 = inputPtr)
    (hfinalInputLen : finalStore.wasm.mem.read32 1048572 =
      UInt32.ofNat input.length)
    (hinputEnd : inputPtr.toNat + input.length ≤ output.toNat)
    (hstackEnd : 1048516 + 76 ≤ inputPtr.toNat) :
    TerminatesWith
      ⟨.running
        ⟨⟨[.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)],
            [.i32 1048512,
              .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
              .i32 0, .i32 0], []⟩,
          Project.HexStdio.func6.drop 16, 0, [], [],
          encodeMainCalls store inputPtr⟩,
        finalStore⟩
      (fun values final => values = [] ∧
        final.wasm.host.stdio.output = encode input) := by
  let body : Config Universal.State :=
    ⟨.running
      ⟨⟨[.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)],
          [.i32 1048512,
            .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
            .i32 0, .i32 0], []⟩,
        Project.HexStdio.func6.drop 16, 0, [], [],
        encodeMainCalls store inputPtr⟩,
      finalStore⟩
  let globalσ : WasmGlobalMap Value :=
    insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 1048512)
  have hglobalAgree : globalHeapAgrees globalσ finalStore.wasm.globals := by
    simpa [globalσ] using hglobalAgreeArg
  apply Submission.PrefixMemory.terminates body
    (output.toNat + 2 * input.length) globalσ
    (fun values final => values = [] ∧
      final.wasm.host.stdio.output = encode input)
    hlimitSmall
    (by simpa [body] using hlimitBound)
    (by simpa [body] using hglobalAgree)
    (by
      change finalStore.runtime.entry.id < finalStore.runtime.instances.size
      rw [hfinalRuntimeEq]
      exact hwfStore)
  intro hlc _
  simpa only [body, globalσ] using
    encode_prefix_finishes input store finalStore inputCapacity inputPtr
      output outputCapacity hinput hentry hhostOutput hcapacityEq hcapacityNat
      hlimitSmall hfinalRuntimeEq hinputCapacityNe hfinalRuntime hfinalEnv
      hfinalHost hfinalTable hfinalInput hfinalCapacity hfinalOutput hfinalZero
      hfinalInputCapacity hfinalInputPtr hfinalInputLen hinputEnd hstackEnd


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000000 in
theorem encode_after_alloc_terminates
    (input : List UInt8) (store : MachineStore Universal.State)
    (inputCapacity inputPtr inputBump : UInt32)
    (allocStore : MachineStore Universal.State)
    (hinput : input ≠ [])
    (hcapacityArg : store.wasm.mem.read32 1048564 = inputCapacity)
    (hptrArg : store.wasm.mem.read32 (1048564 + 4) = inputPtr)
    (hbumpArg : store.wasm.mem.read32 1053960 = inputBump)
    (hread : ReadToEndSuccess input (encodeAfterReadConfig store))
    (halloc : ByteGrowSuccess
      (reserveFrameStore (encodeAllocFrameStore store) (1048512 - 16))
      0 1 (reserveNewCapacity 0 (UInt32.ofNat input.length <<< 1) 0)
      inputBump allocStore) :
    TerminatesWith
      (growResultFinal
        (encodeOutputStore allocStore (allocatorPtr inputBump 1)
          (reserveNewCapacity 0 (UInt32.ofNat input.length <<< 1) 0))
        [.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)]
        [.i32 1048512,
          .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
          .i32 0, .i32 0]
        [] [] 0 [] encodeReserveControls (encodeMainCalls store inputPtr))
      (fun values final => values = [] ∧
        final.wasm.host.stdio.output = encode input) := by
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
  let body : Config Universal.State :=
    ⟨.running
      ⟨⟨[.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)],
          [.i32 1048512,
            .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
            .i32 0, .i32 0], []⟩,
        Project.HexStdio.func6.drop 16, 0, [], [],
        encodeMainCalls store inputPtr⟩,
      finalStore⟩
  have hprefix : Reaches
      (growResultFinal finalStore
        [.i32 1048552, .i32 inputPtr, .i32 (UInt32.ofNat input.length)]
        [.i32 1048512,
          .i32 (inputPtr + UInt32.ofNat input.length), .i32 0, .i32 0,
          .i32 0, .i32 0]
        [] [] 0 [] encodeReserveControls (encodeMainCalls store inputPtr))
      body := by
    apply Reaches.prepend (Step.exitControl rfl)
    simp [growResultFinal, body, encodeReserveControls]
    exact ⟨[], .refl _⟩
  apply TerminatesWith.prependReaches hprefix
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
      UInt32.ofNat (Submission.TotalEncodeLoop.encodeCapacityNat input) :=
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
  have hfinishSmall :
      (allocatorFinish outputCapacity 1 inputBump).toNat < 2 ^ 31 := by
    cases halloc with
    | freshNoGrow hzero hfit hnonnegative =>
        exact UInt32.toNat_lt_signed_limit_of_not_negative _ hnonnegative
    | freshGrow hzero memory previousPages hnotfit hgrow hnonnegative =>
        exact UInt32.toNat_lt_signed_limit_of_not_negative _ hnonnegative
    | reallocNoGrow hnonzero => contradiction
    | reallocGrow hnonzero => contradiction
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
      simpa [outputCapacity, finalStore, encodeOutputStore] using hfinishBound
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
    cases halloc with
    | freshNoGrow => rfl
    | freshGrow => rfl
    | reallocNoGrow hnonzero => contradiction
    | reallocGrow hnonzero => contradiction
  have hfinalGlobal : globalAt? finalStore 0 = some (.i32 1048512) := by
    simp only [finalStore, encodeOutputStore, reserveFinishStore,
      reserveVectorStore, globalAt?, canonicalGlobalIndex_zero]
    apply List.getElem?_set_self
    have hlen : allocStore.wasm.globals.globals.length =
        store.wasm.globals.globals.length := by
      cases halloc with
      | freshNoGrow => simp [allocatorBumpStore, reserveFrameStore,
          encodeAllocFrameStore]
      | freshGrow => simp [allocatorBumpStore, allocatorGrownStore,
          reserveFrameStore, encodeAllocFrameStore]
      | reallocNoGrow hnonzero => contradiction
      | reallocGrow hnonzero => contradiction
    simp only [growResultOkStore]
    rw [hlen]
    exact (getElem?_eq_some_iff.mp hglobal).1
  let globalσ : WasmGlobalMap Value :=
    insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 1048512)
  have hglobalAgree : globalHeapAgrees globalσ finalStore.wasm.globals := by
    intro index value hget
    by_cases hi : index = 0
    · subst index
      rw [get?_insert_eq rfl] at hget
      cases hget
      simpa [globalAt?, canonicalGlobalIndex_zero] using hfinalGlobal
    · have hk : (⟨0, index⟩ : GlobalKey) ≠ ⟨0, 0⟩ := by
        intro heq
        exact hi (congrArg GlobalKey.index heq)
      rw [get?_insert_ne (Ne.symm hk), get?_empty] at hget
      contradiction
  have hwfStore : store.runtime.entry.id < store.runtime.instances.size := by
    by_contra hn
    have hdefault : store.runtime.currentModule =
        (default : ModuleInstance Universal.State).module := by
      rw [RuntimeEnv.currentModule, RuntimeEnv.currentInstance,
        getElem!_neg _ _ (by simpa using hn)]
    have hlenmod := congrArg (fun m : Module => m.funcs.length)
      (hdefault.symm.trans hmod)
    exact (by decide :
      (default : ModuleInstance Universal.State).module.funcs.length ≠
        Project.HexStdio.«module».funcs.length) hlenmod
  have hfinalTable : finalStore.wasm.mem.readBytes 1048576 16 =
      Submission.Hex.asciiTable := by
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
  have hfinalInputCapacity : finalStore.wasm.mem.read32 1048564 =
      inputCapacity := by
    rw [encodeOutputStore_preserves_read32 allocStore output outputCapacity
      1048564 (by decide)]
    rw [halloc.fresh_preserves_read32 (by decide)]
    simp only [reserveFrameStore, encodeAllocFrameStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hcapacityArg
    all_goals decide
  have hfinalInputPtr : finalStore.wasm.mem.read32 1048568 = inputPtr := by
    rw [encodeOutputStore_preserves_read32 allocStore output outputCapacity
      1048568 (by decide)]
    rw [halloc.fresh_preserves_read32 (by decide)]
    simp only [reserveFrameStore, encodeAllocFrameStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hptrArg
    all_goals decide
  have hfinalInputLen : finalStore.wasm.mem.read32 1048572 =
      UInt32.ofNat input.length := by
    rw [encodeOutputStore_preserves_read32 allocStore output outputCapacity
      1048572 (by decide)]
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
  simpa only [body] using
    encode_after_alloc_finish input store finalStore inputCapacity inputPtr
      output outputCapacity hinput hentry hhostOutput hcapacityEq hcapacityNat
      hlimitSmall hlimitBound (by
        change allocStore.runtime = store.runtime
        exact hallocRuntime) (by
        intro hz
        have hzNat := congrArg UInt32.toNat hz
        simp only [UInt32.toNat_zero] at hzNat
        omega)
      (by simpa [globalσ] using hglobalAgree)
      hwfStore hfinalRuntime hfinalEnv hfinalHost hfinalTable hfinalInput
      hfinalCapacity hfinalOutput hfinalZero hfinalInputCapacity hfinalInputPtr
      hfinalInputLen hinputEnd hstackEnd
end Submission.HexDecodeStdio
