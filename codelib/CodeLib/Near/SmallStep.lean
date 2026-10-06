import CodeLib.Near.Proof
import CodeLib.SepLogic.SmallStepAdequacy
import CodeLib.SepLogic.SmallStepTotalLiftingBytes

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic Wasm.Near

/-! ## NEAR runtime -/

/-- Single-instance NEAR runtime using `nearEnv` as the host environment. -/
def nearRuntime (m : Module) : RuntimeEnv NearState :=
  { instances := #[{ module := m, host := nearEnv }]
    entry := ⟨0⟩ }

/-! ## Transfer theorems for KvSetter host calls -/

/-- Transfer for `input(0)`: stores `ns'.context.input` in register 0.
    Mirror of `incrTransfer` in `CounterHostExample`. -/
theorem twp_near_input {hlc : HasLC} [WasmSmallStepGS hlc NearState]
    (ns' : NearState) (m : Module)
    (store : MachineStore NearState) (ns : Nat) (obs : List StepKind) (nt : Nat)
    (_ : store.runtime.currentModule = m)
    (results : List Value) (postWasm : Store NearState)
    (h : inputFn.invoke store.wasm [.i64 0] = .Return results postWasm) :
    hostStateOwn ns' ∗ stateInterp (GF := WasmHeapGF NearState) store ns obs nt ==∗
      hostStateOwn (ns'.setRegister 0 ns'.context.input) ∗
      stateInterp (GF := WasmHeapGF NearState) { store with wasm := postWasm } ns obs nt := by
  -- Unfold inputFn/writeRegisterResult/checkedSetRegister?, eliminate 0 = u64Max branch,
  -- then split on the withinLimit condition.
  simp only [inputFn, writeRegisterResult, checkedSetRegister?,
             show ¬ (0 : UInt64) = u64Max from by decide, ite_false] at h
  split_ifs at h with hLim
  · simp at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    iintro ⟨HP, Hσ⟩
    imod stateInterp_host_set_expected store ns obs nt ns'
        (ns'.setRegister 0 ns'.context.input) $$ [$Hσ $HP] with ⟨%heq, Hσ, HP'⟩
    rw [heq]
    imodintro
    isplitl_exact HP'
    · iexact Hσ

/-- Transfer for `read_register(0, 0)`: copies register 0 content into memory at offset 0,
    exchanging ghost ownership of `oldBytes` for `data`. The host state is unchanged. -/
theorem twp_near_readRegister {hlc : HasLC} [WasmSmallStepGS hlc NearState]
    (ns' : NearState) (data oldBytes : List UInt8) (m : Module)
    (hReg : ns'.registers 0 = some data)
    (hLen : oldBytes.length = data.length)
    (hnowrap : data.length < UInt32.size)
    (store : MachineStore NearState) (ns : Nat) (obs : List StepKind) (nt : Nat)
    (_ : store.runtime.currentModule = m)
    (results : List Value) (postWasm : Store NearState)
    (h : readRegisterFn.invoke store.wasm [.i64 0, .i64 0] = .Return results postWasm) :
    (hostStateOwn ns' ∗ pointsToBytes 0 (0 : UInt32) oldBytes) ∗
      stateInterp (GF := WasmHeapGF NearState) store ns obs nt ==∗
    (hostStateOwn ns' ∗ pointsToBytes 0 (0 : UInt32) data) ∗
      stateInterp (GF := WasmHeapGF NearState) { store with wasm := postWasm } ns obs nt := by
  iintro ⟨⟨HP, Hpt⟩, Hσ⟩
  -- Derive per-byte physical facts (read-only: retains Hσ, Hpt).
  wasm_points_to_bytes_agree hbfacts, (0 : UInt32), oldBytes, obs $$ [Hσ Hpt]
  -- Derive heq (read-only: retains Hσ, HP).
  ihave %heq : ⌜store.wasm.host = ns'⌝ $$ [Hσ HP]
  · iapply (stateInterp_host_agree store ns obs nt ns'); iframe Hσ HP
  -- Pure: derive register content from heq + hReg.
  have hreg' : store.wasm.host.registers (0 : UInt64).toNat = some data := by
    simp only [show (0 : UInt64).toNat = 0 from rfl]; exact heq.symm ▸ hReg
  -- Pure: derive memory bound for stateInterp_write_bytes.
  have hbound_write : (0 : UInt32).toNat + data.length ≤ store.wasm.mem.pages * 65536 := by
    simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.zero_add]
    rcases Nat.eq_zero_or_pos data.length with hz | hpos
    · omega
    · have hb := pointsToBytes_facts_bound hbfacts (hLen.symm ▸ hpos) (by
          simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.zero_add]
          exact hLen.symm ▸ hnowrap)
      simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.zero_add] at hb
      omega
  have hnowrap_write : (0 : UInt32).toNat + data.length < UInt32.size := by
    simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.zero_add]; exact hnowrap
  -- Pure: verify readRegisterFn succeeds and determine postWasm.
  simp only [readRegisterFn, hreg', show ¬ ((0 : UInt64).toNat + data.length > memBytes store.wasm)
    from by simp [memBytes]; omega] at h
  simp at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2
  -- Ghost update: exchange oldBytes for data in stateInterp, keep HP unchanged.
  imod stateInterp_write_bytes store ns obs nt (0 : UInt32) oldBytes data hLen
      hbound_write hnowrap_write $$ [$Hσ $Hpt] with ⟨Hσ', Hpt'⟩
  imodintro
  isplitr [Hσ']
  · isplitl_exact HP
    · iexact Hpt'
  · simp only [show UInt32.toNat (0 : UInt32) = 0 from rfl]
    iexact Hσ'

/-- Transfer for `storage_write(keyLen, keyPtr, valLen, valPtr, regId)`:
    updates the NEAR storage trie, discarding the `hostStateOwn` ghost resource.
    The caller-supplied resource `P` is passed through unchanged. -/
theorem twp_near_storageWrite {P : IProp (WasmHeapGF NearState)} {hlc : HasLC} [WasmSmallStepGS hlc NearState]
    (ns'' : NearState) (key val : List UInt8) (m : Module)
    (keyLen keyPtr valLen valPtr regId : UInt64)
    (store : MachineStore NearState) (ns : Nat) (obs : List StepKind) (nt : Nat)
    (hView : ns''.context.isView = false)
    (hKeyGet : getMemOrReg store.wasm keyPtr keyLen = some key)
    (hValGet : getMemOrReg store.wasm valPtr valLen = some val)
    (hKeyLim : withinLimit ns''.config.maxStorageKeyLen key.length = true)
    (hValLim : withinLimit ns''.config.maxStorageValueLen val.length = true)
    (hMaxReg : ∀ old, ns''.storage key = some old →
        withinLimit ns''.config.maxRegisterLen old.length = true)
    (_ : store.runtime.currentModule = m)
    (results : List Value) (postWasm : Store NearState)
    (h : storageWriteFn.invoke store.wasm
           [.i64 keyLen, .i64 keyPtr, .i64 valLen, .i64 valPtr, .i64 regId] =
         .Return results postWasm) :
    (hostStateOwn ns'' ∗ P) ∗ stateInterp (GF := WasmHeapGF NearState) store ns obs nt ==∗
    ((∃ ns_final : NearState, hostStateOwn ns_final ∗
        ⌜ns_final.storage key = some val ∧
          ∀ k, k ≠ key → ns_final.storage k = ns''.storage k⌝) ∗ P) ∗
      stateInterp (GF := WasmHeapGF NearState) { store with wasm := postWasm } ns obs nt := by
  iintro ⟨⟨HP, HcP⟩, Hσ⟩
  ihave %heq : ⌜store.wasm.host = ns''⌝ $$ [Hσ HP]
  · iapply (stateInterp_host_agree store ns obs nt ns''); iframe Hσ HP
  -- Pure helpers rewriting ns'' → store.wasm.host
  have hView' : store.wasm.host.context.isView = false := by rw [heq]; exact hView
  have hKeyLim' : withinLimit store.wasm.host.config.maxStorageKeyLen key.length = true := by
    rw [heq]; exact hKeyLim
  have hValLim' : withinLimit store.wasm.host.config.maxStorageValueLen val.length = true := by
    rw [heq]; exact hValLim
  obtain hStorage | ⟨old, hStorage⟩ :
      ns''.storage key = none ∨ ∃ old, ns''.storage key = some old :=
    match ns''.storage key with
    | none => Or.inl rfl
    | some old => Or.inr ⟨old, rfl⟩
  · -- Absent case: no old value; checkedSetRegister? not invoked by storageWriteFn.
    have hStorage' : store.wasm.host.storage key = none := by rw [heq]; exact hStorage
    have hinvoke := storageWriteFn_invoke_absent store.wasm key val keyLen keyPtr valLen valPtr regId
        hView' hKeyGet hValGet hKeyLim' hValLim' hStorage'
    rw [hinvoke] at h; simp at h; obtain ⟨-, rfl⟩ := h
    imod stateInterp_host_set_expected store ns obs nt ns''
        ((ns''.setStorage key val).invalidateIterators) $$ [$Hσ $HP] with ⟨%_, Hσ, HP'⟩
    rw [heq]
    have hStorageFacts :
        ((ns''.setStorage key val).invalidateIterators).storage key = some val ∧
          ∀ k, k ≠ key →
            ((ns''.setStorage key val).invalidateIterators).storage k = ns''.storage k :=
      ⟨by simp [NearState.setStorage, NearState.invalidateIterators],
       fun k hk => by simp [NearState.setStorage, NearState.invalidateIterators, hk]⟩
    imodintro
    isplitl [HP' HcP]
    · isplitr [HcP]
      · iexists (ns''.setStorage key val).invalidateIterators
        isplitl_exact HP'
        · ipureexact hStorageFacts
      · iexact HcP
    · iexact Hσ
  · -- Present case: old value exists; checkedSetRegister? stores old value in regId.
    have hStorage' : store.wasm.host.storage key = some old := by rw [heq]; exact hStorage
    have hLim' : withinLimit store.wasm.host.config.maxRegisterLen old.length = true := by
      rw [heq]; exact hMaxReg old hStorage
    have hChecked : ∃ stReg, checkedSetRegister? store.wasm regId old = some stReg := by
      simp only [checkedSetRegister?]
      by_cases hMax : regId = u64Max
      · exact ⟨store.wasm, by simp [hMax]⟩
      · refine ⟨{ store.wasm with host := store.wasm.host.setRegister regId.toNat old }, ?_⟩
        simp only [hMax, ite_false, ite_eq_left hLim']
    obtain ⟨stReg, hCheckedProof⟩ := hChecked
    have hinvoke := storageWriteFn_invoke_present store.wasm key val old
        keyLen keyPtr valLen valPtr regId stReg
        hView' hKeyGet hValGet hKeyLim' hValLim' hStorage' hCheckedProof
    rw [hinvoke] at h; simp at h; obtain ⟨-, rfl⟩ := h
    imod stateInterp_host_set_expected store ns obs nt ns''
        ((stReg.host.setStorage key val).invalidateIterators) $$ [$Hσ $HP] with ⟨%_, Hσ, HP'⟩
    have hStRegStorage : stReg.host.storage = ns''.storage := by
      rw [← heq]
      simp only [checkedSetRegister?] at hCheckedProof
      split_ifs at hCheckedProof with hMax
      · simp at hCheckedProof; subst hCheckedProof; rfl
      · simp at hCheckedProof; subst hCheckedProof; simp [NearState.setRegister]
    have hStorageFacts :
        ((stReg.host.setStorage key val).invalidateIterators).storage key = some val ∧
          ∀ k, k ≠ key →
            ((stReg.host.setStorage key val).invalidateIterators).storage k = ns''.storage k :=
      ⟨by simp [NearState.setStorage, NearState.invalidateIterators],
       fun k hk => by
         simp [NearState.setStorage, NearState.invalidateIterators, hk]
         exact congrFun hStRegStorage k⟩
    have hStReg_wasm : { stReg with host := (stReg.host.setStorage key val).invalidateIterators } =
        { store.wasm with host := (stReg.host.setStorage key val).invalidateIterators } := by
      simp only [checkedSetRegister?] at hCheckedProof
      split_ifs at hCheckedProof with hMax
      · simp at hCheckedProof; subst hCheckedProof; rfl
      · simp at hCheckedProof; subst hCheckedProof; rfl
    imodintro
    isplitl [HP' HcP]
    · isplitr [HcP]
      · iexists (stReg.host.setStorage key val).invalidateIterators
        isplitl_exact HP'
        · ipureexact hStorageFacts
      · iexact HcP
    · simp only [hStReg_wasm]
      iexact Hσ

end Wasm.SmallStep
