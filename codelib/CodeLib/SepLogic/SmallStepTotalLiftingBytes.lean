import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Byte-granular and supplementary total-WP instruction rules

Total weakest-precondition lifting rules on top of `SmallStepTotalLifting`,
factored out of the `hex_stdio` worked examples for reuse:

* byte-granular memory access — `twp_load8U`, `twp_load8U_addr`, `twp_store8`,
  `twp_store8_addr`, `twp_store32_addr`, `twp_store64_addr`;
* the signed comparison `twp_ltS` and `twp_drop`; and
* `twp_memorySize_framed` / `twp_memoryGrow_framed`, `memory.size` / `memory.grow`
  rules that thread an arbitrary owned resource through the instruction (a
  lighter-weight alternative to the memory-page-tracking variants).

Each is program-agnostic and has a use site in the hex encode/decode proofs.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
local instance instSubmissionWasmTotalIrisGS :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) :=
  instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}


/-- Total primitive rule for `i32.load8_u`. -/
theorem twp_load8U
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hpt Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts : ⌜store.wasm.mem.read8 (address + offset) = byte ∧
      (address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_facts store ns obs nt
      (address + offset) byte $$ [$Hσ $Hpt] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, by simpa [Hread] using Step.load8U hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load8U offset))
      ⟨.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using (Step.load8U (α := α) hbound)
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hpt

/-- Offset-zero form of `twp_load8U`. -/
theorem twp_load8U_addr
    {params localValues values : List Value}
    {address : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
      WP (.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues, .i32 address :: values⟩,
      .load8U 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_load8U (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (params := params)
      (localValues := localValues) (values := values) (code := code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) byte (by simp))

/-- Total primitive rule for `i32.store8`. -/
theorem twp_store8
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store8 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some oldByte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some value.toUInt8) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hpt Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %HinBounds :
      ⌜(address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hσ Hpt]
  · imod stateInterp_pointsTo_inBounds store ns obs nt
      (address + offset) oldByte $$ [$Hσ $Hpt] with %HinBounds
    ipureintro
    exact HinBounds
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write8 (address + offset) value.toUInt8 } },
      [], ⟨rfl, _, rfl, Step.store8 hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store8 offset))
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write8
                (address + offset) value.toUInt8 } }⟩ :=
    Step.store8 hbound
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_store8 store ns obs nt
      (address + offset) oldByte value.toUInt8
      (by simpa [hnowrap] using HinBounds) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hpt

/-- Offset-zero form of `twp_store8`, avoiding an `addr + 0` unification
artifact in generated code. -/
theorem twp_store8_addr
    {params localValues values : List Value}
    {address value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some oldByte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value.toUInt8) -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store8 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_store8 (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (value := value)
      (params := params) (localValues := localValues) (values := values)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) oldByte (by simp))

theorem twp_store32_addr
    {params localValues values : List Value}
    {address value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    pointsTo_u32 0 address oldWord -∗
    (pointsTo_u32 0 address value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store32 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_store32 (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (value := value)
      (params := params) (localValues := localValues) (values := values)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) oldWord (by simp)
      (by simpa using h1) (by simpa using h2) (by simpa using h3))


theorem twp_ltS
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs.toInt32 < rhs.toInt32 then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ltS :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ltS hresult)

theorem twp_drop
    {params localValues values : List Value}
    {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, localValues, value :: values⟩,
        .drop :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.drop)


/-- Total rule for `memory.size`. -/
theorem twp_memorySize_framed
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (R : IProp (WasmHeapGF α))
    (Htwp : ∀ pages : Nat,
        runtimeModuleOwn instanceId runtimeModule ∗ R -∗
        WP (.running ⟨⟨params, localValues,
            sizeValue runtimeModule.memIs64 pages :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule ∗ R -∗
    WP (.running ⟨⟨params, localValues, values⟩,
        .memorySize :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro ⟨Hruntime, HR⟩
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.currentModule = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      instanceId runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running ⟨⟨params, localValues,
        sizeValue store.runtime.currentModule.memIs64 store.wasm.mem.pages :: values⟩,
      code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction .memorySize, rfl, Step.memorySize⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.memorySize wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · simp only [Hmodule]
    iapply Htwp
    iframe

/-- Total rule for `memory.grow`, exposing both the successful old-page
count and the `0xffffffff` failure result to the continuation. -/
theorem twp_memoryGrow_framed
    {params localValues values : List Value}
    {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (R : IProp (WasmHeapGF α))
    (Htwp : ∀ result : UInt32,
        runtimeModuleOwn instanceId runtimeModule ∗ R -∗
        WP (.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule ∗ R -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro ⟨Hruntime, HR⟩
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 (0xFFFFFFFF : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩,
        store, [], ⟨rfl, .instruction .memoryGrow, rfl,
          Step.memoryGrowFailure hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    obtain ⟨rfl, hconfig⟩ :=
      step_deterministic (Step.memoryGrowFailure hg) wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod Hclose
    imodintro
    isplit
    · ipureintro
      rfl
    isplit
    · ipureintro
      rfl
    isplitl [Hσ]
    · iexact Hσ
    · iapply Htwp
      iframe
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem := memory } }, [],
        ⟨rfl, .instruction .memoryGrow, rfl, by
          simpa only [Wasm.SmallStep.setMemory_eq] using
            Step.memoryGrowSuccess hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    have expectedStep : Step
        ⟨.running ⟨⟨params, localValues, .i32 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
            .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ := by
      simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg
    obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod stateInterp_memoryGrow store ns obs nt delta
      (store.wasm.memoryCap store.runtime.currentModule 0)
      memory previousPages hg $$ Hσ with Hσ
    imod Hclose
    imodintro
    isplit
    · ipureintro
      rfl
    isplit
    · ipureintro
      rfl
    isplitl [Hσ]
    · iexact Hσ
    · iapply Htwp
      iframe


/-- Offset-zero form of `twp_store64`. -/
theorem twp_store64_addr
    {params localValues values : List Value}
    {address : UInt32} {value : UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    pointsTo_u64 0 address oldWord -∗
    (pointsTo_u64 0 address value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
        .store64 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro Hword Hcont
  ihave Hword' : pointsTo_u64 0 (address + 0) oldWord $$ [Hword]
  · rw [UInt32.add_zero]
    iexact Hword
  iapply twp_store64 (α := α) (address := address) (offset := 0)
      (value := value) oldWord (by simp)
      (by simpa using h1) (by simpa using h2) (by simpa using h3)
      (by simpa using h4) (by simpa using h5) (by simpa using h6)
      (by simpa using h7) $$ Hword'
  iintro Hword
  iapply Hcont
  rw [UInt32.add_zero]
  iexact Hword


end Wasm.SmallStep
