import CodeLib.SepLogic.SmallStepExactPages

/-!
# Upper page bounds from a terminating exact-page contract

Replay snapshots the physical page count at a reached prefix, then retains
that lower-bound snapshot through the same execution's terminal suffix.
Agreement with the returned exact page authority gives the upper bound.
This uses the program's checked resource evolution, not a separate claim
that arbitrary host functions or cross-instance transitions preserve pages.
-/

namespace Wasm.SmallStep

open Wasm.SepLogic Iris Iris.ProgramLogic Language.Notation Std

variable {α : Type} {Terminal : Type} [view : TerminalView α Terminal]

local instance (priority := high) growingPagesTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage

local instance (priority := high) growingPagesTerminalIrisGS
    [WasmSmallStepGS hlc α] :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      growingPagesTerminalLanguage (WasmHeapGF α) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

/-- Any execution from the same initial configuration has a suffix to a
known terminal endpoint. Determinism and terminality discharge the comparison
without a supplied trace-length bound. -/
theorem Steps.suffix_to_value
    {initial reached final : Config α} {trace fullTrace : List StepKind}
    (full : Steps initial fullTrace final)
    (first : Steps initial trace reached)
    (value : Terminal) (hvalue : Language.IntoVal final.expr value) :
    ∃ suffix : List StepKind, Steps reached suffix final := by
  rcases steps_comparable full first with ⟨suffix, remaining⟩ | remaining
  · cases remaining with
    | refl => exact ⟨[], .refl _⟩
    | cons head tail =>
        have hprim : (final.expr, final.store) -<([] : List StepKind)>->
            (_, _, ([] : List (Expr α))) := ⟨rfl, _, rfl, head⟩
        have impossible := Language.val_stuck hprim
        simp [← hvalue.into_val] at impossible
  · exact remaining

/-- A terminal execution and an exact-page total WP imply an upper bound at
every reached prefix. The initialized store, host environment, and physical
cap are unchanged. The terminal execution is an explicit premise; callers
must derive it from total adequacy rather than assume termination publicly. -/
theorem bounded_pages_at_every_prefix
    [InvGpreS (WasmHeapGF α)]
    (initial : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (capσ : WasmMemoryCapMap Nat)
    (frontier bound : Nat)
    (hagree : heapAgreesWithMem σ (storeResolve initial.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve initial.store))
    (hbelow : HeapBelow σ frontier)
    (hcaps : capHeapAgrees capσ initial.store.wasm.mem.pages initial.store.wasm.memoryCaps)
    (hglobals : globalHeapAgrees globalσ initial.store.wasm.globals)
    (hwf : initial.store.runtime.entry.id < initial.store.runtime.instances.size)
    (hwp : ∀ [gs : WasmSmallStepGS .hasLC α],
      gs.memoryPages.stateFrac = (1 : Qp).half →
      InitialMachineClientResources initial σ globalσ capσ frontier ∗
        memoryPagesHalf initial.store.wasm.mem.pages ⊢
        WP initial.expr @ Stuckness.NotStuck; ⊤
          [{ _value, iprop(∃ pages : Nat, ⌜pages ≤ bound⌝ ∗ memoryPagesHalf pages) }])
    {final reached : Config α} {fullTrace trace : List StepKind}
    (full : Steps initial fullTrace final)
    (value : Terminal) (hvalue : Language.IntoVal final.expr value)
    (execution : Steps initial trace reached) :
    reached.store.wasm.mem.pages ≤ bound := by
  obtain ⟨suffix, remaining⟩ := full.suffix_to_value execution value hvalue
  apply pure_soundness (PROP := IProp (WasmHeapGF α))
  apply fupd_soundness .hasLC 0 (E1 := ⊤) (E2 := ⊤)
  intro inv
  iintro _Hcredits
  imod smallStep_init_exact_at_caps initial σ globalσ capσ frontier
      hagree hinBounds hbelow hcaps hglobals hwf with
    ⟨%gs, %hmode, Hstate, Hclient, Hhalf⟩
  rcases hmode with ⟨rfl, hhalf⟩
  letI : WasmSmallStepGS .hasLC α := gs
  ihave Hwp := hwp hhalf $$ [Hclient Hhalf]
  · iframe Hclient Hhalf
  imod twp_replay_steps execution 0 [] 0 $$ [Hstate Hwp] with ⟨Hstate, Hwp⟩
  · iframe Hstate Hwp
  imod stateInterp_memoryPages_snapshot reached.store (0 + trace.length) [] 0
      $$ Hstate with ⟨Hstate, #Hsnapshot⟩
  imod twp_replay_value (post := fun _value : Terminal =>
      iprop(∃ pages : Nat, ⌜pages ≤ bound⌝ ∗ memoryPagesHalf pages))
      remaining value hvalue (0 + trace.length) [] 0
      $$ [Hstate Hwp] with ⟨_Hstate, %pages, %hbound, Hhalf⟩
  · iframe Hstate Hwp
  ihave %hle := pagesAuthorityFrac_lb_agree (1 : Qp).half pages
      reached.store.wasm.mem.pages $$ [Hhalf Hsnapshot]
  · iunfold memoryPagesHalf at Hhalf
    iframe Hhalf Hsnapshot
  imodintro
  ipureexact Nat.le_trans hle hbound

end Wasm.SmallStep
