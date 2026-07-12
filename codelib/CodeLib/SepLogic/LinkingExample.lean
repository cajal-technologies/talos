import CodeLib.SepLogic.ModuleLinking
import CodeLib.SepLogic.WasmHeap

namespace Wasm.SepLogic.LinkingExample

open Wasm.SepLogic.ModuleLinking (funcSatisfies frame_rule)
open Iris

variable [inst : WasmHeapGS]

-- Note on `∗`/`-∗`: only available inside `⊢`/`⊣⊢` macros or `iprop%(...)`.

/-- Increment specification: function owns `ptr ↦ v`, writes `v+1`, returns.
    No frame baked in — use `frame_rule` to thread caller resources through. -/
def incrementSpec
    (m : Module) (incr_idx : Nat)
    (ptr : UInt32) (v : UInt64) : Prop :=
  funcSatisfies m incr_idx
    (fun _st      => pointsTo_u64 ptr v)
    (fun _st' _vs => pointsTo_u64 ptr (v + 1))

/-- Two sequential increment calls using `frame_rule` to thread the frame
    `pointsTo_u64 ptr₂ u` through both calls.

    ## Strategy
    1. Apply `frame_rule R (h_incr v)` — get a framed spec for call 1.
    2. Apply `frame_rule R (h_incr (v+1))` — get a framed spec for call 2.
    3. iProp WP reasoning threads ownership through both calls.
    4. Adequacy extracts the final `TerminatesWith` conclusion.
    Full proof deferred: requires `frame_rule` proof and iProp WP adequacy. -/
theorem linked_two_calls
    (m : Wasm.Module) (ptr ptr₂ : UInt32) (v u : UInt64)
    (incr_idx : Nat)
    (h_incr : ∀ w, incrementSpec m incr_idx ptr w) :
    ∀ (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
      (σ : WasmHeapMap (Option UInt8)),
      (genHeapInterp σ ⊢ pointsTo_u64 ptr v ∗ pointsTo_u64 ptr₂ u) →
      Wasm.TerminatesWith env m incr_idx st []
        (fun st₁ _ =>
          ∃ σ₁ : WasmHeapMap (Option UInt8),
          (genHeapInterp σ₁ ⊢ pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u) ∧
          Wasm.TerminatesWith env m incr_idx st₁ []
            (fun _ _ =>
              ∃ σ₂ : WasmHeapMap (Option UInt8),
              genHeapInterp σ₂ ⊢ pointsTo_u64 ptr (v + 2) ∗ pointsTo_u64 ptr₂ u)) := by
  -- Call 1: frame ptr₂ through incr(v)
  have h1 := frame_rule (pointsTo_u64 ptr₂ u) (h_incr v)
  -- Call 2: frame ptr₂ through incr(v+1), normalizing (v+1)+1 → v+2
  have h2v : funcSatisfies m incr_idx
      (fun _st => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u)
      (fun _st' _vs => iprop% pointsTo_u64 ptr (v + 2) ∗ pointsTo_u64 ptr₂ u) := by
    have h := frame_rule (pointsTo_u64 ptr₂ u) (h_incr (v + 1))
    simp only [show (v : UInt64) + 1 + 1 = v + 2 from by omega] at h
    exact h
  obtain ⟨f₁, hf₁, hspec₁⟩ := h1
  obtain ⟨f₂, hf₂, hspec₂⟩ := h2v
  intro env st σ h_heap
  -- Apply adequacy for the first call
  have hterm1 := wasm_iProp_TerminatesWith m incr_idx env st
    (fun _st => iprop% pointsTo_u64 ptr v ∗ pointsTo_u64 ptr₂ u)
    (fun _st' _vs => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u)
    σ ⟨f₁, hf₁, hspec₁⟩ h_heap
  -- For every fuel witnessing the first call, build the nested conclusion
  obtain ⟨N₁, hN₁⟩ := hterm1
  exact ⟨N₁, fun fuel hfuel => by
    obtain ⟨vs₁, st₁, hrun₁, σ₁, hσ₁⟩ := hN₁ fuel hfuel
    -- Apply adequacy for the second call, using the post-state ghost heap
    have hterm2 :=
      wasm_iProp_TerminatesWith m incr_idx env st₁
        (fun _st => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u)
        (fun _st' _vs => iprop% pointsTo_u64 ptr (v + 2) ∗ pointsTo_u64 ptr₂ u)
        σ₁ ⟨f₂, hf₂, hspec₂⟩ hσ₁
    exact ⟨vs₁, st₁, hrun₁, ⟨σ₁, hσ₁, hterm2⟩⟩⟩

end Wasm.SepLogic.LinkingExample
