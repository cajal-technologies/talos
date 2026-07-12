import CodeLib.SepLogic.ModuleLinking
import CodeLib.SepLogic.WasmHeap

namespace Wasm.SepLogic.LinkingExample

-- Shadow Wasm.FuncSpec (interpreter's 5-arg def from Interpreter.Wasm.Wp.Call)
-- that ancestor-namespace lookup would otherwise resolve bare `FuncSpec` to.
private abbrev FuncSpec := Wasm.SepLogic.ModuleLinking.FuncSpec
open Wasm.SepLogic.ModuleLinking (funcSatisfies frame_rule link_modules)

open Iris

variable [inst : WasmHeapGS]

-- Note on `∗`: in iris-lean `∗` is only available inside `iprop(...)` or `⊢`/`⊣⊢`
-- macros (see Iris.BI.BIBase). In term position, use `iprop% (A ∗ B)` instead.

/-- Increment specification: the function reads ptr (value `v`), writes `v+1`, returns.
    `pre` owns the memory cell; `post` owns it with the new value.
    No `frame` field — the caller's additional resources are preserved by ∗. -/
def incrementSpec (ptr : UInt32) (v : UInt64) : FuncSpec where
  pre  := fun _st      => pointsTo_u64 ptr v
  post := fun _st' _vs => pointsTo_u64 ptr (v + 1)

/-- Two sequential increment calls with an automatic iProp frame.

    ## Setup
    Initial heap: `pointsTo_u64 ptr v ∗ pointsTo_u64 ptr₂ u`
    The second cell `ptr₂` is the caller's frame — it must be untouched.

    ## Call 1  (frame R = pointsTo_u64 ptr₂ u)
    Apply `h_incr v` with R = pointsTo_u64 ptr₂ u; hpre already has the right form.
    TerminatesWith gives `∃ σ₁, genHeapInterp σ₁ ⊢ pointsTo_u64 ptr (v+1) ∗ pointsTo_u64 ptr₂ u`

    ## Call 2  (same frame R)
    Apply `h_incr (v+1)` at the new heap σ₁; same frame R.
    TerminatesWith gives `∃ σ₂, genHeapInterp σ₂ ⊢ pointsTo_u64 ptr (v+2) ∗ pointsTo_u64 ptr₂ u`

    The frame `pointsTo_u64 ptr₂ u` is preserved automatically by ∗;
    no explicit `S.frame` condition is needed. -/
theorem linked_two_calls
    (m : Wasm.Module) (ptr ptr₂ : UInt32) (v u : UInt64)
    (incr_idx : Nat)
    (h_incr : ∀ w, funcSatisfies m incr_idx (incrementSpec ptr w)) :
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
  intro env st σ hpre
  -- ── Call 1 ──────────────────────────────────────────────────────────────────
  -- h_incr v : funcSatisfies m incr_idx (incrementSpec ptr v)
  -- frame R = pointsTo_u64 ptr₂ u; hpre already witnesses pre ∗ R.
  obtain ⟨N₁, hN₁⟩ := h_incr v env st [] (pointsTo_u64 ptr₂ u) σ hpre
  refine ⟨N₁, fun fuel₁ hle₁ => ?_⟩
  obtain ⟨vs₁, st₁, hrun₁, σ₁, hpost₁⟩ := hN₁ fuel₁ hle₁
  -- hpost₁ : genHeapInterp σ₁ ⊢ pointsTo_u64 ptr (v+1) ∗ pointsTo_u64 ptr₂ u
  refine ⟨vs₁, st₁, hrun₁, σ₁, hpost₁, ?_⟩
  -- ── Call 2 ──────────────────────────────────────────────────────────────────
  -- h_incr (v+1) at heap σ₁; same frame R = pointsTo_u64 ptr₂ u.
  obtain ⟨N₂, hN₂⟩ := h_incr (v + 1) env st₁ [] (pointsTo_u64 ptr₂ u) σ₁ hpost₁
  refine ⟨N₂, fun fuel₂ hle₂ => ?_⟩
  obtain ⟨vs₂, st₂, hrun₂, σ₂, hpost₂⟩ := hN₂ fuel₂ hle₂
  -- hpost₂ type: genHeapInterp σ₂ ⊢ (incrementSpec ptr (v+1)).post st₂ vs₂ ∗ ...
  -- Unfold incrementSpec to expose `(v+1)+1`, then rewrite to `v+2`.
  simp only [incrementSpec] at hpost₂
  -- Now: hpost₂ : genHeapInterp σ₂ ⊢ pointsTo_u64 ptr ((v+1)+1) ∗ pointsTo_u64 ptr₂ u
  rw [show (v + 1 : UInt64) + 1 = v + 2 from by rw [UInt64.add_assoc]; congr 1] at hpost₂
  exact ⟨vs₂, st₂, hrun₂, σ₂, hpost₂⟩

end Wasm.SepLogic.LinkingExample
