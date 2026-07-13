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

/-- Two sequential increment calls: `frame_rule` threads ownership through both.

    Proves the iProp-level composition: for any frame resource `pointsTo_u64 ptr₂ u`,
    both the first call `(ptr: v → v+1)` and the second `(ptr: v+1 → v+2)` have
    framed specs that preserve `pointsTo_u64 ptr₂ u`.

    ## Architecture
    1. `frame_rule R (h_incr v)` lifts the bare spec to `{pre ∗ R} / {post ∗ R}`.
    2. `frame_rule R (h_incr (v+1))` does the same for the continuation spec.
    3. UInt64 arithmetic: `(v+1)+1 = v+2` by `UInt64.add_assoc + native_decide`.

    ## Extracting TerminatesWith (not done here)
    To extract `TerminatesWith`, the caller needs:
    - `h_init : ⊢ genHeapInterp σ ∗ pre st` (valid combined auth+frag assertion)
    - A monotonicity lemma `wp_wasm_iProp ... post ⊢ wp_wasm ... True`
    - Then: `wasm_adequacy` → `pure_soundness` → `wp_wasm_prop_to_TerminatesWith`
    The key constraint: `h_init` requires BOTH `genHeapInterp` (AUTH) and ownership
    frags together — obtainable via `genHeap_init` at allocation time. -/
theorem linked_two_calls
    (m : Wasm.Module) (ptr ptr₂ : UInt32) (v u : UInt64)
    (incr_idx : Nat)
    (h_incr : ∀ w, incrementSpec m incr_idx ptr w) :
    funcSatisfies m incr_idx
      (fun _ => iprop% pointsTo_u64 ptr v ∗ pointsTo_u64 ptr₂ u)
      (fun _ _ => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u) ∧
    funcSatisfies m incr_idx
      (fun _ => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u)
      (fun _ _ => iprop% pointsTo_u64 ptr (v + 2) ∗ pointsTo_u64 ptr₂ u) := by
  -- Call 1: frame ptr₂ through incr(v)
  have h1 := frame_rule (pointsTo_u64 ptr₂ u) (h_incr v)
  -- Call 2: frame ptr₂ through incr(v+1), normalizing (v+1)+1 → v+2
  have h2v : funcSatisfies m incr_idx
      (fun _ => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u)
      (fun _ _ => iprop% pointsTo_u64 ptr (v + 2) ∗ pointsTo_u64 ptr₂ u) := by
    have h := frame_rule (pointsTo_u64 ptr₂ u) (h_incr (v + 1))
    have heq : (v + 1 + 1 : UInt64) = v + 2 := by
      have h1 : (1 : UInt64) + 1 = 2 := by native_decide
      rw [UInt64.add_assoc, h1]
    simp only [heq] at h
    exact h
  exact ⟨h1, h2v⟩

end Wasm.SepLogic.LinkingExample
