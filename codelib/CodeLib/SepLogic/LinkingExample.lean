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

/-- iProp → Prop bridge: the increment function terminates from a valid initial
    combined assertion `⊢ genHeapInterp σ ∗ (ptr ↦ v ∗ ptr₂ ↦ u)`.

    Uses `wp_wasm_iProp_call` to chain:
      funcSatisfies (via frame_rule) + h_init
        → ⊢ genHeapInterp σ ∗ wp_wasm_iProp ... (pointsTo ptr (v+1) ∗ pointsTo ptr₂ u)
        → ⊢ genHeapInterp σ ∗ wp_wasm ... True            (trivialize postcondition)
        → wp_wasm_prop ... True                             (wasm_adequacy + pure_soundness)
        → TerminatesWith {} m incr_idx st [] (fun _ _ => True)  (conversion)

    ## Why `fun _ _ => True` and not `fun st' _ => st'.mem.read64 ptr = v + 2`

    The `v + 2` conclusion would require:
    1. Sequential composition: a second `TerminatesWith` for the post-state `st₁`
       from the first call.  But after extracting `True` from the first call we
       lose track of `st₁` and cannot build `⊢ genHeapInterp σ₁ ∗ pointsTo ptr (v+1)`
       needed to run `wp_wasm_iProp_call` again.
    2. Ghost-to-physical link: `genHeap_valid` gives `get? σ addr = some (some byte)`
       (ghost map content), not `st'.mem.bytes addr.toNat = byte` (physical memory).
       The connection requires `heapAgreesWithMem σ mem` as a maintained invariant,
       which is not currently set up as an iProp invariant.

    Both missing pieces belong to a heap-with-invariant setup (e.g. Iris invariants
    for `heapAgreesWithMem`).  This theorem shows the iProp→Prop adequacy path
    is already in place; only the sequential ghost-state tracking is missing.

    ## Hypothesis note
    `⊢ genHeapInterp σ ∗ (...)` is the CORRECT combined form (AUTH ∗ FRAG).
    The form `genHeapInterp σ ⊢ ...` (AUTH ⊢ FRAG alone) is false in the genHeap
    RA model and cannot be used here. -/
theorem linked_terminates
    (m : Wasm.Module) (ptr ptr₂ : UInt32) (v u : UInt64)
    (incr_idx : Nat)
    (h_incr : ∀ w, incrementSpec m incr_idx ptr w)
    (st : Store Unit) (σ : WasmHeapMap (Option UInt8))
    (h_init : ⊢ genHeapInterp σ ∗ (pointsTo_u64 ptr v ∗ pointsTo_u64 ptr₂ u))
    (himp : m.imports[incr_idx]? = none)
    (h_noimports : m.imports.length = 0)
    (hresults : ∀ f, m.funcs[incr_idx]? = some f → f.results.length = 0) :
    TerminatesWith {} m incr_idx st [] (fun _ _ => True) := by
  obtain ⟨f, hf, hspec⟩ := frame_rule (pointsTo_u64 ptr₂ u) (h_incr v)
  -- Coerce hspec {} st [] to explicit iProp types to avoid HOU when chaining below:
  -- the framed pre beta-reduces to (pointsTo_u64 ptr v ∗ pointsTo_u64 ptr₂ u) by
  -- (fun _ => pointsTo_u64 ptr v) st = pointsTo_u64 ptr v, handled by isDefEq.
  have hspec_inst : ⊢ (iprop% pointsTo_u64 ptr v ∗ pointsTo_u64 ptr₂ u) -∗
      wp_wasm_iProp m st (f.toLocals []) f.body {}
        (fun st' vs => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u) :=
    hspec {} st []
  -- Chain h_init through hspec_inst: ⊢ genHeapInterp σ ∗ wp_wasm_iProp ...
  have hwp_init : ⊢ genHeapInterp σ ∗
      wp_wasm_iProp m st (f.toLocals []) f.body {}
        (fun st' vs => iprop% pointsTo_u64 ptr (v + 1) ∗ pointsTo_u64 ptr₂ u) :=
    h_init.trans (BI.sep_mono_right (BI.wand_entails hspec_inst))
  -- Trivialize iProp postcondition → Prop WP with True
  have hwp_true : ⊢ genHeapInterp σ ∗ wp_wasm m st (f.toLocals []) f.body {} (fun _ _ => True) :=
    hwp_init.trans (BI.sep_mono_right wp_wasm_iProp_trivialize)
  -- Adequacy: extract Prop-level wp_wasm_prop
  have hwp_prop : wp_wasm_prop m st (f.toLocals []) f.body {} (fun _ _ => True) :=
    pure_soundness (hwp_true.trans
      (wasm_adequacy m st (f.toLocals []) f.body {} (fun _ _ => True) σ))
  -- Normalize args form for TerminatesWith ([] take/reverse = [])
  have hwp_prop' :
      wp_wasm_prop m st
        (f.toLocals (([] : List Value).take f.numParams).reverse)
        f.body {} (fun _ _ => True) := by
    simp only [List.take_nil, List.reverse_nil]; exact hwp_prop
  exact wp_wasm_prop_to_TerminatesWith
    (by rw [h_noimports, Nat.sub_zero]; exact hf)
    himp (hresults f hf) (Nat.zero_le _) (fun _ _ h => h) hwp_prop'

end Wasm.SepLogic.LinkingExample
