import CodeLib.SepLogic.Adequacy

namespace Wasm.SepLogic.Test

open Iris Wasm Std

-- THE MISSING PIECE: wasm_adequacy takes ⊢ wp_wasm (which needs WasmHeapGS)
-- and produces wp_wasm_prop (which doesn't). Need a wrapper that:
-- 1. Allocates ghost state via genHeap_init_names
-- 2. Gets genHeapInterp σ + WasmHeapGS instance
-- 3. Uses the iProp proof to get ⊢ genHeapInterp σ ∗ wp_wasm
-- 4. Applies wasm_adequacy to get |==> ⌜wp_wasm_prop⌝
-- 5. Applies pure_soundness to extract wp_wasm_prop

-- This is HeapLang's heap_adequacy pattern.
-- Check: does genHeap_init_names give us the WasmHeapGS instance?
-- Yes: it produces ∃ γh γm, ... where G := ⟨γh, γm⟩ : genHeapGS
-- So the wrapper universally quantifies over the instance.

-- Proposed signature:
-- theorem wasm_heap_adequacy
--     (m : Module) (st : Store Unit) (locals : Locals)
--     (prog : Program) (env : HostEnv Unit)
--     (Q : Store Unit → List Value → Prop)
--     (hwp : ∀ [inst : WasmHeapGS], ⊢ wp_wasm m st locals prog env Q) :
--     wp_wasm_prop m st locals prog env Q

-- For now, test that the iProp proof works with explicit instance:
theorem test_with_explicit_inst
    [inst : WasmHeapGS]
    (m : Module) (st : Store Unit) (env : HostEnv Unit)
    (locals : Locals) (v : UInt32)
    (Q : Store Unit → List Value → Prop)
    (hQ : Q st (.i32 v :: locals.values)) :
    ⊢ wp_wasm m st locals [.const v, .ret] env Q := by
  apply wp_wasm_const v
  intro σ'
  iintro Hσ'
  imodintro
  iexists σ'
  isplitl [Hσ']
  · iexact Hσ'
  · unfold wp_wasm
    iapply least_fixpoint_unfold_mpr
    unfold wp_wasm_F
    simp only [LeibnizO.car]
    exact BI.pure_intro hQ

end Wasm.SepLogic.Test
