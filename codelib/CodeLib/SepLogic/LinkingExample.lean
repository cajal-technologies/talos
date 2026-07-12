import CodeLib.SepLogic.ModuleLinking
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap

/-! # Module Linking Example: two sequential increment calls

Module A exports `increment(ptr)`:
  pre  : `st.mem.read64 ptr = v`  for some `v`
  post : `st'.mem.read64 ptr = v + 1`
  frame: every 8-byte cell whose range doesn't overlap `[ptr, ptr+8)` is
         unchanged — this is the ownership guarantee.

Module B imports `increment`, calls it TWICE on the same `ptr`.
B's proof NEVER mentions A's implementation; it only uses the spec.
The frame property is used to show that an unrelated cell `ptr₂` is
preserved across both calls. -/

namespace Wasm.SepLogic.LinkingExample

-- Shadow the ancestor Wasm.FuncSpec (an interpreter def with 5 args from
-- Wasm.Wp.Call) so that bare `FuncSpec` refers to our structure.
private abbrev FuncSpec := Wasm.SepLogic.ModuleLinking.FuncSpec

open Wasm.SepLogic.ModuleLinking (funcSatisfies link_modules compose_with_import)

/-- Specification for `increment ptr v`:
    the function reads `v` from `ptr`, writes `v + 1` back, and guarantees
    that every non-overlapping 8-byte cell is unchanged (frame rule). -/
def incrementSpec (ptr : UInt32) (v : UInt64) : FuncSpec where
  pre   := fun st  => st.mem.read64 ptr = v
  post  := fun st' rs => st'.mem.read64 ptr = v + 1 ∧ rs = []
  -- frame: every u64 cell whose byte range [addr, addr+8) does not
  -- overlap [ptr, ptr+8) is preserved.
  frame := fun st st' =>
    ∀ (addr : UInt32),
      (addr.toNat + 8 ≤ ptr.toNat ∨ ptr.toNat + 8 ≤ addr.toNat) →
      st'.mem.read64 addr = st.mem.read64 addr

/-- **Two-call increment theorem**.

    Given any module satisfying `incrementSpec ptr w` for every starting
    value `w`, calling increment TWICE at `ptr` gives `v + 2`, and an
    unrelated cell `ptr₂` (non-overlapping with `ptr`) is preserved across
    both calls.

    ## How the frame is used

    After call 1 (initial store `st`, result `st₁`):
    - postcondition: `st₁.read64 ptr = v + 1`
    - **frame**: `st₁.read64 ptr₂ = st.read64 ptr₂ = u`   ← uses frame

    After call 2 (initial store `st₁`, result `st₂`):
    - postcondition: `st₂.read64 ptr = (v+1)+1 = v+2`
    - **frame**: `st₂.read64 ptr₂ = st₁.read64 ptr₂ = u`  ← uses frame

    B's proof is parametric over `m` and never inspects its code. -/
theorem linked_two_calls
    (m : Wasm.Module) (ptr ptr₂ : UInt32) (v u : UInt64)
    (incr_idx : Nat)
    (h_nonoverlap : ptr₂.toNat + 8 ≤ ptr.toNat ∨ ptr.toNat + 8 ≤ ptr₂.toNat)
    (h_incr : ∀ w, funcSatisfies m incr_idx (incrementSpec ptr w)) :
    ∀ (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit),
      st.mem.read64 ptr  = v →
      st.mem.read64 ptr₂ = u →
      Wasm.TerminatesWith env m incr_idx st []
        (fun st₁ _ =>
          st₁.mem.read64 ptr  = v + 1 ∧
          st₁.mem.read64 ptr₂ = u     ∧
          Wasm.TerminatesWith env m incr_idx st₁ []
            (fun st₂ _ =>
              st₂.mem.read64 ptr  = v + 2 ∧
              st₂.mem.read64 ptr₂ = u)) := by
  intro env st hpre₁ hpre₂
  -- ── First call ──────────────────────────────────────────────────────────
  obtain ⟨N₁, hN₁⟩ := h_incr v env st [] hpre₁
  refine ⟨N₁, fun fuel₁ hle₁ => ?_⟩
  obtain ⟨vs₁, st₁, hrun₁, hpostframe₁⟩ := hN₁ fuel₁ hle₁
  obtain ⟨hpost₁, hfr₁⟩ := hpostframe₁
  -- Unfold incrementSpec so hpost₁ and hfr₁ have explicit function types
  simp only [incrementSpec] at hpost₁ hfr₁
  obtain ⟨hv₁, _⟩ := hpost₁
  -- Frame from call 1: ptr₂ is outside the footprint → unchanged
  have hu₁ : st₁.mem.read64 ptr₂ = u :=
    (hfr₁ ptr₂ h_nonoverlap).trans hpre₂
  refine ⟨vs₁, st₁, hrun₁, hv₁, hu₁, ?_⟩
  -- ── Second call ─────────────────────────────────────────────────────────
  -- At st₁ with st₁.read64 ptr = v+1; apply spec at starting value (v+1)
  obtain ⟨N₂, hN₂⟩ := h_incr (v + 1) env st₁ [] hv₁
  refine ⟨N₂, fun fuel₂ hle₂ => ?_⟩
  obtain ⟨vs₂, st₂, hrun₂, hpostframe₂⟩ := hN₂ fuel₂ hle₂
  obtain ⟨hpost₂, hfr₂⟩ := hpostframe₂
  simp only [incrementSpec] at hpost₂ hfr₂
  obtain ⟨hv₂, _⟩ := hpost₂
  -- Frame from call 2: ptr₂ still unchanged
  have hu₂ : st₂.mem.read64 ptr₂ = u :=
    (hfr₂ ptr₂ h_nonoverlap).trans hu₁
  -- (v+1)+1 = v+2 for UInt64
  refine ⟨vs₂, st₂, hrun₂, ?_, hu₂⟩
  rw [hv₂, UInt64.add_assoc]; congr 1

end Wasm.SepLogic.LinkingExample
