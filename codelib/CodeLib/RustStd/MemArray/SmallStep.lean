import CodeLib.RustStd.MemArray
import CodeLib.SepLogic.SmallStepAdequacy

/-! Small-step ownership facts for consecutive memory arrays. -/

namespace Wasm.SepLogic

open Iris Std
open Wasm.SmallStep

/-- Walking `arrayAt` ownership reads back exactly its sequence of `u32` words. -/
theorem arrayAt_readWords32 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat) (obs : List StepKind) (threads : Nat)
    (base : UInt32) (output : List UInt32)
    (hfit : base.toNat + 4 * output.length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps obs threads ∗ arrayAt 0 base output ==∗
      stateInterp (GF := WasmHeapGF α) store steps obs threads ∗ arrayAt 0 base output ∗
      ⌜store.wasm.mem.readWords32 base output.length = output⌝ := by
  induction output generalizing base with
  | nil =>
    simp only [arrayAt, List.length_nil, Mem.readWords32]
    iintro ⟨Hstate, Hemp⟩
    imodintro
    isplitl_exacts [Hstate Hemp]
    ipureintro; trivial
  | cons x xs ih =>
    simp only [arrayAt, List.length_cons]
    simp only [List.length_cons, UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    have hfit' : (base + 4).toNat + 4 * xs.length ≤ UInt32.size := by
      simp only [UInt32.size]; omega
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    iintro ⟨Hstate, Hword, Hxs⟩
    imod stateInterp_pointsTo_u32_facts_frame store steps obs threads base x
      h1 h2 h3 $$ [$Hstate $Hword] with ⟨Hstate, Hword, %hfacts⟩
    imod ih (base + 4) hfit' $$ [$Hstate $Hxs] with ⟨Hstate, Hxs, %hread⟩
    imodintro
    isplitl_exact Hstate
    isplitl [Hword Hxs]
    · isplitl_exact Hword; iexact Hxs
    ipureintro
    simp only [Mem.readWords32, hfacts.1, hread]

end Wasm.SepLogic
