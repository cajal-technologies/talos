import CodeLib.Examples.MergeSort.Pure
import CodeLib.Examples.UInt32Array.Laws

/-!
# Derived laws for the merge-sort proof

Address arithmetic and compact contextual WP rules for the instruction
sequences used by the handwritten implementation.
-/

namespace Wasm.Examples.MergeSort

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep
open Wasm.Examples.UInt32Array

theorem ValidLayout.source_fits
    {source temporary : UInt32} {length : Nat}
    (h : ValidLayout source temporary length) :
    source.toNat + 4 * length ≤ UInt32.size := h.1

theorem ValidLayout.temporary_fits
    {source temporary : UInt32} {length : Nat}
    (h : ValidLayout source temporary length) :
    temporary.toNat + 4 * length ≤ UInt32.size := h.2.1

theorem ValidLayout.length_lt
    {source temporary : UInt32} {length : Nat}
    (h : ValidLayout source temporary length) :
    length < UInt32.size := by
  have hfit := h.source_fits
  have hsize : UInt32.size = 4294967296 := rfl
  rw [hsize] at hfit ⊢; omega
set_option maxHeartbeats 2000000 in
theorem twp_copyAt
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues stack : List Value}
    {sourceIndex sourceElement temporaryIndex temporaryElement : Nat}
    {source temporary : UInt32}
    {input scratch : List UInt32} {i k : Nat}
    (hi : i < input.length) (hk : k < scratch.length)
    (hsourceFit : source.toNat + 4 * input.length ≤ UInt32.size)
    (htemporaryFit :
      temporary.toNat + 4 * scratch.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hsource :
      (⟨params, localValues, stack⟩ : Locals).get sourceIndex =
        some (.i32 source))
    (hsourceElement :
      (⟨params, localValues, stack⟩ : Locals).get sourceElement =
        some (.i32 (UInt32.ofNat i)))
    (htemporary :
      (⟨params, localValues, stack⟩ : Locals).get temporaryIndex =
        some (.i32 temporary))
    (htemporaryElement :
      (⟨params, localValues, stack⟩ : Locals).get temporaryElement =
        some (.i32 (UInt32.ofNat k))) :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (arrayAt 0 source input ∗
        arrayAt 0 temporary (scratch.set k input[i]) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        storeAt temporaryIndex temporaryElement
          (loadAt sourceIndex sourceElement) ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let destination := 4 * UInt32.ofNat k + temporary
  have hslot :
      destination.toNat = temporary.toNat + 4 * k := by
    dsimp [destination]
    rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using
      arrayAddress_toNat temporary htemporaryFit hk
  have hroom : destination.toNat + 4 ≤ UInt32.size := by omega
  obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 destination (by
    simpa only [UInt32.size] using hroom)
  iintro ⟨Hsource, Htemporary, Hcont⟩
  simp only [storeAt, List.append_assoc]
  iapply twp_address htemporary htemporaryElement
  iapply twp_loadAt hi hsourceFit
    (by simpa using hsource)
    (by simpa using hsourceElement)
  iframe; iintro Hsource
  ihave ⟨Hcell, Hclose⟩ := arrayAt_set 0 temporary scratch k input[i] hk $$ Htemporary
  simp only [List.cons_append, List.nil_append]
  ihave Hcell' : pointsTo_u32 0 destination scratch[k] $$ [Hcell]
  · dsimp [destination]
    irw_exact [UInt32.add_comm] with Hcell
  iapply_splitl_exact twp_store32_cell h1 h2 h3 with Hcell'
  iintro Hcell
  iapply_splitl_exact Hcont with Hsource
  iapply Hclose
  ihave Hcell' :
      pointsTo_u32 0
        (temporary + 4 * UInt32.ofNat k) input[i] $$ [Hcell]
  · dsimp [destination]
    irw_exact [UInt32.add_comm] with Hcell
  iexact Hcell'


end Wasm.Examples.MergeSort
