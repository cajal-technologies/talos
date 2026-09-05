import CodeLib.Examples.Quicksort.Pure
import CodeLib.Examples.UInt32Array.Laws
import CodeLib.SepLogic.SmallStepTotalLoop
import CodeLib.UInt32

/-!
# Derived laws for the quicksort proof

Compact contextual WP rule for the swapAt instruction sequence.
-/

namespace Wasm.Examples.Quicksort

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep
open Wasm.Examples.UInt32Array


set_option maxHeartbeats 2000000 in
theorem twp_swapAt
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {baseIndex aIndex bIndex tmpIndex : Nat}
    {base : UInt32} {input : List UInt32} {a b : Nat}
    {updated : Locals}
    (ha : a < input.length) (hb : b < input.length)
    (hfit : base.toNat + 4 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (ha_local : (⟨params, localValues, stack⟩ : Locals).get aIndex =
      some (.i32 (UInt32.ofNat a)))
    (htmp_set : (⟨params, localValues, .i32 input[a] :: stack⟩ : Locals).set?
      tmpIndex (.i32 input[a]) = some updated)
    (hbase_after : updated.get baseIndex = some (.i32 base))
    (ha_after : updated.get aIndex = some (.i32 (UInt32.ofNat a)))
    (hb_after : updated.get bIndex = some (.i32 (UInt32.ofNat b)))
    (htmp_after : updated.get tmpIndex = some (.i32 input[a])) :
    arrayAt 0 base input ∗
      (arrayAt 0 base (swapElems input a b) -∗
        WP (.running
          ⟨{ updated with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        swapAt baseIndex aIndex bIndex tmpIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  let addr_a : UInt32 := 4 * UInt32.ofNat a + base
  have hslot_a : addr_a.toNat = base.toNat + 4 * a := by
    dsimp [addr_a]
    rw [UInt32.add_comm]
    exact Mem.words32_slotAddr_toNat base a (by
      simpa only [UInt32.size] using Nat.lt_of_lt_of_le (by omega) hfit)
  have hroom_a : addr_a.toNat + 4 ≤ UInt32.size := by rw [hslot_a]; omega
  obtain ⟨h1_a, h2_a, h3_a⟩ := UInt32.addSteps4 addr_a (by
    simpa only [UInt32.size] using hroom_a)
  let addr_b : UInt32 := 4 * UInt32.ofNat b + base
  have hslot_b : addr_b.toNat = base.toNat + 4 * b := by
    dsimp [addr_b]
    rw [UInt32.add_comm]
    exact Mem.words32_slotAddr_toNat base b (by
      simpa only [UInt32.size] using Nat.lt_of_lt_of_le (by omega) hfit)
  have hroom_b : addr_b.toNat + 4 ≤ UInt32.size := by rw [hslot_b]; omega
  obtain ⟨h1_b, h2_b, h3_b⟩ := UInt32.addSteps4 addr_b (by
    simpa only [UInt32.size] using hroom_b)
  have hswap : swapElems input a b = (input.set a input[b]).set b input[a] :=
    List.swapElems_eq_set input ha hb
  iintro ⟨Harray, Hcont⟩
  simp only [swapAt, storeAt, List.append_assoc,
    List.cons_append, List.nil_append]
  -- step 1: load arr[a] onto stack
  iapply_frame_intro twp_loadAt ha hfit hbase ha_local as Harray
  -- step 2: save arr[a] in tmp local
  iapply Wasm.SmallStep.twp_localSet htmp_set
  -- step 3: compute address of arr[a]
  iapply twp_address (by exact hbase_after) (by exact ha_after)
  -- step 4: load arr[b] onto stack
  iapply_frame_intro twp_loadAt hb hfit (by exact hbase_after) (by exact hb_after) as Harray
  -- focus on cell a for the first store
  ihave ⟨Hcell_a, Hclose_a⟩ := arrayAt_set 0 base input a input[b] ha $$ Harray
  ihave Hcell_a' : pointsTo_u32 0 addr_a input[a] $$ [Hcell_a]
  · dsimp [addr_a]
    irw_exact [UInt32.add_comm] with Hcell_a
  -- step 5: store arr[b] at arr[a]
  iapply_splitl_exact twp_store32_cell h1_a h2_a h3_a with Hcell_a'
  iintro Hcell_a
  -- rebuild intermediate array
  ihave Harray2 : arrayAt 0 base (input.set a input[b]) $$ [Hcell_a Hclose_a]
  · iapply Hclose_a
    irw_exact [UInt32.add_comm] with Hcell_a
  -- step 6: compute address of arr[b]
  iapply twp_address (by exact hbase_after) (by exact hb_after)
  -- step 7: push tmp (= original arr[a]) onto stack
  iapply Wasm.SmallStep.twp_localGet (by exact htmp_after)
  -- focus on cell b for the second store
  have hb' : b < (input.set a input[b]).length := by rw [List.length_set]; exact hb
  ihave ⟨Hcell_b, Hclose_b⟩ := arrayAt_set 0 base (input.set a input[b]) b input[a] hb' $$ Harray2
  ihave Hcell_b' : pointsTo_u32 0 addr_b (input.set a input[b])[b] $$ [Hcell_b]
  · dsimp [addr_b]
    irw_exact [UInt32.add_comm] with Hcell_b
  -- step 8: store original arr[a] at arr[b]
  iapply_splitl_exact twp_store32_cell h1_b h2_b h3_b with Hcell_b'
  iintro Hcell_b
  -- apply continuation with swapped array
  iapply Hcont
  rw [hswap]
  iapply Hclose_b
  irw_exact [UInt32.add_comm] with Hcell_b


theorem u32_ofNat_sub_eq {a b : Nat} (hle : b ≤ a) (ha : a < UInt32.size) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  have hb : b < UInt32.size := Nat.lt_of_le_of_lt hle ha
  have hab : a - b < UInt32.size := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  apply UInt32.toNat.inj
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' ha, UInt32.toNat_ofNat_of_lt' hb,
      UInt32.toNat_ofNat_of_lt' hab]
  have := (UInt32.ofNat a).toNat_lt
  rw [UInt32.toNat_ofNat_of_lt' ha] at this; omega

end Wasm.Examples.Quicksort
