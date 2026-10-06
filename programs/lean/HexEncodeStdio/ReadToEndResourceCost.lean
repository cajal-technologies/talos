import HexEncodeStdio.ReadToEndTransition
import HexEncodeStdio.AllocatorResourceCost

/-! # Resource potentials for the actual adaptive hex input loop

These arithmetic invariant transitions account for the growth attempt before
final EOF. The operational composition below uses the same generated module. -/

namespace Project.HexEncodeStdio.ReadToEndResourceCost

open Wasm Wasm.SmallStep

/-- Covers the first allocation and the speculative growth before final EOF. -/
def capacityBound (inputBytes : Nat) : Nat := 2 * inputBytes + 32

def inputFrontierBound (inputBytes : Nat) : Nat := 1054000 + 2 * capacityBound inputBytes

/-- Includes the output reserve's actual minimum capacity of eight bytes. -/
def completeFrontierBound (inputBytes : Nat) : Nat := inputFrontierBound inputBytes + max 8 (2 * inputBytes)

def InputFits (inputBytes : Nat) : Prop := completeFrontierBound inputBytes < 2 ^ 31

/-- Adds upper potentials to the already-proved concrete semantic invariant. -/
structure BoundedReadInv (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State) (capacity data length bump : UInt32) : Prop
    extends ReadToEndInv input consumed remaining store capacity data length bump where
  capacity_upper : capacity.toNat ≤ capacityBound input.length
  bump_upper : bump.toNat ≤ 1054000 + 2 * capacity.toNat

/-- The generated growth branch is entered with a full Vec, including when
there is no unread input left. That exact guard bounds its requested capacity. -/
theorem selected_capacity_bound {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State} {capacity data length bump : UInt32}
    (h : BoundedReadInv input consumed remaining store capacity data length bump)
    (hfull : length = capacity) :
    (readToEndNewCapacity capacity).toNat ≤ capacityBound input.length := by
  have hs := congrArg List.length h.split
  simp only [List.length_append] at hs
  have hl : capacity.toNat = consumed.length := by rw [← hfull]; exact h.length_nat
  rw [readToEndNewCapacity_toNat capacity h.toReadToEndInv.capacity_small]
  unfold capacityBound
  omega

/-- Reallocation copies at most the capacity-potential increase. -/
theorem copied_capacity_bound {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State} {capacity data length bump : UInt32}
    (h : BoundedReadInv input consumed remaining store capacity data length bump) :
    capacity.toNat ≤ (readToEndNewCapacity capacity).toNat - capacity.toNat := by
  rw [readToEndNewCapacity_toNat capacity h.toReadToEndInv.capacity_small]
  omega

/-- Allocation is alignment one, and doubling keeps total retained bump usage
within twice the newest capacity. This holds even on the final EOF growth. -/
theorem next_bump_potential {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State} {capacity data length bump : UInt32}
    (h : BoundedReadInv input consumed remaining store capacity data length bump) :
    (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤
      1054000 + 2 * (readToEndNewCapacity capacity).toNat := by
  rw [h.toReadToEndInv.finish_toNat]
  have hdoubled : 2 * capacity.toNat ≤ (readToEndNewCapacity capacity).toNat := by
    rw [readToEndNewCapacity_toNat capacity h.toReadToEndInv.capacity_small]
    exact Nat.le_max_right _ _
  have hb := h.bump_upper
  omega

/-- The input-size bound closes the allocator's signed-end arithmetic guard
for each actual full-capacity request, without assuming a successful call. -/
theorem growth_finish_bound {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State} {capacity data length bump : UInt32}
    (h : BoundedReadInv input consumed remaining store capacity data length bump)
    (hfull : length = capacity) (hfit : InputFits input.length) :
    (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat ≤ inputFrontierBound input.length ∧
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toNat < 2 ^ 31 := by
  have hb := next_bump_potential h
  have hc := selected_capacity_bound h hfull
  dsimp only [InputFits, completeFrontierBound, inputFrontierBound] at *
  omega

/-- A nonempty first allocation has capacity max(first-read-count,8). -/
theorem initial_potentials (inputBytes firstCount : Nat)
    (hcount : firstCount ≤ inputBytes) :
    max firstCount 8 ≤ capacityBound inputBytes ∧
      1054000 + max firstCount 8 ≤ 1054000 + 2 * max firstCount 8 := by
  unfold capacityBound
  omega

/-- Every complete input under this conservative bound has representable
output size and room below the signed address boundary. -/
theorem input_fits_output (inputBytes : Nat) (h : InputFits inputBytes) :
    2 * inputBytes < UInt32.size ∧ inputFrontierBound inputBytes + max 8 (2 * inputBytes) < 2 ^ 31 := by
  unfold InputFits completeFrontierBound at h
  norm_num [UInt32.size]
  omega


/-- Actual successful byte growth preserves both the semantic invariant and
input-dependent upper potentials. The call witness is used only at this local
store-composition boundary; the loop must construct it from the input bound. -/
theorem BoundedReadInv.after_growth {input consumed remaining : List UInt8}
    {store allocStore : MachineStore Universal.State} {capacity data length bump : UInt32}
    (h : BoundedReadInv input consumed remaining store capacity data length bump)
    (hfull : length = capacity) (hfit : InputFits input.length)
    (hgrow : ByteGrowSuccess store capacity data (readToEndNewCapacity capacity) bump allocStore) :
    BoundedReadInv input consumed remaining (readToEndGrownStore allocStore capacity bump)
      (readToEndNewCapacity capacity) bump length
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump) := by
  have hfinish := growth_finish_bound h hfull hfit
  exact {
    toReadToEndInv := hgrow.grown_invariant h.toReadToEndInv
      (AllocatorResourceCost.nonnegative _ hfinish.2)
    capacity_upper := selected_capacity_bound h hfull
    bump_upper := next_bump_potential h }

/-- Reading actual bytes and committing their count preserve the upper
potentials because no allocation occurs in this part of the iteration. -/
theorem BoundedReadInv.after_read {input consumed remaining : List UInt8}
    {store : MachineStore Universal.State} {capacity data length bump chunk filled : UInt32}
    (h : BoundedReadInv input consumed remaining store capacity data length bump)
    (hfilled : filled.toNat ≤ (readToEndTarget chunk capacity length).toNat) :
    let target := readToEndTarget chunk capacity length
    let bytes := remaining.take target.toNat
    BoundedReadInv input (consumed ++ bytes) (remaining.drop bytes.length)
      (readToEndAppliedStore store data length filled target bytes)
      capacity data (length + UInt32.ofNat bytes.length) bump := by
  dsimp only
  exact ⟨h.toReadToEndInv.after_read hfilled, h.capacity_upper, h.bump_upper⟩

/-- The zero-fill charge is exactly the increase in initialized vector bytes.
This remains true at EOF, when count is zero but target can still be positive. -/
theorem fill_potential (length filled target count : Nat)
    (hfilled : filled ≤ target) (hcount : count ≤ target) :
    target - filled + (length + filled) = (length + count) + (target - count) := by omega

/-- A successful host read reduces the unread-input termination measure. -/
theorem remaining_decreases (remaining : List UInt8) (target : Nat)
    (hinput : remaining ≠ []) (hpositive : 0 < target) :
    (remaining.drop (remaining.take target).length).length < remaining.length := by
  have hn : 0 < remaining.length := List.length_pos_iff.mpr hinput
  rw [List.length_drop, List.length_take]
  omega

end Project.HexEncodeStdio.ReadToEndResourceCost
