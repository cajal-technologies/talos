import Project.HostCounter.Spec

/-!
# Proof of `StepPreservesInv`

The exported `step()` body (cf. `Program.lean`):

```
block 0 0
  call $host_get      -- pushes counter as i32
  i32.const 9
  i32.gt_u            -- 1 if counter > 9, else 0
  br_if 0             -- if non-zero, exit the block (skip the bump)
  call $host_inc      -- only reached when counter ≤ 9
end
```

so there are two execution paths through the block:

* **counter > 9.** From `CounterInv` we know `counter ≤ 10`, so this
  branch can only fire at `counter = 10`. `br_if` exits the block with
  the store untouched — the invariant survives trivially.
* **counter ≤ 9.** We fall through to `call $host_inc`, which bumps
  the counter to `counter + 1 ≤ 10`. The invariant survives.

The proof is parametric over every `HostEnv` satisfying `counterSpec`:
we only ever consume the two contracts, never a concrete `HostFn`.
-/

namespace Project.HostCounter.Proof

open Wasm
open Project.HostCounter
open Project.HostCounter.Host
open Project.HostCounter.Spec

/-- `step` preserves the `CounterInv` invariant under any host satisfying
`counterSpec`. -/
@[proves Project.HostCounter.Spec.StepPreservesInv]
theorem step_preserves_inv : StepPreservesInv := by
  intro env initial hSat hInv
  apply TerminatesWith.toPartiallyMeets
  -- Pull resolver + contract for each import out of the satisfaction.
  obtain ⟨hf_get, c_get, hEnv_get, hC_get, hCall_get⟩ := hSat 0 (by decide)
  obtain ⟨hf_inc, c_inc, hEnv_inc, hC_inc, hCall_inc⟩ := hSat 1 (by decide)
  -- The contracts for indices 0/1 are definitionally `getContract` /
  -- `incContract` (cf. `counterSpec` in Host.lean). Reduce away the
  -- generic `c_get` / `c_inc` so subsequent calls use the concrete shape.
  have hC0 : counterSpec.contracts[0]? = some getContract := rfl
  have hC1 : counterSpec.contracts[1]? = some incContract := rfl
  rw [hC0] at hC_get; injection hC_get with hC_get'; subst hC_get'
  rw [hC1] at hC_inc; injection hC_inc with hC_inc'; subst hC_inc'
  -- Reduce `TerminatesWith` to a `wp` obligation on the body of `step`
  -- (in-module index 0; unified index 2 = stepIdx).
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[], [], func0, []⟩) (by rfl)
  -- Initial frame is empty (no params/locals/values).
  show wp _ func0 _ initial _ _
  unfold func0
  -- Peel the outermost block. ps = rs = 0, so the inner frame inherits
  -- the empty value stack and an exit (Fallthrough / Break 0) restores
  -- it. No outer `rest` means a Fallthrough out of the block lands at
  -- `wp _ [] _` which closes by `wp_nil` against the entry post.
  apply wp_block_cons
  -- Inside the block, stack is empty. First instruction: `.call 0`
  -- (host_get). Use the WP rule for host calls and discharge both
  -- outcomes via the contract.
  refine wp_call_host_cons
    (imp := { «module» := "env", name := "host_get",
              params := [], results := [.i32] })
    (hf := hf_get) rfl hEnv_get ?_ ?_
  · -- Return branch: host_get returned with the counter on the stack.
    intro vs st' hInv'
    -- The args slot in `hInv'` is `(List.take 0 …).reverse`; reduce it
    -- to `[]` so the abstract `hf_get.invoke initial []` lines up with
    -- the contract's specialisation below.
    simp only [List.take,
               List.reverse_nil] at hInv'
    -- Specialise the get contract at `(initial, [])`.
    have hContract := hCall_get initial []
    -- `getContract initial [] (hf_get.invoke initial [])` unfolds to
    -- `[] = [] ∧ hf_get.invoke … = .Return [.i32 (UInt32.ofNat …)] initial`.
    simp only [getContract] at hContract
    obtain ⟨_, hRes⟩ := hContract
    rw [hRes] at hInv'
    injection hInv' with hvs hst
    subst hvs; subst hst
    -- Symbolically execute through `const 9`, `gtU`, `br_if 0`.
    -- After `gtU` the top of stack is `if counter > 9 then 1 else 0`
    -- (as `UInt32`), so `br_if 0` branches iff `counter > 9`.
    wp_run
    -- Two paths: invariant says counter ≤ 10, so `counter > 9` ⟺ `counter = 10`.
    set counter := initial.host.counter with hCounterDef
    have hInvNat : counter ≤ 10 := hInv
    have hSize : UInt32.size = 4294967296 := rfl
    have hCounterLt : counter < UInt32.size := by
      simp only [hSize]; omega
    have hCounter32 : (UInt32.ofNat counter).toNat = counter :=
      UInt32.toNat_ofNat_of_lt' hCounterLt
    by_cases hcmp : (9 : UInt32) < UInt32.ofNat counter
    · -- counter > 9. With invariant `counter ≤ 10`, that pins counter = 10.
      -- `br_if 0` fires → exit the block with the original store.
      simp [hcmp]
      -- Goal: CounterInv initial — trivially from `hInv`.
      exact hInv
    · -- counter ≤ 9. Fall through to `.call 1` (host_inc), which bumps
      -- the counter by one; the new value is ≤ 10.
      simp [hcmp]
      refine wp_call_host_cons
        (imp := { «module» := "env", name := "host_inc",
                  params := [], results := [] })
        (hf := hf_inc) rfl hEnv_inc ?_ ?_
      · -- Return branch for host_inc.
        intro vs2 st2 hInv2
        simp only [List.take,
                   List.reverse_nil] at hInv2
        have hContract2 := hCall_inc initial []
        simp only [incContract] at hContract2
        obtain ⟨_, hRes2⟩ := hContract2
        rw [hRes2] at hInv2
        injection hInv2 with hvs2 hst2
        subst hvs2; subst hst2
        -- After inc, the block body is done; we reach `wp _ [] _` and
        -- close by `wp_nil` against the outer post (`CounterInv`).
        wp_run
        -- Goal: counter + 1 ≤ 10.
        -- We know counter ≤ 10 (hInv) and counter ≤ 9 (from hcmp). The
        -- UInt32 comparison `counter ≤ 9` lifts to `Nat` via toNat.
        have hcmp_nat : counter ≤ 9 := by
          have hlift : ¬ (9 : UInt32).toNat < (UInt32.ofNat counter).toNat := by
            intro h; exact hcmp (UInt32.lt_iff_toNat_lt.mpr h)
          have h9 : (9 : UInt32).toNat = 9 := by decide
          rw [h9, hCounter32] at hlift
          omega
        show CounterInv _
        simp only [CounterInv]
        omega
      · -- Trap branch for host_inc — ruled out by the contract.
        intro st2 msg hInv2
        simp only [List.take,
                   List.reverse_nil] at hInv2
        have hContract2 := hCall_inc initial []
        simp only [incContract] at hContract2
        obtain ⟨_, hRes2⟩ := hContract2
        rw [hRes2] at hInv2
        cases hInv2
  · -- Trap branch for host_get — ruled out by the contract.
    intro st' msg hInv'
    simp only [List.take,
               List.reverse_nil] at hInv'
    have hContract := hCall_get initial []
    simp only [getContract] at hContract
    obtain ⟨_, hRes⟩ := hContract
    rw [hRes] at hInv'
    cases hInv'

end Project.HostCounter.Proof
