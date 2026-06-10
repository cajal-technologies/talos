import Project.HostCounter.Spec

/-!
# Proof of `StepPreservesInv`

The exported `step()` is a thin wrapper (`func1`, unified index `3`)
that calls into the guarded-increment body (`func0`, unified index `2`):

```
;; func1 (= step, unified index 3)
call 2
return

;; func0 (unified index 2)
block 0 0
  call $host_get      -- pushes counter as i32
  i32.const 10
  i32.lt_u            -- 1 if counter < 10, else 0
  i32.const 1
  i32.and             -- unchanged (guard bit & 1)
  i32.eqz             -- 1 if counter ≥ 10, else 0
  br_if 0             -- if non-zero, exit the block (skip the bump)
  call $host_inc      -- only reached when counter < 10
end
return
```

so there are two execution paths through the block of `func0`:

* **counter ≥ 10.** From `CounterInv` we know `counter ≤ 10`, so this
  branch can only fire at `counter = 10`. `br_if` exits the block with
  the store untouched — the invariant survives trivially.
* **counter < 10.** We fall through to `call $host_inc`, which bumps
  the counter to `counter + 1 ≤ 10`. The invariant survives.

The proof splits accordingly: an inner lemma (`func0_meets_inv`)
establishes `TerminatesWith` for `func0` at the given store, and the
main theorem enters `func1`, discharges its `.call 2` against the
inner lemma via `wp_call_at`, and reduces the trailing `.ret`.

Both pieces are parametric over every `HostEnv` satisfying
`counterSpec`: we only ever consume the two contracts, never a
concrete `HostFn`.
-/

namespace Project.HostCounter.Proof

open Wasm
open Project.HostCounter
open Project.HostCounter.Host
open Project.HostCounter.Spec

/-- The guarded-increment body `func0` (unified index `2`), run at any
store satisfying `CounterInv` under any host satisfying `counterSpec`,
terminates with no values and a store still satisfying `CounterInv`. -/
theorem func0_meets_inv (env : HostEnv CounterState)
    (initial : Store CounterState)
    (hSat : env.Satisfies «module» counterSpec)
    (hInv : CounterInv initial) :
    TerminatesWith env «module» 2 initial []
      (fun st vs => CounterInv st ∧ vs = []) := by
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
  -- Reduce `TerminatesWith` to a `wp` obligation on the body of `func0`
  -- (in-module index 0; unified index 2).
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[], [], func0, []⟩) (by rfl)
  -- Initial frame is empty (no params/locals/values).
  show wp _ func0 _ initial _ _
  unfold func0
  -- Peel the outermost block. ps = rs = 0, so the inner frame inherits
  -- the empty value stack and an exit (Fallthrough / Break 0) restores
  -- it. The `rest` after the block is `[.ret]`, which `wp_ret_cons`
  -- reduces against the entry post.
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
    -- Symbolically execute through `const 10`, `ltU`, `const 1`, `and`,
    -- `eqz`, `br_if 0`. After `eqz` the top of stack is
    -- `if counter < 10 then 0 else 1` (as `UInt32`), so `br_if 0`
    -- branches iff `counter ≥ 10`.
    wp_run
    -- Two paths: invariant says counter ≤ 10, so ¬(counter < 10) ⟺ counter = 10.
    set counter := initial.host.counter with hCounterDef
    have hInvNat : counter ≤ 10 := hInv
    have hSize : UInt32.size = 4294967296 := rfl
    have hCounterLt : counter < UInt32.size := by
      simp only [hSize]; omega
    have hCounter32 : (UInt32.ofNat counter).toNat = counter :=
      UInt32.toNat_ofNat_of_lt' hCounterLt
    by_cases hcmp : UInt32.ofNat counter < (10 : UInt32)
    · -- counter < 10. Fall through to `.call 1` (host_inc), which bumps
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
        -- After inc, the block body is done; the trailing `.ret`
        -- reduces by `wp_ret_cons` against the entry post.
        wp_run
        -- Goal: counter + 1 ≤ 10 (plus the trivial values component).
        -- We know counter ≤ 10 (hInv) and counter < 10 (from hcmp). The
        -- UInt32 comparison lifts to `Nat` via toNat.
        have hcmp_nat : counter < 10 := by
          have hlift : (UInt32.ofNat counter).toNat < (10 : UInt32).toNat :=
            UInt32.lt_iff_toNat_lt.mp hcmp
          have h10 : (10 : UInt32).toNat = 10 := by decide
          rw [h10, hCounter32] at hlift
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
    · -- counter ≥ 10. With invariant `counter ≤ 10`, that pins counter = 10.
      -- `br_if 0` fires → exit the block with the original store; the
      -- trailing `.ret` returns with the (empty) stack.
      simp [hcmp]
      -- Goal: CounterInv initial (plus the trivial values component).
      exact hInv
  · -- Trap branch for host_get — ruled out by the contract.
    intro st' msg hInv'
    simp only [List.take,
               List.reverse_nil] at hInv'
    have hContract := hCall_get initial []
    simp only [getContract] at hContract
    obtain ⟨_, hRes⟩ := hContract
    rw [hRes] at hInv'
    cases hInv'

/-- `step` preserves the `CounterInv` invariant under any host satisfying
`counterSpec`. -/
@[proves Project.HostCounter.Spec.StepPreservesInv]
theorem step_preserves_inv : StepPreservesInv := by
  intro env initial hSat hInv
  apply TerminatesWith.toPartiallyMeets
  -- Reduce `TerminatesWith` to a `wp` obligation on the body of the
  -- exported wrapper `func1` (in-module index 1; unified index 3 = stepIdx).
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[], [], func1, []⟩) (by rfl)
  -- Initial frame is empty (no params/locals/values).
  show wp _ func1 _ initial _ _
  unfold func1
  -- `.call 2` dispatches into `func0`; its behaviour at this store is
  -- exactly the inner lemma's `TerminatesWith`, unfolded.
  refine wp_call_at (Post := fun st vs => CounterInv st ∧ vs = [])
    (func0_meets_inv env initial hSat hInv) ?_
  -- After the call returns (empty stack, invariant holds), the trailing
  -- `.ret` returns the (empty) stack against the entry post.
  rintro st' vs ⟨hInv', rfl⟩
  wp_run
  exact hInv'

end Project.HostCounter.Proof
