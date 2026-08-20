import Project.NumInteger.Spec           -- opt-level 0 build: func2Config, func2_terminatesWith
import Project.NumIntegerOpt3.Spec        -- opt-level 3 build: gcdConfig, mod3_gcd_smallStep_total

/-!
# Equivalence of the two `gcd_u64` builds (`opt-level = 0` vs `opt-level = 3`)

`num_integer` and `num_integer_opt3` are compiled from **byte-for-byte the
same Rust source** (`Integer::gcd` on `u64`, Stein's binary GCD). The only
difference is the optimisation level:

* `opt-level = 0` is the unoptimised build. It carves a frame out of the
  shadow stack: it reads and writes the stack-pointer global (`global 0`),
  spills both operands into linear memory, and runs the whole algorithm
  through `i64.load`/`i64.store`. Three functions (`func0`/`func1`/`func2`);
  `gcd_u64` is exported at **func 2**, reachable as `func2Config`.

* `opt-level = 3` is the optimised build. Stein's algorithm is inlined into a
  **single** function that touches **neither linear memory nor any global** —
  it is pure register (local) computation. `gcd_u64` is exported at **func 0**,
  reachable as `gcdConfig`.

Both modules declare the *same* mutable state (a 16-page memory with no data
segments, three `i32` globals initialised to `1048576`, one 1×1 funcref
table), so their canonical initial stores coincide.

## What "equivalent" means here

We do **not** state that either program computes `Nat.gcd` (that is a separate,
already-proved fact for both). We state that the **two programs are
observationally equivalent to each other**: run from the canonical initial store
on the same arguments, they agree on the whole *observable outcome*.

The observation matches what a caller / host can see: the **returned values**
— or, symmetrically, a **trap**: if one build fails to return, so does the
other. The observation function is stated as the host state
(`MachineStore.wasm.host`), but both modules run with host type `Unit`, so
that component is trivially equal on any two stores; the meaningful content of
the equivalence is co-termination with identical return values.

The observation deliberately **excludes linear memory**. `opt-level = 0`
dirties the shadow-stack scratch region with spurious writes that
`opt-level = 3` never performs, so the two final memories genuinely differ.
That difference is invisible to the caller and is not part of the
equivalence.

## Why the initial store is constrained

`opt-level = 0` depends on a well-formed shadow stack: it subtracts from
`global 0` and accesses the frame it carves out of linear memory. On a
pathological initial store (stack pointer too low, too few pages) `opt-level = 0`
can **trap** where the memory-free `opt-level = 3` still returns `gcd`. The
canonical initial store baked into `func2Config` and `gcdConfig` ensures both
builds are total and their outcomes coincide.
-/

namespace Project.NumIntegerOpt3.Equivalence

open Wasm

/-- **Program equivalence of the two `gcd_u64` builds.**

For every argument pair, the two builds are `SmallStep.ObservationallyEquivOn`
from their canonical initial configurations: they agree on the returned value /
trap, with linear memory left unobserved. (The observation function is the
host state, which is trivial at host type `Unit`; the returned-values and
co-termination agreement is built into `ObservationallyEquivOn` itself.) -/
def GcdOptEquiv : Prop :=
  ∀ (a b : UInt64),
    SmallStep.ObservationallyEquivOn
      (Project.NumInteger.Spec.func2Config a b)
      (Project.NumIntegerOpt3.Spec.gcdConfig a b)
      (fun store => store.wasm.host)

theorem gcd_opt_equiv : GcdOptEquiv := by
  intro a b
  apply SmallStep.ObservationallyEquivOn.of_common_outcome (o := ())
  · refine (Project.NumInteger.Spec.func2_terminatesWith a b).mono ?_
    intro values store h
    exact ⟨h, Subsingleton.elim store.wasm.host ()⟩
  · refine (Project.NumIntegerOpt3.Spec.mod3_gcd_smallStep_total a b).mono ?_
    intro values store h
    exact ⟨h, Subsingleton.elim store.wasm.host ()⟩

end Project.NumIntegerOpt3.Equivalence
