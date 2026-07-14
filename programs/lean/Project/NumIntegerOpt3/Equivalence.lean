import Project.NumInteger.Program        -- opt-level 0 build → `Project.NumInteger.module`
import Project.NumIntegerOpt3.Program    -- opt-level 3 build → `Project.NumIntegerOpt3.module`

/-!
# Equivalence of the two `gcd_u64` builds (`opt-level = 0` vs `opt-level = 3`)

`num_integer` and `num_integer_opt3` are compiled from **byte-for-byte the
same Rust source** (`Integer::gcd` on `u64`, Stein's binary GCD). The only
difference is the optimisation level:

* `mod0` (`opt-level = 0`) is the unoptimised build. It carves a frame out of
  the shadow stack: it reads and writes the stack-pointer global (`global 0`),
  spills both operands into linear memory, and runs the whole algorithm
  through `i64.load`/`i64.store`. Three functions (`func0`/`func1`/`func2`);
  `gcd_u64` is exported at **func 2**.

* `mod3` (`opt-level = 3`) is the optimised build. Stein's algorithm is
  inlined into a **single** function that touches **neither linear memory nor
  any global** — it is pure register (local) computation. `gcd_u64` is
  exported at **func 0**.

Both modules declare the *same* mutable state (a 16-page memory with no data
segments, three `i32` globals initialised to `1048576`, one 1×1 funcref
table), so `mod0.initialStore = mod3.initialStore`.

## What "equivalent" means here

We do **not** state that either program computes `Nat.gcd` (that is a separate,
already-proved fact for `mod0`). We state that the **two programs are
observationally equivalent to each other**: run from the same initial store on
the same arguments, they agree on the whole *observable outcome*.

The observation is deliberately chosen to match what a caller / host can see:

* the **returned values** — or, symmetrically, a **trap** (`sea salida o
  fallo`): if one build fails to return, so does the other;
* the **host's internal state** (`Store.host`) at the end.

The observation deliberately **excludes linear memory**. `mod0` dirties the
shadow-stack scratch region (the "espurio" writes) that `mod3` never performs,
so the two final memories genuinely differ. That difference is invisible to
the caller and is not part of the equivalence.  (Aside: the globals *do* end
up equal — `mod0` restores `global 0` and `mod3` never touches it — but, like
memory, they are module-internal state and are not part of the observation we
insist on.)

## Why the initial store is constrained

`mod0` depends on a well-formed shadow stack: it subtracts from `global 0` and
accesses the frame it carves out of linear memory. On a pathological initial
store (stack pointer too low, too few pages) `mod0` can **trap** where the
memory-free `mod3` still returns `gcd`. So the two are *not* equivalent for a
completely arbitrary initial state. Restricted to the canonical initial store
(`global 0 = 1048576`, 16 zeroed pages — i.e. `mod0.initialStore`) both builds
are total and their outcomes coincide. That is why `mod0.initialStore` is the
fixed starting store passed to `ObservationallyEquiv` below.

Everything in this file is a **statement only** — the proofs are left as
`sorry` for a follow-up.
-/

namespace Project.NumIntegerOpt3.Equivalence

open Wasm

/-- The unoptimised (`opt-level = 0`) build: shadow-stack version. -/
abbrev mod0 : Wasm.Module := Project.NumInteger.module

/-- The optimised (`opt-level = 3`) build: register-only version. -/
abbrev mod3 : Wasm.Module := Project.NumIntegerOpt3.module

/-- `gcd_u64` is exported at func **2** in the `opt-level = 0` build. -/
abbrev entry0 : Nat := 2

/-- `gcd_u64` is exported at func **0** in the `opt-level = 3` build. -/
abbrev entry3 : Nat := 0

/-! ## The equivalence -/

/-- **Program equivalence of the two `gcd_u64` builds.**

For every argument pair, the two builds are `Wasm.ObservationallyEquiv` from
the canonical initial store: they agree on the returned value / trap and on the
host state, with linear memory left unobserved (the general notion, and why a
trap on one side forces a trap on the other, live in `CodeLib.Equivalence`).

Passing `mod0.initialStore` as the fixed starting store is load-bearing — on a
pathological store `mod0` can trap where the memory-free `mod3` still returns
(see the note above). -/
def GcdOptEquiv : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    ObservationallyEquiv env mod0 entry0 mod3 entry3 mod0.initialStore [.i64 a, .i64 b]

/-! ## Proof obligation (left as `sorry` — to be discharged in a follow-up)

This is intentionally unproved: this file is the *statement* deliverable.
The modules are not wired into `lean/Project.lean`, so the `sorry` warning does
not reach the default build / CI. -/

theorem gcd_opt_equiv : GcdOptEquiv := by
  sorry

end Project.NumIntegerOpt3.Equivalence
