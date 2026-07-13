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
are total and their outcomes coincide. That precondition is the hypothesis
`initial = mod0.initialStore` below.

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

/-- **Program equivalence of the two `gcd_u64` builds (primary form).**

For every argument pair and every candidate observable outcome
`(result, hostFinal)`, the two builds agree: the `opt-level = 0` export
reaches that outcome **iff** the `opt-level = 3` export does.

Reading the biconditional:

* Instantiating `result`/`hostFinal` at the value `mod3` actually returns
  forces `mod0` to return the same thing (agreement on success).
* If a build never returns — it traps or diverges — then *no* outcome is
  reachable for it, so `TerminatesWith … = False` for every `(result,
  hostFinal)`; the biconditional then forces the other build to have no
  reachable outcome either (agreement on failure).

Linear memory is never mentioned, so `mod0`'s spurious shadow-stack writes do
not break the equivalence. The `Store.host` conjunct records that the host
state is preserved identically; for this import-free module the host type is
`Unit`, so it holds automatically — it is written explicitly to pin down the
intended, general shape of the observation. -/
def GcdOptEquiv : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = mod0.initialStore →
    ∀ (result : List Value) (hostFinal : Unit),
      TerminatesWith env mod0 entry0 initial [.i64 a, .i64 b]
          (fun st vs => vs = result ∧ st.host = hostFinal)
        ↔
      TerminatesWith env mod3 entry3 initial [.i64 a, .i64 b]
          (fun st vs => vs = result ∧ st.host = hostFinal)

/-- **Program equivalence (concrete "happy-path" form).**

Both builds are total on the canonical store, so the equivalence also reads
positively: from the same initial store and the same arguments there is a
**common** return value that *both* builds produce, and *both* leave the host
state untouched. This drops the trap-symmetry that `GcdOptEquiv`'s
biconditional also expresses, in exchange for being easier to read and to
consume downstream. -/
def GcdOptEquiv' : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = mod0.initialStore →
    ∃ result : List Value,
      TerminatesWith env mod0 entry0 initial [.i64 a, .i64 b]
          (fun st vs => vs = result ∧ st.host = initial.host) ∧
      TerminatesWith env mod3 entry3 initial [.i64 a, .i64 b]
          (fun st vs => vs = result ∧ st.host = initial.host)

/-! ## Proof obligations (left as `sorry` — to be discharged in a follow-up)

These are intentionally unproved: this file is the *statement* deliverable.
The modules are not wired into `lean/Project.lean`, so the `sorry` warnings do
not reach the default build / CI. -/

theorem gcd_opt_equiv : GcdOptEquiv := by
  sorry

theorem gcd_opt_equiv' : GcdOptEquiv' := by
  sorry

end Project.NumIntegerOpt3.Equivalence
