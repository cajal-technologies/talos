import CodeLib

/-!
# Host design for `host_counter`

The Rust crate imports two host functions:

```
host_inc()        : ()    → ()
host_get()        : ()    → u32
```

They share a single piece of host state — a counter — and the
program-level proof reasons about the contracts, not a specific
implementation. This file defines:

* `CounterState` — the shape of `Store.host` for this host.
* `incContract` / `getContract` — the per-import `HostContract`s.
* `counterSpec` — the `HostSpec` bundling both contracts in import
  order (`host_get` at index `0`, `host_inc` at index `1`). The order
  matches how the Rust toolchain lays out the imports in the emitted
  wasm — verified against `programs/rust/build/host_counter/program.wat`.
* `incHost` / `getHost` / `counterEnv` — a reference `HostEnv`
  implementing the contracts (handy for `native_decide` smoke tests
  and as the witness that `counterSpec` is satisfiable).

The program-level `@[spec_of]` theorem in `Spec.lean` quantifies over
every `HostEnv` that `Satisfies` `counterSpec`, so any implementation
matching the contracts — not just `counterEnv` — is covered.
-/

namespace Project.HostCounter.Host

open Wasm

/-- Host-side state: a single natural-number counter. Stored as `Nat`
(not `UInt32`) so the invariant `counter ≤ 10` reads cleanly and the
contracts don't need to worry about wraparound — the invariant keeps
the value far below `2^32` regardless. -/
structure CounterState where
  counter : Nat
deriving Repr, Inhabited

/-- Contract for `host_inc`: takes no arguments, returns no values,
never traps, and bumps `st.host.counter` by `1`. All other store
fields are preserved. -/
def incContract : HostContract CounterState := fun st args res =>
  args = [] ∧
  res = .Return [] { st with host := ⟨st.host.counter + 1⟩ }

/-- Contract for `host_get`: takes no arguments, returns the current
counter as an `i32`, never traps, and leaves the store untouched.

Returning `UInt32.ofNat st.host.counter` is faithful as long as the
counter stays below `2^32`; the program-level invariant ensures this. -/
def getContract : HostContract CounterState := fun st args res =>
  args = [] ∧
  res = .Return [.i32 (UInt32.ofNat st.host.counter)] st

/-- The host specification bundling both contracts in import order:
`host_get` at index `0`, `host_inc` at index `1` (as emitted by the
Rust toolchain into `program.wat`). So `counterSpec.contracts[0]?`
resolves `call 0` (`host_get`) and `[1]?` resolves `call 1`
(`host_inc`). -/
def counterSpec : HostSpec CounterState :=
  { contracts := [getContract, incContract] }

/-! ## A reference host implementation

`counterEnv` provides a concrete `HostFn` for each contract. It is
not used by the program-level spec (which quantifies over every
satisfying environment) but it gives us a witness that `counterSpec`
is inhabited, and is convenient for end-to-end `native_decide`
smoke tests. -/

/-- Reference implementation of `host_inc`. -/
def incHost : HostFn CounterState :=
  { params := []
    results := []
    invoke  := fun st _ =>
      .Return [] { st with host := ⟨st.host.counter + 1⟩ } }

/-- Reference implementation of `host_get`. -/
def getHost : HostFn CounterState :=
  { params := []
    results := [.i32]
    invoke  := fun st _ =>
      .Return [.i32 (UInt32.ofNat st.host.counter)] st }

/-- Reference `HostEnv` for the counter host. Order matches the wasm
import order: `host_get` at unified index `0`, `host_inc` at index `1`. -/
def counterEnv : HostEnv CounterState :=
  { funcs := [getHost, incHost] }

end Project.HostCounter.Host
