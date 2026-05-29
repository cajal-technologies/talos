<!-- DELETE ME when host functions are fully implemented and merged. This is a
working design doc, not permanent documentation. -->

# Adding host functions

A project for verifying WebAssembly code using Lean 4. Today `Module` has no
`imports` field and `call` only dispatches to in-module functions. Without
imports, no program that does I/O, allocates via a host allocator, or interacts
with a runtime is verifiable — which rules out most "real" Wasm. This doc plans
how to add host functions.

## Current status of the interpreter

What's there, in the order it matters for adding hosts:

- `Module = { funcs, exports, memory, globals }` — no `imports` field at all
  (`interpreter/Interpreter/Wasm/Syntax.lean:211`).
- `Store = { globals, mem, dataSegments }` — no slot for host-owned state
  (`interpreter/Interpreter/Wasm/Syntax.lean:224`).
- `Instruction.call : Nat → Instruction` dispatches via `m.funcs[id]?`
  (`interpreter/Interpreter/Wasm/Semantics.lean:424`, `:687`) — a flat index
  space with no notion of "this index is imported".
- The fuel-free spec predicates (`TerminatesWith` / `PartiallyMeets`) take `m`,
  `initial : Store`, `args` — nothing about the host. They'd need to either be
  reparameterized over a host environment or thread host facts through the
  post-condition.
- WP layer is mature for atomic / block / loop / call, so adding a
  `wp_call_host_cons` lemma will follow the existing pattern, not reinvent it.

So the surface area to change is small but cross-cutting: AST, semantics,
Store, the WP layer's call rule, and the fuel-free predicates.

## Recommended design

### 1. Two-tier host model: a concrete `HostEnv` for executing, a `HostSpec` for proving

```lean
-- executing side: a host function is a (possibly effectful) Store transformer.
-- Mem/globals are reachable so a host fn can read/write caller memory the way
-- real hosts do (the blockchain `storage_read(key_ptr, key_len, …)` shape).
inductive HostResult
  | Return : List Value → Store → HostResult
  | Trap   : Store → String → HostResult

structure HostFn where
  signature : List ValueType × List ValueType  -- (params, results), for the validator
  invoke    : Store → List Value → HostResult

structure HostEnv where
  funcs : List HostFn   -- positional, matches Module.imports order
```

### 2. `Module.imports` occupies the low indices of the unified function index space

(As in real Wasm.)

```lean
structure ImportDecl where
  module : String       -- e.g. "env"
  name   : String       -- e.g. "log"
  params : List ValueType
  results: List ValueType

-- In semantics, `call id` becomes:
--   if id < m.imports.length then call-host (env.funcs[id])
--   else call-wasm (m.funcs[id - m.imports.length])
```

That's the only change to `call` dispatch. Everything else in the interpreter
stays put.

### 3. For proofs, abstract the host as a *relation*, not a function

```lean
/-- Per-import contract. Says nothing about *how* the host works,
    only what relating-pre-and-post is allowed when this import is called.
    e.g. `log` could be: `fun st args st' rs => st' = st ∧ rs = []`. -/
abbrev HostContract := Store → List Value → Store → List Value → Prop

structure HostSpec (m : Module) where
  contracts : List HostContract   -- length = m.imports.length

/-- A `HostEnv` *satisfies* a `HostSpec` if every concrete invocation
    is permitted by the corresponding contract. -/
def HostEnv.Satisfies (env : HostEnv) (spec : HostSpec m) : Prop :=
  ∀ i st args st' rs,
    (env.funcs[i]?.map (·.invoke st args)) = some (.Return rs st') →
    ∃ c, spec.contracts[i]? = some c ∧ c st args st' rs
```

Program theorems are stated
`∀ env, env.Satisfies hostSpec → TerminatesWith env m entry args P`. The
executor side picks any satisfying `env`; the proof side only ever knows the
contracts. Same pattern as parametric stack frames in CompCert and the
"abstract oracle" technique in seL4.

### 4. Threading

Pass `HostEnv` next to `Module` everywhere (`run`, `execOne`, `exec`, `wp`).
Do **not** put it in `Store` — it isn't mutable, and it isn't part of the
program's state, so keeping it on the side mirrors `Module` and avoids `Store`
invariants growing.

## Suggested host examples (progressively harder)

1. **`log : i32 i32 → ()`** (NEAR/EVM/WASI-style trace) — pops `(ptr, len)`,
   host reads `mem[ptr, ptr+len)` and appends to an *output trace*
   `List (List UInt8)` that lives in the host's piece of `Store`. Contract:
   trace grows by exactly the read bytes; memory unchanged. Good first
   example: read-only on caller, write-only on host, easy invariant.
2. **`abort : i32 i32 → never`** — host trap with caller-provided message.
   Contract: always returns `.Trap`. Demonstrates that traps from imports
   compose with the existing `Continuation.Trap` path.
3. **`get_random : () → i32`** — pure-but-unknown. Contract: returns any
   `i32`. Forces specs to be written as "for all return values", catching the
   bug where someone accidentally relies on a specific value.
4. **`storage_read : i32 i32 i32 → i32`** (blockchain) — reads from a
   host-managed KV store *into caller memory*. Contract: a relation tying the
   abstract storage map, the bytes written to caller memory, and the
   return-value-as-length. First example where the host both *reads* (key
   from mem) and *writes* (value to mem) the caller's linear memory.
5. **`storage_write : i32 i32 i32 i32 → ()`** — the mirror. Pair (4) and (5)
   for the canonical "blockchain smart contract that increments a counter on
   chain" example — the milestone that proves the design works for the
   eventual target use case.

## Milestones

| # | Scope | Done = |
|---|---|---|
| M0 | `Module.imports` field, decoder ignores it, all existing builds pass | green build with the new field empty |
| M1 | Threading: add `HostEnv` parameter through `run` / `exec` / `execOne` (default empty for back-compat), add host slot typed by host | examples still compile with `()` host |
| M2 | `Instruction.call` dispatches to host when `id < imports.length`. `runHost` test using a concrete `log` host that prints to a trace. `native_decide` examples cover return + trap + reading caller mem | runnable end-to-end |
| M3 | WP layer: `wp_call_host_cons` lemma analogous to `wp_call_cons`, parameterized by the import's contract | factorial-style example using `log` proves a trace-shape postcondition |
| M4 | `HostSpec` + `HostEnv.Satisfies`. `TerminatesWith` and `PartiallyMeets` reparameterized to take an `env` that's universally bound *outside* the contract assumption | example (1) re-stated parametric over env |
| M5 | The two halves of a blockchain-style host: `storage_read` + `storage_write`. Proof of a "counter contract" that on entry reads `counter` from storage, increments, writes back, parametric over any satisfying env | demonstrates host fns mutating caller memory and host KV in one example |
| M6 (stretch) | Decoder support so a hand-written `.wat` with `(import "env" "log" …)` round-trips | one program in `programs/` uses an import |

Out of scope on purpose: validation of import signatures (M2 traps on
signature mismatch at runtime; a typed validator is its own project),
`call_indirect` through host tables, multi-module linking.

## Things to avoid

Don't put host state inside `Store`. It looks tempting because it keeps the
existing `run : … → Result` shape, but it forces every `Store` invariant to
mention the host's piece, and it conflates "Wasm-visible state" with "host's
view of the world". Keep them separate — `HostEnv` alongside `Module`,
host's mutable view as its own field — and the existing memory/globals lemmas
don't have to change.
