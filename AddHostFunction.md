<!-- DELETE ME when host functions are fully implemented and merged. This is a
working design doc, not permanent documentation. -->

# Adding host functions

A project for verifying WebAssembly code using Lean 4. Without imports, no
program that does I/O, allocates via a host allocator, or interacts with a
runtime is verifiable — which rules out most "real" Wasm. This doc covers
how host functions land in the codebase.

## Where we are (M0–M5 done)

The initial plan went through five milestones (in commit history under PR
#15). M0–M5 introduced:

- `Module.imports : List ImportDecl` (the low end of the unified function
  index space).
- `HostFn` / `HostEnv` / `HostResult` threaded through
  `execOne` / `exec` / `run`.
- `.call id` dispatches to `env.funcs[id]` when `id < m.imports.length`,
  else `m.funcs[id - m.imports.length]`.
- WP rule: `wp_call_host_cons` + `exec_call_host_cons` helper.
- Contract layer: `HostContract` / `HostSpec` / `HostEnv.Satisfies` —
  abstract-oracle pattern from CompCert / seL4.
- `Store.host : List (UInt32 × UInt32)` — a *concrete* KV slot baked
  into the store, used by a `storage_read` / `storage_write` counter demo.

That last bullet — concrete host state baked into `Store` — is the
piece we're walking back. Pinning a single representation
(`List (UInt32 × UInt32)`) into the universal `Store` definition forces
every future host (a trace, a chain context, a filesystem) to share
that representation or to encode itself into it, and it lets Wasm-core
invariants accidentally mention the host's piece. The fix lands in M6.

## The shape we're refactoring to: `Store α`

Make the store polymorphic over the host's state type. Wasm core is
α-agnostic; concrete hosts pick their own α. Existing programs run
against `α := Unit`.

```lean
structure Store (α : Type) where
  globals      : Globals
  mem          : Mem
  dataSegments : List (Option (List UInt8)) := []
  host         : α   -- the host's mutable state; no schema baked in
```

Knock-on shapes:

```lean
inductive HostResult (α : Type) where
  | Return : List Value → Store α → HostResult α
  | Trap   : Store α → String → HostResult α

structure HostFn (α : Type) where
  params  : List ValueType := []
  results : List ValueType := []
  invoke  : Store α → List Value → HostResult α

structure HostEnv (α : Type) where
  funcs : List (HostFn α) := []

abbrev HostContract (α : Type) := Store α → List Value → HostResult α → Prop
structure HostSpec (α : Type) where contracts : List (HostContract α) := []

def HostEnv.Satisfies (env : HostEnv α) (m : Module) (spec : HostSpec α) : Prop :=
  ∀ i, i < m.imports.length →
    ∃ hf c, env.funcs[i]? = some hf ∧ spec.contracts[i]? = some c ∧
            ∀ st args, c st args (hf.invoke st args)
```

`Module` itself stays α-free (it's just bytecode + import signatures);
α enters when you pair it with a `Store α` and a `HostEnv α`.

### Design decisions (locked in)

| # | Question | Choice |
|---|---|---|
| 1 | Naming under polymorphism | **No `abbrev Store := Store Unit` alias.** Sweep the corpus to `Store Unit` explicitly so the polymorphic name is consistent everywhere. |
| 2 | `Module.initialStore` default for `α` | **`[Inhabited α]` constraint** with `host := default`. Existing callers `m.initialStore` keep working under `α := Unit`. |
| 3 | α-implicit noise across signatures | **Accept.** `Continuation α`, `Result α`, `Assertion α`, etc. flow via auto-bound implicits. |
| 4 | Vacuous env quantifier on import-free programs | **Explicit** (Option A). Every corpus theorem prefixes `∀ env : HostEnv Unit,` — makes "host-independent" visible at the spec. |
| 5 | Host reentrancy (host calls back into wasm) | **Out of scope.** No mechanism for `HostFn.invoke` to re-enter `run`. Real reentrant hosts (blockchain trampolines, JS) need a future milestone. |
| 6 | Simp firing under α-polymorphism | **Accept the low risk.** Auto-bound `{α}` unifies from `st : Store ?α`. If a real proof ever fails, add explicit `(α := X)`. |

### What pause-resume buys that this doesn't

Discussed and rejected. Pause-resume (interpreter yields `Awaiting`,
executor resumes) gives a "purer" Wasm core but pays for it with a
CEK-style frame stack, two-level fuel accounting, and `(Store × HostState)`
threaded through every post-condition. `Store α` gets all three of the
stated wins — easier host reasoning, arbitrary hosts, clean separation —
at a fraction of the surgery. Big-step `exec` / `run` survive unchanged;
proofs stay single-shot.

## Milestones

Done (PR #15 — original implementation):

| # | Scope |
|---|---|
| M0 | `Module.imports` field |
| M1 | `HostEnv` plumbing through interpreter |
| M2 | `.call` dispatches to host imports |
| M3 | `wp_call_host_cons` + WP-level proof |
| M4 | `HostContract` / `HostSpec` / `HostEnv.Satisfies` |
| M5 | Storage-backed counter, parametric over satisfying env (concrete `Store.host : List (UInt32 × UInt32)` slot) |

Done (post-`Store α` refactor):

| # | Scope |
|---|---|
| M6 | `Store α` polymorphism end-to-end. Dropped the concrete `host` slot — it is now `host : α`. `Continuation α`, `Result α`, `HostFn α`, `HostEnv α`, `HostResult α`, `HostContract α`, `HostSpec α` all parameterized. `[Inhabited α]` constraint on `Module.initialStore`. Corpus (interpreter examples + `programs/lean/Project/*`) swept to `Store Unit`. Counter lives at α := `Counter.HostState = List (UInt32 × UInt32)`. |
| M7 | `TerminatesWith` / `PartiallyMeets` / `FuncSpec` take `env : HostEnv α` explicitly (Option A). All 106+ atomic wp simp lemmas + `wp_block_cons` / `wp_iff_cons` / `wp_loop_cons` / `wp_loop_br0_cons` are env-polymorphic. Every corpus spec now reads `∀ env : HostEnv Unit, TerminatesWith env …` — host-independence is visible at the spec. Bridge lemmas (`of_wp_entry*`, `mono`, `to_TerminatesWith`, `toPartiallyMeets`, `of_run`, `of_run_eq`) all updated. |
| M8 | This document updated to reflect the polymorphic design as built. |

Pending:

| # | Scope | Done = |
|---|---|---|
| M9 (stretch) | WAT decoder support so a `.wat` with `(import "env" "log" …)` round-trips into `Module.imports`. | One program in `programs/lean/Project/` uses an import. |

Out of scope on purpose: import-signature validation (today's runtime
trap on mismatch is fine until a typed validator lands as its own
project), `call_indirect` through host tables, multi-module linking,
host reentrancy.

## Suggested host examples (progressively harder)

Same five from the original plan; all still apply post-`Store α`.
Two have been built (`abort` flavour in `HostDispatch`, storage in
`Counter`); the rest remain useful exercises:

1. **`log : i32 i32 → ()`** — host reads `mem[ptr, ptr+len)` and appends
   to an output trace. α := `List (List UInt8)`. Read-only on caller,
   write-only on host.
2. **`abort : i32 i32 → never`** — host trap with caller-provided message.
   Already demonstrated in `HostDispatch.lean` (sans memory arg).
3. **`get_random : () → i32`** — pure-but-unknown; contract returns any
   `i32`. Forces specs to be written as "for all return values".
4. **`storage_read : i32 i32 i32 → i32`** (blockchain) — reads from a
   host-managed KV store *into caller memory*. α := the KV map. Already
   demonstrated in `Counter.lean` *with i32 args directly*; the
   memory-passing variant is the next step.
5. **`storage_write : i32 i32 i32 i32 → ()`** — the mirror.
