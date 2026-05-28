# verifier

A small Lean CLI that drives the Rust → wasm → Lean verification loop.
`verifier new <path>` scaffolds a fixed-shape project from a bundled
template (a Cargo workspace + a Lean project); `verifier check` builds
every crate to wasm, decodes it into a Lean `Program.lean`, and runs
`lake build`.

## Build

```bash
cd verifier
lake build       # produces .lake/build/bin/verifier
```

## Project layout

`verifier` is convention-driven — there are no `verifier.toml` /
`origin.toml` files. Every project has the same fixed shape:

```
project/
  rust/
    Cargo.toml                ← cargo workspace
    .cargo/config.toml        ← `cargo build-wasm` alias
    is_even/
      Cargo.toml
      src/lib.rs              ← `pub fn is_even(...) -> bool { ... }`
      src/exports.rs          ← `#[unsafe(no_mangle)] pub extern "C" fn is_even`
    is_odd/
      Cargo.toml              ← depends on `is_even` (path = "../is_even")
      src/lib.rs
      src/exports.rs
    build/
      is_even/{program.wasm, program.wat}   ← produced by `verifier check`
      is_odd/{program.wasm, program.wat}
  lean/
    lakefile.toml             ← name = "Project", CodeLib as a git dep
    lean-toolchain            ← matches the verifier's own toolchain
    Project.lean              ← imports each `Project.<Crate>.Proof`
    Project/
      IsEven/
        Program.lean          ← auto-generated from build/is_even/program.wasm
        Spec.lean             ← `def MyProp : Prop := …` statements
        Proof.lean            ← `theorem _ : MyProp := …` proofs
      IsOdd/
        Program.lean
        Spec.lean
        Proof.lean
```

The rust↔lean mapping is by name: crate `foo_bar` ↔ Lean module
`Project.FooBar` (snake_case → PascalCase). If a Lean module dir is
missing for a crate, `verifier check` errors out — the shape is fixed.

## Setting up a Rust crate for wasm

The bundled template already does this for you; this section explains
the conventions in case you add more crates by hand.

**`Cargo.toml`** — declare a `cdylib` crate so the wasm output is a
freestanding module:

```toml
[package]
name    = "foo"
version = "0.1.0"
edition = "2024"

[lib]
crate-type = ["cdylib", "rlib"]
```

The workspace-root `Cargo.toml` keeps the release profile small so the
emitted wasm stays decoder-friendly:

```toml
[profile.release]
opt-level = "s"
lto       = true
```

**`rust/.cargo/config.toml`** — a `build-wasm` alias so you don't have
to re-type the target every time. Lives at the workspace root, not
inside individual crates:

```toml
[alias]
build-wasm = "build --release --target wasm32-unknown-unknown"
```

After this `cargo build-wasm` (run from `rust/`) produces every member
crate's wasm under `target/wasm32-unknown-unknown/release/<crate>.wasm`.
`verifier check` invokes this command and then copies each output into
`rust/build/<crate>/program.wasm`.

**`src/exports.rs`** — the single module that pins the public surface
the verifier reasons about. Every function the verifier should see
lives here, marked `#[unsafe(no_mangle)] pub extern "C"`:

```rust
#[unsafe(no_mangle)]
pub extern "C" fn is_even(n: i32) -> bool {
    crate::is_even(n)
}
```

**`src/lib.rs`** — the public Rust API (kept separate from the C-ABI
wrappers so Rust callers and verifier-visible exports stay distinct):

```rust
mod exports;

pub fn is_even(n: i32) -> bool {
    n % 2 == 0
}
```

Keeping exports in their own file means the wasm export table matches
exactly what's listed in `exports.rs`, which is the surface area
`Spec.lean` writes properties against.

## Tutorial

### 1. Bootstrap a new project

```bash
lake exe verifier new my-project
```

`<path>` must not exist (or must be empty). This:

1. Copies the bundled template (cargo workspace with `is_even` and
   `is_odd`, plus a Lean `Project` lib) into `my-project/`.
2. Runs `cargo check` inside `my-project/rust/`.
3. Runs an initial `lake build` inside `my-project/lean/` to fetch
   CodeLib and warm caches.

Once it returns, you have a fully working example you can edit in
place — add a function in `rust/<crate>/src/lib.rs`, mirror it in
`exports.rs`, and re-run `verifier check`.

### 2. Build + verify

```bash
cd my-project
lake exe verifier check
```

This **must** be run from the project root (the directory containing
`rust/` and `lean/`).

Pipeline:

1. `cargo build-wasm` in `rust/` — builds every workspace member.
2. For each crate:
   - Copy `target/wasm32-unknown-unknown/release/<crate>.wasm` to
     `rust/build/<crate>/program.wasm` (only writes when bytes change,
     so re-runs are idempotent).
   - `wasm-tools print` → `rust/build/<crate>/program.wat`.
   - If the wasm is newer than `lean/Project/<Crate>/Program.lean` (or
     `--force-emit`), decode the wat in-process and re-emit
     `Program.lean`.
3. One `lake build` in `lean/`.
4. Summary line: crate count, `lake build` status, `sorry` count.

### 3. Adding a crate

1. `mkdir rust/foo_bar && …` — write `Cargo.toml`, `src/lib.rs`,
   `src/exports.rs` following the conventions above.
2. Add `"foo_bar"` to the `members` list in `rust/Cargo.toml`.
3. Create `lean/Project/FooBar/{Program,Spec,Proof}.lean` (you can
   copy the `IsEven` ones as a starting point).
4. Add `import Project.FooBar.Proof` to `lean/Project.lean`.
5. `lake exe verifier check`.

### 4. Writing specs and proofs

`Spec.lean` (statements as `def : Prop`):

```lean
import Project.IsEven.Program

namespace Project.IsEven.Spec
open Wasm

/-- The exported `is_even` returns 1 for even inputs and 0 otherwise. -/
def IsEvenSpec : Prop :=
  ∀ (initial : Store) (n : UInt32),
    TerminatesWith «module» 0 initial [.i32 n]
      (fun _ rs => rs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)])

end Project.IsEven.Spec
```

`Proof.lean` (theorems that close those statements):

```lean
import Project.IsEven.Spec

namespace Project.IsEven.Proof
open Project.IsEven.Spec

theorem is_even_spec : IsEvenSpec := by
  intro initial n
  -- … your proof …

end Project.IsEven.Proof
```

## Commands

```
verifier new   <project-path>
verifier check [--force-emit]
verifier report                  (stub — not implemented)
```

- `verifier new` requires a non-existent or empty target directory.
- `verifier check` must be run from the project root.
- `--force-emit` re-emits every `Program.lean` even when its
  corresponding `program.wasm` hasn't changed.

### CodeLib source

The bundled `lakefile.toml` requires `CodeLib` (the Wasm interpreter +
`wp` tactic your specs build on) from the public Talos GitHub remote,
so a freshly scaffolded project is self-contained:

```toml
[[require]]
name = "CodeLib"
git = "https://github.com/cajal-technologies/talos"
subDir = "codelib"
rev = "main"
```

The matching `lean-toolchain` is baked into the verifier binary at
compile time (from `verifier/lean-toolchain`) and copied into every new
project.

## Tooling required

- `cargo` with the `wasm32-unknown-unknown` target installed
  (`rustup target add wasm32-unknown-unknown`)
- [`wasm-tools`](https://github.com/bytecodealliance/wasm-tools)
  (`brew install wasm-tools` or `cargo install wasm-tools`)
- `lake` (comes with the Lean toolchain pinned in `verifier/lean-toolchain`)
