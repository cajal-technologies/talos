# verifier

A small Lean CLI that drives the Rust → wasm → Lean verification loop.
`verifier init <path>` (`new` is an alias) scaffolds a fixed-shape project from a bundled
template (a Cargo workspace + a Lean project); `verifier check` (or `build` / `emit` / `prove` separately) builds
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
    build/
      is_even/{program.wasm, program.wat}   ← produced by `verifier build`
  lean/
    lakefile.toml             ← name = "Project", CodeLib as a git dep
    lean-toolchain            ← matches the verifier's own toolchain
    Project.lean              ← imports each `Project.<Crate>.Spec`
    Project/
      IsEven/
        Program.lean          ← auto-generated from build/is_even/program.wasm
        Spec.lean             ← `def MyProp : Prop := …` + proofs (scaffolded by `verifier emit`)
```

The rust↔lean mapping is by name: crate `foo_bar` ↔ Lean module
`Project.FooBar` (snake_case → PascalCase). `verifier emit` creates the
Lean module dir if it is missing — `Program.lean` every run, and the
extra files (`Spec.lean`, …) from the bundled module template only when
they don't already exist, so your edits are never overwritten.

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
`verifier check` (or `build` / `emit` / `prove` separately) invokes this command and then copies each output into
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

1. Copies the bundled template (cargo workspace with `is_even`, plus a Lean `Project` lib) into `my-project/`.
2. Runs an initial `lake build` inside `my-project/lean/` to fetch
   CodeLib and warm caches.

Once it returns, you have a fully working example you can edit in
place — add a function in `rust/<crate>/src/lib.rs`, mirror it in
`exports.rs`, and re-run `verifier check` (or `build` / `emit` / `prove` separately).

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

1. Create `rust/foo_bar/` by hand — copying the bundled `is_even` crate
   is the easiest start — and add `"foo_bar"` to the `members` list of
   `rust/Cargo.toml`, following the conventions in "Setting up a Rust
   crate for wasm" above. No Lean files are needed yet.
2. Edit `rust/foo_bar/src/lib.rs` and `src/exports.rs` to implement and
   export your function, following the conventions above.
3. `verifier emit foo_bar` — builds the wasm (if needed), generates
   `lean/Project/FooBar/Program.lean`, and scaffolds `Spec.lean` from the
   module template. (`verifier check foo_bar` does build → emit → prove
   in one go.)
4. Add `import Project.FooBar.Spec` to `lean/Project.lean` so the new
   module is part of the build.
5. Fill in `Spec.lean`, then `verifier prove foo_bar` (or `check`).

### 4. Writing specs and proofs

`Spec.lean` (statements as `def : Prop`, linked to the Rust export
via `@[spec_of …]`):

```lean
import Project.IsEven.Program

namespace Project.IsEven.Spec
open Wasm

/-- The exported `is_even` returns 1 for even inputs and 0 otherwise.

Informal spec:
For any input `n : UInt32`, `is_even` returns `1` when `n` is even
and `0` otherwise. -/
@[spec_of "rust-exported" "is_even::is_even"]
def IsEvenSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt32),
    TerminatesWith env «module» 0 initial [.i32 n]
      (fun _ rs => rs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)])

end Project.IsEven.Spec
```

`Proof.lean` (theorems that close those statements, linked via
`@[proves]`):

```lean
import Project.IsEven.Spec

namespace Project.IsEven.Proof
open Project.IsEven.Spec

@[proves Project.IsEven.Spec.IsEvenSpec]
theorem is_even_correct : IsEvenSpec := by
  intro env initial n
  apply TerminatesWith.of_wp_entry (f := ⟨[.i32], [], func0, [.i32]⟩) rfl
  intro initial'
  unfold func0
  wp_run
  simp [UInt32.and_one_eq_zero_iff_toNat_mod_two, UInt32.and_comm]

end Project.IsEven.Proof
```

`@[spec_of]` and `@[proves]` are the load-bearing project conventions
that downstream tools (notably `verifier extract`) use to discover
specs and link them to proofs. The `Spec.lean`/`Proof.lean` file split
is recommended for organization but not required by those tools — see
[`EXTRACT.md`](EXTRACT.md) for the full rules.

## Commands

```
verifier init <path>              # alias: new
verifier del <crate>
verifier build [crate…]
verifier emit [crate…] [--force-emit]
verifier prove [crate…]
verifier check [crate…] [--force-emit] [--no-prove]
verifier extract [crate…] [--out DIR]
verifier report [crate…] [--extracted DIR] [--out DIR]
```

Run from the project root. Omit crate names to process all crates.
In the Talos monorepo: `cd programs && lake -d ../verifier exe verifier …`

- `init` / `new` requires a non-existent or empty target directory.
- `del` removes a crate: deletes `rust/<crate>/`, `lean/Project/<Crate>/`, `rust/build/<crate>/`, and cleans the workspace member from `rust/Cargo.toml` and the import from `lean/Project.lean`.
- `build` writes `rust/build/<crate>/program.{wasm,wat}` via cargo + wasm-tools.
- `emit` decodes `program.wat` into `Program.lean`, and scaffolds the
  bundled module template (`Spec.lean`) into `lean/Project/<Crate>/`,
  writing only files that don't already exist.
- `prove` runs `lake build` on `Project/<Crate>/Program.lean` and `Spec.lean` per crate (not `Proof.lean` unless you import it in `Project.lean`).
- `check` runs `build` → `emit` → `prove`.
- `--force-emit` re-emits every selected `Program.lean` even when wasm is unchanged.
- `--no-prove` skips the final `lake build` (CI freshness check).
- `extract` produces
  one JSON artifact per crate at `<DIR>/<crate>.json` (default
  `DIR = ./extracted/`) capturing source files, exports, the Lean
  program decl, formal specs, and verifications. See
  [`EXTRACT.md`](EXTRACT.md) for the full schema and the project
  conventions it relies on (`@[spec_of]`, `@[proves]`, docstring
  shape).
- `report` must be run from the project root. It runs
  `verifier extract` into `./extracted/` (override with `--extracted DIR`)
  and then builds the Astro static site bundled at `verifier/report/`
  (located relative to the verifier binary) into `./out/` (override with
  `--out DIR`). An optional crate filter narrows the extract step.
  Requires `npm` on PATH; if `verifier/report/node_modules` is missing the
  command runs `npm install` first.

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
