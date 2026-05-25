# Contributing to Talos

Thanks for your interest. This document covers how the project is structured, how to build and test it, and how to contribute.

## Architecture overview

The codebase has five main parts — described at a level that shouldn't go stale as features are added:

- **Interpreter** — the core Wasm semantics. A pure, fuel-bounded big-step interpreter; the same definitions used for execution are the ones proofs reason about.
- **Decoder** — parses `.wat` text format (and `.wasm` binaries via `wasm-tools`) into the interpreter's AST.
- **Runner** — CLI front-end that loads a module and invokes a function on supplied arguments.
- **WP theory** — weakest precondition calculus built on top of the interpreter. This is the primary reasoning layer; most proofs are written against the WP API rather than unfolding the interpreter directly.
- **Wast support** — runs the official WebAssembly spec testsuite (`.wast` files) against the interpreter to track coverage.

## Building

```bash
lake build
```

Dependencies:

- **Lean 4** — toolchain is pinned in `lean-toolchain` and fetched automatically by [`elan`](https://github.com/leanprover/elan).
- **[`wasm-tools`](https://github.com/bytecodealliance/wasm-tools)** — decodes `.wasm` binaries and drives the testsuite. Install with `brew install wasm-tools` or `cargo install wasm-tools`.

## Running the Wasm spec testsuite

```bash
just testsuite
```

Filter to a specific `.wast` file by passing a substring of its name:

```bash
just testsuite i32
```

The testsuite is the primary signal for interpreter coverage. **If you want to extend the project, increasing testsuite coverage is the best place to start.** Pick a failing test, trace why it fails, implement the missing feature or fix the bug, and verify the test now passes.

## Contributing code

Pull requests are welcome. A few guidelines:

**Own your PR.** If you used AI tooling to write or review code, say so in the PR description. The human author is still fully accountable — you should understand every line, be prepared to answer questions, and be ready to address review feedback. Reviewers have the same responsibility: don't approve what you don't understand.

**Keep PRs focused.** One logical change per PR. A new instruction, a bug fix, a proof — not all three. Easier to review, easier to revert if something goes wrong.

**Proofs over tests.** Where a behavioral claim can be stated as a Lean theorem, prefer that over an ad-hoc test. The testsuite covers interpreter correctness at the spec level; theorems cover semantic properties of specific programs.

**Prefer clarity over cleverness.** The interpreter is intentionally simple so proofs stay tractable. Don't introduce complexity in the interpreter for performance reasons; if you need a faster path, prove it equivalent to the reference interpreter and keep them separate.

## Good starting points

Not sure where to begin? Here are some directions that tend to produce useful contributions:

**Write a missing example.** `interpreter/Interpreter/Wasm/Examples/` contains hand-built modules with Lean proofs. As the interpreter grows, some behaviors don't have a corresponding example yet — a small program that exercises a specific instruction or control-flow pattern, paired with a proof that it does what you expect, is a self-contained contribution. `Factorial.lean` is the reference for what a complete example looks like.

**Find an interpreter bug via an example.** Write a small Wasm program that exercises today's supported features and prove something about it. If the proof fails because the interpreter behaves unexpectedly, that's a real bug. Reporting it with a minimal reproducer is a valuable contribution on its own; fixing it is even better.

**Extend the spec testsuite coverage.** Run `just testsuite`, find a failing test, trace why it fails, implement the missing piece, and verify the test passes. This is the fastest feedback loop for interpreter work.

**Add a Rust crate to `programs/`.** The `programs/` package contains Rust crates compiled to Wasm with Lean proofs of their behavior. Adding a new crate with a spec and at least one proof is welcome. **Open a GitHub issue describing the crate and the property you intend to prove before starting** — this avoids duplicated effort and lets us flag any concerns early.

**Contribute to `codelib/`.** The `codelib/` package holds lifting lemmas and reasoning helpers shared across programs. New lemmas are welcome if they are general enough to be useful in more than one place and are accompanied by at least one use site. A lemma without a consumer will not be accepted.

**Quality-of-life improvements.** Better CI feedback, new `just` recipes, editor setup documentation, improved error messages — anything that makes the repository easier to work with is fair game. When in doubt, open an issue first to check it's worth the effort.

## Code of conduct

This is a collaborative project in a public space. Treat everyone respectfully — no harassment, no personal attacks, no dismissiveness toward newcomers or non-native speakers. Disagreement about code or design is fine and expected; make it about the ideas, not the people. If something feels off, reach out to a maintainer.
