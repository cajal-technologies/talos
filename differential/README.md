# Differential testing

Keeps the runner in parity with a trusted engine by running the same modules on
both and flagging divergences — above all **soundness** divergences, where the
runner accepts or runs a module the oracle rejects or traps on.

```bash
just differential                          # recgroup soundness mode, V8 oracle
just differential --mode recgroup -n 300   # reproduce the full #108 cluster
just differential --mode mutate --seeds differential/seeds
```

## How it works

The engine is [miscast](https://github.com/jasisz/miscast) (@jasisz), a differential
and self-checking WebAssembly GC soundness tester. `scripts/differential.sh` builds
the runner, points miscast's custom system-under-test at it, and runs it against V8.

No adapter is needed: miscast invokes a custom SUT as `CUSTOM_CMD='<cmd> {wat} {export}'`
and reads a value from stdout / a trap from a `trap:` line, which is exactly the
runner's CLI and output contract. Out-of-fuel (exit 2, empty stdout) reads as
unsupported, so it never shows up as a false divergence.

miscast is pinned as an external dependency (a rev in `scripts/differential.sh`),
not vendored. The first run clones it into `.differential-cache/` (gitignored);
set `MISCAST_DIR=/path/to/miscast` to use a local checkout instead.

## Requirements

- `wasm-tools`
- `node` ≥ 22 (the V8 / WasmGC oracle)

## Seeds

`seeds/` holds hand-checked `.wat` probes for the seed-driven modes (`mutate`,
`replay`). Each is one soundness corner, and a regression guard. They are also
runnable directly:

```bash
lake exe runner differential/seeds/recgroup_callindirect.wat go
```

traps with `indirect call type mismatch`, agreeing with V8 — the minimal form of #108,
which the runner now handles correctly. It must keep trapping.

## Known noise

The runner's Lean float formatting differs from V8's, so some `f64` results show up
as *value* (not soundness) divergences. Those are formatting noise, not bugs; the
follow-up CI gate baselines them (and the #108 recgroup cluster) so it only trips on
new divergences.
