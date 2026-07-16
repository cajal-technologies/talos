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
runner's CLI and output contract — including uncaught exceptions (reported as a
`trap:` line, matching V8's classification) and float arguments (the WAT literal
grammar, the same values V8 sees). Out-of-fuel (exit 2, empty stdout) reads as
unsupported, so it never shows up as a false divergence.

(miscast also ships `tools/talos_run.py`, an adapter written before the runner
spoke this contract natively; driving the runner directly keeps the verdict
mapping in one place instead of two.)

miscast is pinned as an external dependency (a rev in `scripts/differential.sh`),
not vendored. The first run clones it into `.differential-cache/` (gitignored);
set `MISCAST_DIR=/path/to/miscast` to use a local checkout instead.

## Requirements

- `wasm-tools`
- `python3` and `git` (fetching and driving miscast)
- `node` ≥ 22 (the V8 / WasmGC oracle) — found on `PATH` or under `~/.nvm`;
  override with `NODE=/path/to/node`

## Seeds

`seeds/` holds hand-checked `.wat` probes for the seed-driven modes (`mutate`,
`replay`). Each is one soundness corner, and a regression guard. **Every seed
must export its entry point as `f`** — miscast drives a bare `.wat` through the
export named `f` (the convention its own seed corpus follows); any other name
makes the seed-driven modes silently skip the module. Seeds are also runnable
directly:

```bash
cd interpreter && lake exe runner ../differential/seeds/recgroup_callindirect.wat f
```

traps with `indirect call type mismatch`, agreeing with V8 — the minimal form of #108,
which the runner now handles correctly. It must keep trapping.

## Known noise

The runner's Lean float formatting differs from V8's, so some `f64` results show up
as *value* (not soundness) divergences. Those are formatting noise, not bugs; the
follow-up CI gate baselines them (and the #108 recgroup cluster) so it only trips on
new divergences.
