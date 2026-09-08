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
`trap:` line, matching V8's classification). Invoke arguments are i32/i64 only —
miscast skips float- and ref-arg actions upstream — and the runner reads them as
plain integers, exactly as V8 does. Out-of-fuel (exit 2, empty stdout) reads as
unsupported, so it never shows up as a false divergence.

(miscast also ships `tools/talos_run.py`, an adapter written before the runner
spoke this contract natively; driving the runner directly keeps the verdict
mapping in one place instead of two.)

The contract is enforced, not assumed: every run starts with **canaries** that
probe the runner's actual output against miscast's own classification regexes —
an arg-count complaint must not read as validator rejection (that would record
false REJECT agreement on invalid modules), an uncaught exception must read as
a trap, and a garbage float argument must fail the run rather than parse as
`0.0`. A reworded runner error message that breaks the coupling fails the run
immediately instead of silently skewing verdicts.

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
makes the seed-driven modes silently skip the module. `scripts/differential.sh`
lints the corpus for this on every run, so a wrongly named seed fails loudly.
Seeds are also runnable directly:

```bash
cd interpreter && lake exe runner ../differential/seeds/recgroup_callindirect.wat f
```

traps with `indirect call type mismatch`, agreeing with V8 — the minimal form of #108,
which the runner now handles correctly. It must keep trapping.

## Known noise

The runner's Lean float formatting differs from V8's, so `f64` results *can* show
up as *value* (not soundness) divergences in modes that compare results as text.
Note that earlier sweeps predate two fixes on this branch — float CLI args used to
be read as raw bit patterns, and garbage float literals used to parse as `0.0` —
both of which manufactured exactly this kind of value divergence. The CI gate
below uses a fresh baseline and the pinned seed loader's float-result bitcast
wrappers where supported. It adds no float tolerance or blanket float exclusion.

## CI regression gate

```bash
just differential-ci
# Subsequent local runs use a new output directory:
just differential-ci --output .differential-cache/check-2
```

The `Differential testing` workflow runs this on pull requests, pushes to `main`,
and manual dispatch. It pins Node to **24.13.0**, wasm-tools to **1.251.0**, and
uses the existing miscast and Lean pins. Four workers execute a finite corpus:

- miscast's complete `all -n 300` generated GC suite and invalid-module battery;
- all 300 `recgroup` cases, including the #108 indirect-call soundness regression;
- every seed in Talos and in the pinned miscast checkout;
- every type mutation of the Talos seeds, routed to execution or validation.

V8 runs with `--experimental-wasm-exnref` for both execution and validation;
Node 24.13.0 otherwise rejects the exception-reference cases before comparing
them. The flag is recorded with the tool versions and included in replays.

These generators use fixed case indices; the random `smith` mode is outside the
gate. Seeds must be standalone `.wat` modules; stateful `.wast` scripts belong
in the separate conformance harness. Every subprocess has a 20-second timeout,
including the shell harness's
contract canaries. The comparison step has a 10-minute limit; the job allows
60 minutes including the cold Lean build.

`baseline.json` records the tool versions, a count and hash of the complete case
inputs, and any individually explained exceptions. The gate fails on a new or
changed disagreement, lost coverage, tool drift, or a stale exception. A fixed
exception must be removed so it cannot later hide the same regression. Existing
semantic disagreements are recorded individually, as proposed in
[#152](https://github.com/cajal-technologies/talos/pull/152); every new
or changed soundness failure fails the gate. Crashes, timeouts, and unreadable
numeric comparisons cannot be waived.
Unsupported cases and oracle disagreements remain visible as coverage gaps;
they are never counted as agreement. A self-checking expected value cannot
substitute for a missing V8 result in this gate.

The implementation calls miscast's generators, execution functions and verdict
classifier directly. Its small observer wraps the pinned subprocess helper to
enable V8 exception references, retain raw output, and distinguish host crashes
and timeouts from unsupported operations. Review
that API boundary when changing the miscast revision.

### Initial baseline

The baseline was measured with a freshly built runner at Talos
`78f9d08d46bcda1e4ddf794a697a18cccc59ba0f`, using the versions and V8 flag above.
It covers **620 cases**: 194 generated `all` cases, 300 `recgroup` cases, 38
invalid modules, one Talos seed and its 70 mutations, and 17 upstream seeds.

| Outcome | Cases | Observed behavior |
| --- | ---: | --- |
| Agreement | 556 | Matching values, traps, or validation rejection |
| `SOUNDNESS` | 27 | 26 invalid-module acceptances and one subtype-depth implementation-limit disagreement |
| `completeness` | 10 | Element-segment probes trap with out-of-bounds table access in Talos |
| `sut-reject` | 22 | Decoder rejects named data segments or a table declaration accepted by V8 |
| `sut-unsup` | 5 | Invalid modules exit with diagnostics the validation classifier cannot recognize |

Every non-agreement has an exact case ID, engine outcome, and explanation in
`baseline.json`. These are existing findings, not a claim of full conformance.
There are no missing V8 results, wrong-value findings, host crashes, or timeouts
in this initial baseline. The subtype-depth probe is an implementation-limit
comparison; its `SOUNDNESS` label comes from miscast and does not establish a
WebAssembly specification violation.

### Failure artifacts

CI uploads `.differential-cache/ci/` even when the comparison fails:

- `summary.md` and `report.json`: counts, exact per-case verdicts, tool versions,
  commands, exit codes, stdout and stderr;
- `results.jsonl`: flushed after each case, retaining partial results if the job
  is interrupted;
- `repro/<case-hash>/`: the input Wasm text, assembled binary when available, and
  `replay.sh` for every non-agreement;
- `baseline-candidate.json`: an observation for review, never an automatic update.

After downloading the artifact, a case can be replayed with the pinned tools:

```bash
bash repro/<case-hash>/replay.sh /absolute/path/to/talos/interpreter/.lake/build/bin/runner
```

The replay script uses the included V8 oracle and local module files; it does
not depend on paths from the original CI machine. Validation cases replay V8's
validation operation and Talos's existing invoke-based validation probe.

### Intentional baseline changes

For a tool or corpus change, run the full gate in record mode:

```bash
just differential-ci --record --output .differential-cache/baseline-review
```

Inspect `report.json` and replay disagreements before copying the candidate to
`differential/baseline.json`. Every exception requires a specific `reason`; an
unreviewed candidate fails the normal gate. Commit the tool/corpus change and
reviewed baseline together. Record mode does not certify a passing comparison.

The policy tests run without Lean or miscast:

```bash
python3 -m unittest discover -s scripts/tests -p 'test_differential_ci.py' -v
```

With the runner built and pinned miscast fetched, enable the real-engine checks:

```bash
TALOS_DIFFERENTIAL_INTEGRATION=1 python3 -m unittest discover -s scripts/tests -p 'test_differential_ci.py' -v
```

These inject incorrect values, a crash and a timeout into the SUT process while
retaining the real V8 oracle. They also check the #108 trap regression, distinct
identities for equally named mutations, and replaying an artifact from a different
directory. The workflow runs both sets of checks.
