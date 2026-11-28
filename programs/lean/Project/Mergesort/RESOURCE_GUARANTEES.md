# Memory and work bounds for the compiled mergesort

On the Talos Universal host, the named `mergesort` export returns normally for
every list of at most 89,434,754 packed little-endian UInt32 words. It writes
the words in nondecreasing order and preserves duplicates.

For an input of `n` words, let `P(n)` count physical Wasm pages and `W(n)`
count units of modeled work.

```text
P(n) = max(17, ceil((1,049,542 + 24n) / 65,536))
W(n) = 54n ceil(log₂(n + 1)) + 200n + 259 ceil(4n / 256)
       + 583 + 65,536 (P(n) − 17)
```

Every execution prefix uses at most `P(n)` pages and costs at most `W(n)`.
Up to 2,690 words fit within the initial 17 pages. The work model charges one
unit per semantic transition, plus bytes copied or filled by bulk instructions,
bytes transferred through standard I/O, and 65,536 units per new page.
Elapsed time and host-process memory are outside the model.

## Proof and runner

- `GrowingTotalProof.mergesort_growing_memory_correct` proves the registered
  normal-return and all-prefix memory specification.
- `ExportWorkProof.named_export_work` proves sorted output and the work bound
  for the same execution, binding the initial state to the actual export name.
- `ExecutionBudget.run` executes that export with `W(n)` steps.
  `ExecutionBudget.run_export_sorted` proves the budget suffices and gives the
  sorted output and page bound on the store returned by the runner.

## Verification

Generate the Wasm artifacts using the repository's normal program build.
From the repository root, run the proof builds, the five executable regressions,
and the package-wide axiom audits.

```sh
(cd codelib && lake build --wfail)
(cd programs/lean && lake build Project --wfail)
(cd programs/lean && lake env lean --run ../../scripts/check-mergesort-budget.lean)
reports=$(mktemp -d)
for package in interpreter codelib verifier programs/lean; do
  python3 scripts/axiom-audit.py "$package" --report "$reports/${package##*/}.json" || exit 1
done
```

The regression checks compare the generated Wasm text with the embedded module
and exercise empty input, a singleton, unsorted input, duplicates, and unsigned
boundary values using the proved budget.
