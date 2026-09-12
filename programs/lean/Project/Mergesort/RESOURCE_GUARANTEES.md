# Mergesort with proved memory and execution budgets

For inputs within the stated size limit, the compiled `mergesort` export returns
normally and writes the input values in sorted order, preserving duplicates.
The proof also bounds physical Wasm memory throughout execution and supplies a
numerical budget sufficient for Talos's executable runner to finish.

This is stronger than the existing total success-or-OOM contract: within this
range, allocator failure is excluded. The theorem starts from the actual named
export and the standard Universal host. Correct output and the resource bounds
refer to the same execution.

## The guarantees

Let `n` be the number of packed little-endian UInt32 input values. For
`n ≤ 89,434,754`, define:

```text
P(n) = max(17, ceil((1,049,542 + 24n) / 65,536))
W(n) = 54n ceil(log₂(n+1)) + 200n + 259 ceil(4n/256)
       + 583 + 65,536(P(n) - 17)
```

The export returns a sorted permutation, every execution prefix uses at most
`P(n)` physical Wasm pages, and the complete execution uses at most `W(n)` units
of modeled work. A Wasm page is 65,536 bytes. The machine's physical cap remains
65,536 pages; the proof constructs the permitted memory growth rather than
assuming allocation succeeds.

For example, `P(2690) = 17`: up to 2,690 words need no growth beyond the initial
seventeen pages. At 10,000 words the bound permits twenty pages. These are
conservative sufficient bounds, not maximum successful input sizes.

Work charges one unit per semantic transition, the specified bulk-memory byte
counts, actual host transfer bytes, and 65,536 bytes per newly grown page.
Because every transition costs at least one unit, `W(n)` also supplies enough
steps for the executable runner. It is not a bound on elapsed time, process RSS,
or the implementation cost of Lean's memory representation.

The theorem uses Talos's concrete Universal host. A valid read consumes the
smaller of the requested byte count and the remaining input; a valid write
appends the complete requested slice. Invalid arguments and out-of-bounds I/O
trap in this host, and the bounded execution theorem proves those outcomes are
not reached. Memory growth succeeds when the resulting page count fits the
configured cap. Arbitrary short or failing I/O and host-process allocation
failure are outside this model.

## Proof and execution interfaces

- `ExportWorkProof.named_export_work` combines initialization, normal return,
  sorted output, whole-execution work, and bounds for every prefix.
- `GrowingTotalProof.mergesort_growing_memory_correct` proves the verifier's
  registered successful-return and memory specification.
- `ExecutionBudget.run input` initializes the actual named export and executes
  it with `W(input.length)` as its step budget.
- `ExecutionBudget.run_export_sorted` proves that this execution returns the
  correct sorted output and a final store within the page bound.

The numerical theorem and runner adapter are proof-facing APIs. They are not
additional fuel-bearing public specification cards. The original partial and
total success-or-OOM specifications remain available.

## Reproduction

From the repository root, using its pinned Lean toolchain and generated Wasm/WAT:

```sh
lake -d codelib build --wfail
lake -d programs/lean build Project --wfail
python3 scripts/check-resource-guarantees.py --self-test
python3 scripts/check-resource-guarantees.py
```

On this branch the combined validator also checks the hex resource consumer.
It checks both WAT files, executes five mergesort and six hex inputs with their
proved budgets, and audits the resource theorems, both adapters and the shared
runner lemma. Every local declaration in their import closure is included,
including private helpers. Only `propext`, `Classical.choice`, and `Quot.sound`
are accepted. Its receipt records source hashes and fails if validation inputs
change during the run. Existing hex libraries retain legacy linter warnings;
the separate Project command above treats warnings as errors.

## Integration and maintenance

The exact-page resource must pass through allocation, reallocation, input
reading, and the complete driver. The shared API change and required existing
caller migration are described in
[`RESOURCE_PAGES_MIGRATION.md`](../../../../codelib/RESOURCE_PAGES_MIGRATION.md).

The program cost proofs depend on the pinned generated Wasm bodies. A compiler
or Rust source change can require updates to these proofs as well as the
functional proofs. The result establishes the stated guarantees for this
program and semantics; it does not establish compiler correctness, a timing
model, or a scalable automatic method for generating new cost proofs.
