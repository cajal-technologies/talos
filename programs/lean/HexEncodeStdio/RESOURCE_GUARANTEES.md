# Hex encoding with proved memory and execution budgets

For every input of at most 357,738,263 bytes, the compiled `encode` export
returns normally and writes the exact lowercase hexadecimal encoding. The
same execution has an explicit numerical work budget, and physical Wasm memory
stays within its page bound throughout execution.

This is the second consumer of the shared resource APIs. Its runner adapter
uses the same sufficient-budget lemma as mergesort; neither adapter requires
a separate execution semantics.

## Bounds and assumptions

For `n` input bytes:

```text
P(n) = max(17, ceil((1,054,064 + 4n + max(8, 2n)) / 65,536))
W(n) = 675n + 1234 + 65,536(P(n) - 17)
```

Every execution prefix uses between seventeen and `P(n)` Wasm pages. Every
costed prefix uses at most `W(n)` work units, and the complete execution
returns the correct output within that budget. For at most 10,008 input bytes,
the page bound remains seventeen. These are conservative sufficient bounds;
they do not characterize the largest successful input or the exact point
where the program first grows memory.

The theorem starts the actual named export using the Universal host. A valid
read consumes the smaller of the requested length and the remaining input;
a valid write appends the entire requested slice. The proof excludes traps
within the input-size condition. Growth follows Talos's deterministic memory
rule under the unchanged physical cap of 65,536 pages.

Work charges semantic transitions, bulk-memory bytes, actual host transfer
bytes and newly added physical bytes. It supplies a sufficient step budget for
Talos's runner. It is not elapsed time, host-process memory, arbitrary I/O
behavior or a guarantee that the operating system can allocate the modeled
memory. Rust/compiler changes can require updates to the generated-body proofs.

## Interfaces

- `Project.HexEncodeStdio.ResourceProof.named_export_resources` combines
  initialization, correct output, normal return, and every-prefix bounds.
- `Project.HexEncodeStdio.ExecutionBudget.run` executes the actual named export
  using the numerical work bound.
- `Project.HexEncodeStdio.ExecutionBudget.run_export_encoded` proves that the
  runner returns exactly the encoded output with the final page bounds.
- `Wasm.SmallStep.runSteps_result_of_steps_le` is the shared bridge from a
  relational execution prefix to an executable runner with sufficient budget.

The verifier displays two semantic contracts: `Project.HexStdio.Spec.EncodeSpec`
retains total success-or-OOM correctness for every input; `EncodeMemorySpec`
guarantees normal output and every-prefix physical-memory bounds for the
bounded input domain. `Project.HexStdio.Proof` registers their checked proofs
where the extractor discovers them. Numerical work and runner budgets remain
in the Lean proof APIs; neither public contract mentions fuel.

## Reproduction

From the repository root with its pinned toolchain and generated Wasm/WAT:

```sh
lake -d codelib build --wfail
lake -d programs/lean build Project --wfail
python3 scripts/check-resource-guarantees.py --self-test
python3 scripts/check-resource-guarantees.py
```

The combined validator builds both resource consumers and both existing hex
libraries, checks both WAT files against the imported modules, executes five
mergesort and six hex inputs with their proved budgets, and audits every local
declaration in the required import closure. The hex cases include empty input,
byte boundaries, mixed nibbles, and inputs crossing a 256-byte read boundary;
literal expected encodings are checked alongside the existing specification.

The complete audit includes private helpers and accepts only standard Lean
axioms. Receipts record source identities and reject changes during validation.
Existing hex libraries retain legacy linter warnings; the separate Project
command above treats warnings as errors.
