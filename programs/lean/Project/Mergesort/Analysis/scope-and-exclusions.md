# Valid-input scope and exclusion obligations

Status: **frozen hard formalization boundary**.

The proof covers only functions and control-flow paths reachable from the
export under the public input and fixed-machine assumptions.  Imports 0--2 and
local functions 0--11 form the specification closure.  Local functions 12--55
are documentation-only exclusion evidence: they receive no WP specification,
no body proof, and no auxiliary contract introduced merely to traverse their
subgraph.

An excluded edge is discharged at its originating guard in the reachable
caller.  The proof at that program point must derive that the branch condition
is false from the caller's entry facts, a callee postcondition, or the current
loop invariant.  It may not assume that an error routine is benign, appeal to
the error routine's intended behavior, or prove a theorem about the excluded
callee.  If any listed guard cannot be proved false, the closure must be
reopened and reviewed before proof work continues.

## Roots of the excluded subgraph

These are the only syntactic calls from the valid-input proof closure into
functions 12--55:

The line numbers below refer to the frozen
`programs/rust/build/mergesort/program.wat` whose hash is recorded in
`target.md`.

| Obligation | Frozen WAT call | Originating guard | Excluded edge | Required local fact |
| --- | ---: | --- | --- | --- |
| `X-F1-ADD` | 136 | `func1`, checked `length + additional` | `func1 -> func43(0,0)` | exact unsigned no-wrap from `GeometricVecFacts` |
| `X-F1-TAG` | 182 | `func1`, tag returned by `func0` | `func1 -> func43(error words)` | the positive valid-layout `func0` specialization returns tag zero or terminates through `talos.oom` |
| `X-F2-SLICE` | 332 | `func2`, initial scratch-prefix check | `func2 -> func46` | `mid <= scratchLength` from equal source/scratch lengths |
| `X-F2-INDEX-1` | 299 | `func2`, left-selected main-merge destination guard | `func2 -> func49` | the main-loop invariant proves the scratch destination index in range |
| `X-F2-INDEX-2` | 305 | `func2`, right-selected main-merge destination guard | `func2 -> func49` | the main-loop invariant proves the scratch destination index in range |
| `X-F2-INDEX-3` | 471 | `func2`, left-remainder guard | `func2 -> func49` | the left-remainder invariant proves the index in range |
| `X-F2-INDEX-4` | 479 | `func2`, right-remainder guard | `func2 -> func49` | the right-remainder invariant proves the index in range |
| `X-F2-COPY` | 485 | `func2`, final copy-length comparison | `func2 -> func55` | source and scratch numeric lengths are equal |
| `X-F3-READ` | 594 | `func3`, read-count range check | `func3 -> func46` | `func10` returns `count <= 256` |
| `X-F3-VALUES-NULL` | 774 | `func3`, values allocation null check | `func3 -> func43` | normal `func5` return is nonzero; failure terminates through `talos.oom` |
| `X-F3-SCRATCH-NULL` | 779 | `func3`, scratch allocation null check | `func3 -> func43` | normal `func9` return is nonzero; failure terminates through `talos.oom` |

Once these roots are false, every direct or indirect panic, formatting,
bounds-error, generic allocation-error, abort, and unwinding function below
them is unreachable.  The decoded function cards, direct call graph, and table
map remain review evidence for that transitive classification only.

## Other irrelevant branches inside reachable functions

Some unreachable paths do not enter functions 12--55, but they are governed by
the same rule and are proved at their own guards:

- `func0`'s layout-error, zero-size dangling, realloc-zero, and allocator-null
  cases are false in its sole reachable specialization;
- `func3`'s partial-word return is false because public input uses the
  four-byte codec;
- `func3`'s post-read `0x7ffffffc` operation is not an excluded branch.  The
  proof establishes that the masked allocation size equals the full byte
  length; its following branch is the valid empty/nonempty split.  A larger
  input has already terminated through `talos.oom`; and
- the `memory.grow = -1` checks in `func5`, `func8`, and `func9` are not part of
  the excluded panic/error-support boundary.  They call the in-scope `func6 ->
  talos.oom` path, and the modular allocator specs provide that exact OOM
  continuation even when arithmetic classification succeeds.  Initial-store
  cap arithmetic can later strengthen this branch away without affecting the
  main public theorem.

These facts belong in the authoritative specifications and later body proofs
of the reachable functions.  They do not justify contracts for error-support
code.

## The `talos.oom` exception

The direct allocation-failure route

```text
func5 / func8 / func9 -> func6 -> import2 talos.oom
```

is reachable for valid, sufficiently large finite inputs.  It is therefore an
ordinary in-scope terminal path.  Its contract fixes the exact host trap reason
and raised OOM marker while preserving every resource that had not been
committed before failure.  This path is distinct from Rust's generic
allocation-error hooks (`func17`, `func18`, `func23`, `func27`, `func28`, and
`func43`--`func45`), which remain excluded.
