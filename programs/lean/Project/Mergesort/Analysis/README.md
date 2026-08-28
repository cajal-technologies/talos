# Mergesort Wasm analysis

This directory is the review boundary for the merge-sort proof.  The following
gates have now passed for imports 0--2 and local functions 0--11:

1. every reachable-function card records the ABI inputs, owned memory and
   implicit state, outputs, mutations, control flow, call sites, failure modes,
   complexity, and assumptions making excluded branches unreachable; cards for
   functions 12--55 need only document bodies and incoming edges sufficiently
   to justify their exclusion at reachable caller guards;
2. every function in the public proof closure has exactly one authoritative WP
   specification stated against the shared high-level predicates; and
3. each specification has passed a two-sided review: it is strong enough to be
   proved from the body, and every call site can establish its precondition and
   continue from every postcondition.

The authoritative statement set is frozen, and the bottom-up body proofs and
public partial-adequacy composition are complete.  The Lean proofs are stated
against these reviewed contracts rather than redefining or weakening them:
`func2`, `func4`, and the import/shim contracts are closed in
`ContractProofs`; allocators in `Func5Proof`, `Func8Proof`, and `Func9Proof`;
RawVec growth/reserve in `Func0Proof` and `Func1Proof`; the driver in
`DriverProof`; and the final composition in `Proof`.  Functions 12--55 remain
outside proof scope, with obligations discharged only at the originating
guards in reachable callers.

- [Frozen target](target.md)
- [Module inventory](module.md)
- [Function inventory and freshness](function-inventory.md)
- [Call graph](call-graph.md)
- [Valid-input scope and exclusion obligations](scope-and-exclusions.md)
- [Public-path call-site matrix](call-site-matrix.md)
- [Well-formedness assumptions](assumptions.md)
- [Input Vec growth and pre-overflow OOM analysis](capacity-growth.md)
- [Canonical representation design](representations.md)
- [Contract design](contracts.md)
- [Exact authoritative specification statements](authoritative-signatures.md)
- [Indirect table and dispatch analysis](indirect-dispatch.md)
- [Proof ledger](proof-ledger.md)
- [Terminal-outcome design decision](decisions/0001-terminal-outcomes.md)
- [Allocator ownership design decision](decisions/0002-allocator-ownership.md)

This analysis concerns the exact stripped binary loaded by `Program.lean`.
Rust symbol names were recovered from the matching unstripped Cargo artifact
`target/wasm32-unknown-unknown/release/mergesort.wasm`; code sizes, ordering,
and instructions align with `build/mergesort/program.wasm`.

There are three imports, so local Lean `funcN` is absolute Wasm function
`N + 3`.

## Module resources

- Initial memory: 17 pages = 1,114,112 bytes.
- Mutable global 0: downward-growing `__stack_pointer`, initially 1,048,576.
- Heap base: 1,049,536.
- Data end: 1,049,525.
- Bump cursor: memory word at 1,049,492; zero selects the heap base.
- Export `mergesort`: absolute function 6, local `func3`.
- Static table: slot 0 null; slots 1--17 contain allocation-error, panic,
  formatting, payload, and `u32` display functions documented individually.

## Function families

```text
func0--func1   RawVec growth/reservation
func2          recursive u32 merge sort
func3          exported streaming driver
func4--func11  allocator and stdio shims
func12--func45 Rust allocation-error/panic runtime
func46--func55 slice-panic and formatting support
```

## Public-path call graph

```text
func3 exported driver
|- func10 read shim -> stdio.read                    (read loop)
|- func1 RawVec<u8>::reserve
|  `- func0 finish_grow
|     |- func8 realloc
|     `- func5 alloc
|- func5 alloc values
|- func9 alloc_zeroed scratch
|- func2 recursive mergesort
|- func11 write shim -> stdio.write                  (output loop)
`- func7 no-op dealloc

func5/func8/func9 -> func6 -> talos.oom on failure
```

Every edge from this graph into `func43`, `func46`, `func49`, or `func55`
is a bounds/capacity/length error.  The reachable caller proves the edge false
at the originating guard.  Those callees and the runtime below them receive no
WP specification and their bodies are never unfolded in the formal proof.
The direct `func5`/`func8`/`func9 -> func6 -> talos.oom` path is different: it
is a valid terminal outcome and remains in the proof closure.

## Export frame

`func3` reserves 272 bytes below the current stack pointer:

```text
+0   input Vec<u8> capacity
+4   input Vec<u8> pointer
+8   input Vec<u8> length
+12  256-byte read buffer
+268 4-byte output-word buffer
```

## Main-path behavior

The driver reads all input in chunks of at most 256 bytes, extending a
`Vec<u8>`.  Value-level input is a multiple of four, so the invalid trailing
byte branch is unreachable.  It decodes little-endian `u32` values, allocates
an equally sized zeroed scratch array, calls `func2`, writes each sorted word,
performs no-op deallocations, and restores the stack pointer.

The driver is linear outside sorting.  For `n` words, sorting is
`Theta(n log n)`, recursion depth is `Theta(log n)`, reads number
`ceil(4*n/256)+1`, and writes number `n`.

## Very large inputs and terminal outcomes

The bump allocator never reclaims old Vec buffers.  Geometric input-Vec growth
therefore reaches the allocator's signed-address bound while attempting the
2^30-byte reallocation.  It calls `talos.oom` before RawVec can request the
later capacity that would trigger Rust's distinct capacity-overflow panic.
This fact is required to justify the public spec's exhaustive success-or-OOM
disjunction for arbitrary finite value lists.

## Intended high-level predicates

- `ByteSlice(ptr, bytes)` and `WordSlice(ptr, values)`.
- `RawVecHeader(header, capacity, ptr)` and
  `VecU8(header, capacity, ptr, initializedBytes)`.
- `SortBuffers(source, scratch, values, scratchValues)` with equal lengths,
  disjointness, alignment, and nonwrapping bounds.
- `AllocLayout(wasmSize, wasmAlign, size, align)`, allocation tokens, and a
  `BumpHeap` predicate that records cursor/frontier, authoritative allocation
  metadata, and retired blocks left by realloc/dealloc.
- `StackPointer`, one raw 288-byte entry `StackRegion`, its lower 16-byte
  `StackReserve`, and a nonoverlapping structured view of the upper 272-byte
  export region after body initialization.
- one aggregate `Streams(input, output, oom)` Universal host-state view.

These interfaces have been audited at every reachable call site and remain the
maintenance boundary for any later change.  In particular, allocator/outcome
infrastructure is downstream of the contract review: the reviewed contracts
determine what that infrastructure supports.
