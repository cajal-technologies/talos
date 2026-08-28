# Well-formedness and environment assumptions

## Public caller assumption

The public input is an arbitrary finite `List UInt32`.  Its byte stream is the
canonical packed little-endian serialization, so its length is exactly four
times the list length.  This is not a size bound: for every finite execution
that reaches an observable terminal outcome, the theorem classifies that
outcome as normal sorted return or exact OOM.  It does not prove that execution
terminates, including for very large finite inputs.

## Fixed initial machine

- The module, memory, globals, table, data segment, and host registry are the
  exact frozen artifacts in [target.md](target.md).
- The initial stack pointer is 1,048,576 and the export takes no arguments.
- The bump cursor word starts zero, selecting heap base 1,049,536.
- Universal host input is the serialized public input; output is empty and its
  OOM flag is false.
- Execution is single-threaded and the small-step semantics is deterministic.

## Host assumptions proved from Universal

- `stdio.read(length,pointer)` returns exactly the length of the remaining
  input prefix of size at most `length`, writes that prefix in bounds, removes
  it from input, and preserves output.
- `stdio.write(length,pointer)` appends exactly the in-bounds memory slice and
  preserves input.
- `talos.oom()` sets `oom.raised = true` and returns a structural host trap with
  reason `OOM.trapMessage`.

These are consequences of the concrete Universal host implementation, not
axioms supplied by the public caller.

## Internal representation obligations

- The 272-byte export frame plus the 16-byte reserve frame immediately below it
  are in bounds, nonwrapping, and disjoint from static data and all bump
  allocations.
- Every allocator alignment on the public path is one or four, hence nonzero
  and a power of two.
- Live bump allocations are aligned, nonwrapping, below the signed-address
  limit, pairwise disjoint, and below the cursor.  Deallocation does not reclaim
  them; discarded blocks become retired history.
- The Vec header satisfies `length <= capacity`; its initialized prefix is
  owned and spare capacity is distinct from logical contents.
- Sort source and scratch have equal lengths, four-byte alignment, nonwrapping
  byte ranges, in-bounds ownership, and are disjoint.

## Excluded paths and required proofs

- Read count above 256 is impossible by the read contract.
- A trailing partial word is impossible because public input is serialized
  `UInt32` data.
- Every sort slice/bounds/copy-length panic is impossible from `SortBuffers`.
- Generic post-allocation null checks are impossible because the Talos
  allocator returns a pointer or traps through `func6`; it never returns zero
  as an allocation-failure result.
- Capacity overflow is not merely assumed away.  For the geometric input Vec,
  cumulative retained allocations make the bump cursor hit the allocator's
  signed-address failure before a later RawVec capacity-overflow request.  This
  arithmetic lemma is required for the exhaustive success/OOM theorem.
- A normally completed read loop has `byteLength < 2^31`; combined with the
  codec's divisibility by four, this gives the implementation equation
  `byteLength & 0x7ffffffc = byteLength`.  The signed bound follows from the
  geometric lineage because a larger input reaches OOM first.  Neither fact
  alone is sufficient.
- The module's effective memory cap is 65536 pages.  Any allocator end that
  passes `end < 2^31` requires at most 32768 pages, so executions from the
  frozen initial store cannot fail growth.  The modular function specs do not
  own instantiated cap metadata and therefore accept `memory.grow = -1` as a
  second route to the same in-scope exact `talos.oom` outcome.

No proof may replace one of these obligations with an informal statement that
the branch is unlikely or irrelevant.
