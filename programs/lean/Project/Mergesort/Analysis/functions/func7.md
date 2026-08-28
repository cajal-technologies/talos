# Mergesort `func7` (absolute 10, `__rust_dealloc`)

No-op deallocator with parameters `(pointer, size, alignment)`.  It has no
instructions beyond return, so memory remains allocated and the bump cursor
does not move.  It is used by `func3` and multiple destructors/formatters.

The main spec consumes the complete live block whose logical pointer, size,
and alignment are tied by exact unsigned equations to the three Wasm
parameters.  Reachable alignments are one and four.  It consumes the allocation
token, preserves physical memory and cursor/frontier, marks the metadata entry
retired, and transfers the bytes once into the retired portion of `BumpHeap`.
This logical retirement is a ghost ownership update justified
by the machine no-op; it must not leave the same bytes with the caller.
Constant time and space, no failure mode.

`func3` is its only reachable caller, for values, scratch, and the current input
buffer.  Calls from panic destructors are excluded documentation.  The
contract is only usable if every container owns its complete allocation,
including spare capacity.
