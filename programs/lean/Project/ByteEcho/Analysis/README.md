# ByteEcho Wasm analysis

This directory records the analysis of the exact binary consumed by
`Program.lean`.  Function numbers in filenames are Lean module-local indices;
the corresponding absolute WAT index is always three larger because the module
has the imports `stdio.read`, `stdio.write`, and `talos.oom` at indices 0--2.
The symbol names below were recovered from the unstripped Cargo artifact
`target/wasm32-unknown-unknown/release/byte_echo.wasm`; its code section agrees
with the stripped verification binary.

## Module state

- Initial memory: 17 pages, covering byte addresses `[0, 1114112)`.
- Mutable global 0: shadow-stack pointer, initially `1048576`.
- Memory word at `1048576`: bump-allocation cursor; zero means use heap base.
- Heap base: `1048592`.
- Data end: `1048585`.
- Table: two entries; only absolute function 12 is installed, at slot 1.
- Public export `byte_echo`: absolute function 3, local function 0.

## Direct call graph

```text
func0 entry
|- func1 no-allocation-shim marker (operationally no-op)
|- func2 bump allocator
|  `- func3 terminal OOM shim -> talos.oom
|- func5 read shim -> stdio.read
|- func6 write shim -> stdio.write
|- func4 deallocator (no-op)
`- func12 allocation-failure path
   `- func10 -> func11 -> func7 -> func8 -> indirect allocation-error handler

func9 is the installed default allocation-error handler.
```

The intended singleton-input execution uses `func0`, `func1`, `func2`,
`func4`, `func5`, and `func6`.  The OOM and allocation-error subgraphs are unreachable
when the initial allocator state is well formed and one byte fits in the
initial 17-page memory.

## Proof-planning consequences

The final development should give each function one principal WP contract.
The public adequacy theorem should use only `func0`'s contract.  `func0` in
turn should use the contracts of the allocator, host shims, and deallocator;
it should not unfold those callees a second time.

## Complexity

For the well-formed singleton input, the entry executes a constant number of
instructions, allocates one byte, performs one read and one write, and uses
constant auxiliary space.  The allocator is constant-time apart from the
abstract cost of `memory.grow`; this concrete call does not grow memory.
