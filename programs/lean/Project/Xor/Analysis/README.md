# Xor Wasm analysis

Function filenames use module-local Lean indices.  Add three to obtain the
absolute WAT index; imports 0--2 are `stdio.read`, `stdio.write`, and
`talos.oom`.
Symbol names were recovered from the matching unstripped Cargo artifact
`target/wasm32-unknown-unknown/release/xor.wasm`.

## Module state

- Initial memory: 17 pages (`[0, 1114112)`).
- Mutable global 0: shadow-stack pointer, initially `1048576`.
- Memory word `1048576`: monotone allocation cursor; zero selects heap base.
- Heap base `1048592`; data end `1048585`.
- Table slot 1 contains absolute function 13 (`func10`).
- Public export `xor`: absolute function 4 (`func1`).

## Direct call graph

```text
func1 public export
`- func0 implementation
   |- func2 no-allocation-shim marker (operationally no-op)
   |- func3 bump allocator
   |  `- func4 terminal OOM shim -> talos.oom
   |- func6 read shim -> stdio.read       (loop)
   |- func7 write shim -> stdio.write
   |- func5 deallocator (no-op)
   `- func13 allocation-failure path
      `- func11 -> func12 -> func8 -> func9 -> indirect handler

func10 is the installed default allocation-error handler.
```

The well-formed two-byte input path allocates two bytes.  The concrete
Universal/StdIO host fills both in one read because it returns the largest
available prefix up to capacity.  The code writes their XOR from one byte in
the shadow-stack frame and returns.  Empty or prematurely exhausted input
returns with no output, but that behavior is outside the public precondition.
The allocation-failure paths are unreachable for this fixed initial state.

## Proof-planning consequences

`func0` requires the only nontrivial loop invariant in this program.  It should
track the consumed input prefix, `filled`, and the initialized prefix of the
two-byte allocation.  The final adequacy bridge should depend solely on
`func1`'s main contract; the export wrapper then uses `func0`'s contract rather
than unfolding it.

## Complexity

For the well-formed two-byte input, execution is constant-time and uses a
two-byte heap allocation plus a fixed 16-byte shadow-stack frame.  On arbitrary
input, this concrete host causes at most two reads: one maximal nonempty read
and, only when fewer than two bytes existed, one zero-count read.
