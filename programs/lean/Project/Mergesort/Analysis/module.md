# Module inventory

## Imports and export

The module has three imported functions.  Therefore generated local function
`funcN` has absolute runtime index `N + 3`.

| Absolute index | Import | Type | Contract card |
| --- | --- | --- | --- |
| 0 | `stdio.read` | `(i32 length, i32 pointer) -> i32 count` | [read](imports/func0-stdio-read.md) |
| 1 | `stdio.write` | `(i32 length, i32 pointer) -> ()` | [write](imports/func1-stdio-write.md) |
| 2 | `talos.oom` | `() -> ()`, structurally trapping | [OOM](imports/func2-talos-oom.md) |

The only function export is `mergesort`, absolute index 6/local `func3`.  The
memory and immutable `__heap_base`/`__data_end` globals are also exported but
are not host inputs to the theorem.

## Runtime resources

- One table, initial and maximum size 18.
- One memory, initial size 17 pages = 1,114,112 bytes, with no declared maximum.
- Mutable global 0 is `__stack_pointer`, initially 1,048,576.
- Immutable global 1 is `__heap_base = 1,049,536`.
- Immutable global 2 is `__data_end = 1,049,525`.
- One active data segment begins at 1,048,576 and has 916 bytes.
- The allocator cursor is the i32 word at 1,049,492.  Zero means heap base.
- The allocation-error hook selector is the word at 1,049,504 and starts zero.
- Panic counters/flags occupy 1,049,496 through 1,049,524.

The stack grows down and the bump heap grows up.  The export's fixed 272-byte
frame is `[1,048,304, 1,048,576)`.  Its reserve call needs a further 16 bytes
`[1,048,288,1,048,304)`, so the entry contract owns the full 288-byte region.
Both are entirely below the data segment and heap.

## Table

Slot zero is null.  Slots 1 through 17 contain absolute functions
`26,18,41,40,45,39,38,36,37,19,35,43,42,44,34,33,57`.  In local numbering
these are `23,15,38,37,42,36,35,33,34,16,32,40,39,41,31,30,54`.
Every indirect call is type checked.  The public well-formed path performs no
indirect call; all indirect dispatch belongs to the excluded Rust panic/OOM
formatting runtime.  The Talos allocator's own failure path calls the direct
`talos.oom` import instead.

The frozen String, StaticStrPayload, and FormatStringPayload vtables at
addresses `1049112`, `1049136`, and `1049164` have been decoded into exact
method slots in [indirect-dispatch.md](indirect-dispatch.md).

## Observable structural traps

Potential traps in the binary include bounds failures, `unreachable`, invalid
indirect dispatch, host traps, and a syntactic memory-growth failure check.
Under the entry assumptions, all slice/bounds/panic edges are proved
unreachable.  The module has an effective 65536-page cap, while every allocator
end that passes its signed check needs at most 32768 pages, so its
`memory.grow = -1` edge is also unreachable in executions from the initial
store.  The modular allocator specs intentionally do not assume a state-linked
cap token; they route physical grow failure through the same exact in-scope
`talos.oom` continuation.  Arithmetic or signed-end
allocator failure is converted by `func5`, `func8`, or `func9` into the direct
`func6 -> talos.oom` path.  The proof must not silently classify arbitrary
traps as OOM.
