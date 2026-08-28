# ByteEcho `func2` (absolute function 5, `__rust_alloc`)

## Role

Monotone bump allocator with optional memory growth.

## Interface

- Parameter 0: requested size in bytes.
- Parameter 1: power-of-two alignment.
- Result: aligned start address.
- Implicit state: cursor word at address `1048576`, heap base `1048592`,
  current memory size, and the `talos.oom` host operation.

## Low-level behavior

It computes `mask = align - 1`, chooses `base = cursor` unless the cursor is
zero (then `base = 1048592`), and computes
`start = (base + mask) & -align` and `end = start + size`.  Unsigned overflow
in alignment/end arithmetic or `end >= 2^31` goes to OOM.  Otherwise it rounds
`end` up to pages.  If needed it grows memory; failed growth also goes to OOM.
On success it stores `end` at address `1048576` and returns `start`.

```text
mask := align - 1
base := cursor == 0 ? heapBase : cursor
checkedBase := base + mask
start := checkedBase & -align
end := start + size
requiredPages := (end + 65535) >> 16
if arithmetic invalid or end >= 2^31: func3(); trap
if requiredPages > memory.size:
  if memory.grow(requiredPages - memory.size) == -1: func3(); trap
cursor := end
return start
```

## Call sites

`func0` calls it with `(size = 1, align = 1)`.  Under the initial module state
this returns `1048592`, stores `1048593` as the cursor, and does not grow
memory.

## Contract ingredients

The main contract must cover both successful allocation and the exact terminal
OOM outcome, while exposing a high-level allocated-region predicate rather
than a raw byte list.  Alignment validity, arithmetic bounds, cursor
monotonicity, disjointness from prior allocations, and memory-growth effects
belong in this contract and nowhere in callers.
