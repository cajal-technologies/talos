# Xor `func0` (absolute function 3, `xor::xor`)

## Role

Internal implementation of the exported XOR program.

## Interface

- Explicit parameters/results: none.
- Implicit inputs: shadow stack, allocator, linear memory, standard-input and
  output state.
- Successful output: no Wasm values; either no host output for incomplete
  input or one byte equal to the XOR of the first two consumed bytes.

## Low-level state

- Local 0: 16-byte shadow-stack frame base.
- Local 1: heap pointer returned for the two-byte input buffer.
- Local 2: `filled`, number of bytes read so far.
- Local 3: count returned by the latest read.
- Stack-frame byte at offset 15: one-byte XOR output buffer.

## Calls and control flow

```text
sp := global0 - 16; global0 := sp
func2()
ptr := func3(size = 2, align = 1)
if ptr == 0:
  func13(1, 2); trap
filled := 0
store16(ptr, 0)
while filled < 2:
  count := func6(ptr + filled, 2 - filled)
  if count == 0:
    func5(ptr, 2, 1)
    restore global0
    return
  filled := filled + count
sp[15] := load8(ptr + 1) XOR load8(ptr)
func7(sp + 15, 1)
func5(ptr, 2, 1)
restore global0
return
```

The host read contract guarantees `count <= 2 - filled`; consequently the
addition cannot overshoot two.  The concrete Universal/StdIO host returns the
maximal available prefix.  Thus input length zero gives one zero-count read,
length one gives a one-byte read followed by a zero-count read, and length at
least two gives one two-byte read.

## Well-formed public path

For exactly two input bytes, the read loop eventually has `filled = 2`; the
zero-count early-return branch is unreachable before completion.  The fixed
two-byte allocation fits without memory growth, so the null and OOM branches
are also unreachable.

## Contract ingredients

The loop invariant should expose a high-level two-byte buffer predicate split
at `filled`, relate the initialized prefix to the consumed host prefix, and
retain writable ownership of the suffix.  The main contract should assume the
well-formed exact two-byte input and use it to eliminate the EOF,
null-allocation, and OOM branches.  Incomplete-input behavior is an optional
regression result rather than part of the principal contract.

## Complexity

Constant time and space for the fixed buffer; exactly one host read and one
host write on the well-formed path.
