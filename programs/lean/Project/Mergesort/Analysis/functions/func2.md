# Mergesort `func2` (absolute 5, `mergesort::mergesort`)

## Interface

Parameters are `(source, sourceLength, scratch, scratchLength)`, with lengths
in `u32` elements.  Implicit input is ownership of disjoint, in-bounds,
nonwrapping little-endian `u32` arrays.  The numeric i32 lengths must equal the
logical list lengths; equal source/scratch length is a precondition, not an
inference from memory ownership.

No global or host state is mutated.  The function does not move the shadow
stack pointer.  It mutates both caller-owned arrays and otherwise frames the
runtime module, instance, host state, globals, and caller continuation.

## Algorithm

For length below two it returns unchanged.  Otherwise:

```text
mid := sourceLength / 2
require scratchLength >= mid
func2(source, mid, scratch, mid)
func2(source+4*mid, sourceLength-mid,
      scratch+4*mid, scratchLength-mid)
merge sorted source halves into scratch
copy remaining left or right suffix
require sourceLength == scratchLength
memory.copy(source, scratch, 4*sourceLength)
```

The main merge loop tracks source-left index, right-relative index, scratch
output index, right-base pointer, and scratch cursor.  It uses unsigned i32
comparison, exactly matching `UInt32` order, and chooses the left element on
equality.

The nine generated locals after the four parameters have stable phase roles:
`mid`, output count, right-source base, right length, scratch cursor, left
index, right-relative index, and the two currently loaded values.  Some are
reused in remainder loops, so the contract exposes none of them; loop
invariants give their semantic interpretation at each program point.

The recursive measure is `sourceLength`.  Both calls use strictly smaller
lengths when `sourceLength >= 2`: `mid=floor(n/2)` and `n-mid`.  Main and
remainder loops advance an output or input index on every back edge.

## Panic-only branches

Calls to `func46`, `func49`, and `func55` report invalid slice bounds,
destination indices, or unequal copy lengths.  Equal-length valid disjoint
arrays prove the initial slice and final length checks unreachable; the four
index-failure sites additionally require the merge/remainder loop invariants.
They cannot be removed from the body-side audit merely from the entry
precondition.

The originating guard obligations are now fixed as follows.  For
`n >= 2`, `mid=n/2` satisfies `0 < mid < n`; equal buffer lengths therefore
make the initial `scratchLength < mid` edge false.  At the main-loop head the
invariant is

```text
0 <= i < mid <= j < n
k = i + (j-mid)
scratch.length = n
```

so both loads and the selected store at `k` are in bounds.  If the left half
is exhausted, `i=mid` and hence `k=j`; copying the right suffix advances both
indices together until `n`.  If the right half is exhausted, `j=n` and
`k=i+(n-mid)`; the remaining left count is `mid-i`, so the final output index
is exactly `n`.  These two equations discharge the two remainder-copy bounds
edges.  Finally, entry equality gives `sourceLength=scratchLength`, excluding
the copy-length edge.  `WordSlice` no-wrap supplies exactness of every
generated `index << 2`, pointer addition, and final `4*n` byte count.

## Exact postcondition and complexity

There exists `output` such that source contains `output` and
`SortedPermutation originalSource output`.  For length at most one,
`output=originalSource` and scratch is unchanged; for larger length, scratch
also contains `output`.
Time is `Theta(n log n)`, recursion depth `Theta(log n)`, and each nontrivial
call performs one linear merge and one linear final copy.  This function's
main WP contract should be the sole implementation proof used at recursive and
entry call sites.

## Call-site preparation

The first recursive call receives the left prefixes and frames both right
suffixes.  The second receives the right suffixes after recombining the sorted
left prefixes.  The driver calls with separately allocated source and zeroed
scratch blocks of identical size.  `SortBuffers` therefore needs exact
split-at-mid and recombination laws, plus pointer-addition/no-wrap facts.

## Contract audit status

The authoritative statement is frozen.  `SortBuffers_append` prepares and
reassembles both recursive calls while retaining full-range disjointness;
`SortBuffers_copyFocus` supports each loop load/store; and
`SortBuffers_copyBackFocus` exposes the exact final `memory.copy` and reseals
both arrays as the output.  The retained older body theorem proves only scratch
length at its outer interface even though an inner proof point reconstructs
the exact contents; it is evidence, not the authoritative theorem, and must be
rebased onto this stronger frozen contract before being used.
