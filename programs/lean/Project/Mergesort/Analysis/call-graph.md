# Call graph and proof closure

## Direct calls

Numbers below are generated local indices; `import0`/`import1`/`import2` are
read, write, and OOM respectively.  Repeated syntactic call sites are shown in
the function cards even when this adjacency list deduplicates the edge.

```text
0  -> 8, 4, 5
1  -> 43, 0
2  -> 2, 49, 46, 55
3  -> 10, 1, 46, 4, 5, 9, 7, 43, 2, 11
4  ->
5  -> 6
6  -> import2
7  ->
8  -> 6
9  -> 6
10 -> import0
11 -> import1
12 -> 25
13 -> 43, 21
14 -> 7
15 -> 7
16 -> 7
17 -> 18
18 -> indirect(type 0)
19 -> 20
20 -> 22
21 -> 8, 4, 5
22 -> 29, indirect(type 0), 14, 24
23 ->
24 -> 12
25 ->
26 -> 19
27 -> 28
28 -> 17
29 ->
30 ->
31 ->
32 -> 53, 48
33 ->
34 ->
35 -> 4, 5, 44
36 -> 53
37 -> 13
38 -> 13
39 -> 48
40 -> 48, 4, 5, 44
41 ->
42 -> 48
43 -> 44, 45
44 -> 27
45 -> 47
46 -> 47
47 -> 26
48 -> indirect(types 1 and 2)
49 -> 47
50 -> 51, 52, indirect(types 1 and 2)
51 ->
52 -> indirect(types 1 and 2)
53 -> indirect(type 1)
54 -> 50
55 -> 47
```

## Public well-formed closure

The semantic proof closure is deliberately smaller than the syntactic closure:

```text
3 driver
|- 10 read -> import0
|- 1 reserve -> 0 finish-grow -> 8 realloc / 4 marker + 5 alloc
|- 5 alloc -> 6 -> import2 on failure
|- 9 alloc-zeroed -> 6 -> import2 on failure
|- 2 recursive sort
|- 11 write -> import1
`- 7 no-op dealloc
```

Calls from `2`/`3` to `46`, `49`, `55`, and `43` are proof obligations, not
callee dependencies: the caller invariant must prove their guards false.
Consequently functions 12--55 need accurate documentation and incoming-edge
classification only.  They receive no WP specifications and their bodies are
not unfolded or proved.  The direct `func6 -> talos.oom` path remains in the
closure because it is a valid terminal outcome.

## Completed proof order

The implementation followed the reviewed dependency order:

1. dossiers, representations, authoritative contracts, and the reachable
   call-site matrix were frozen for imports 0--2 and funcs0--11;
2. the exact-outcome adequacy and allocator ownership infrastructure was
   implemented against those contracts;
3. imports 0--2 and shims 10, 11, and 6 were proved;
4. allocation marker/deallocator 4 and 7, followed by allocators 5, 8, and 9,
   were proved;
5. RawVec grow/reserve 0 and 1 were proved compositionally;
6. recursive sort 2 was proved once and reused through `Func2Spec`; and
7. driver 3 was proved from its callee contracts, then
   `Proof.mergesort_correct` derived the public specification exclusively via
   `entry_adequacy_of_func3`.

The allocator interface was handled first because it was the highest-risk
dependency and is used by both the read loop and the values/scratch setup.
