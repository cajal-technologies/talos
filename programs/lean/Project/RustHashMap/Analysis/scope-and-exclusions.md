# Valid-input scope and exclusion obligations

An excluded edge is discharged at its originating guard in the reachable
caller.  The proof at that program point must derive that the branch
condition is false from the caller's entry facts, a callee
postcondition, or the current loop invariant.  It may not assume that an
error routine is benign, appeal to the error routine's intended
behavior, or prove a theorem about the excluded callee.

## How to read the table

The line numbers refer to the frozen WAT file
`programs/rust/build/rust_hash_map/program.wat`.

The column names are short. `WAT call` is the frozen WAT call.
`Guard` is the originating guard. `Edge` is the excluded edge. The
source of each edge is the absolute function in the obligation key, so
the column gives the target only. `Required fact` points into the list
below the table.

Absolute Wasm index `N` is the Lean local name `func(N-3)`.

| Obligation | WAT call | Guard | Edge | Required fact |
| --- | ---: | --- | --- | --- |
| X-D19-NULL | 4763 | 4698-4701 | -> 99 | f1 |
| X-D21-NULL | 5300 | 5220-5223 | -> 99 | f1 |
| X-D22-NULL | 5570 | 5527-5530 | -> 99 | f2 |
| X-F7-NULL | 1285 | 1117-1121 | -> 99 | f1 |
| X-F8-NULL | 1473 | 1316-1320 | -> 99 | f1 |
| X-F7-CAP | 1285 | 1084-1091 | -> 99 | f3 |
| X-F7-GROW | 1215 | 1203-1207 | -> 13 | f4 |
| X-F13-ADD | 2572 | 2563-2570 | -> 99 | f5 |
| X-F13-OOM | 2618 | 2609-2613 | -> 99 | f6 |
| X-F17-CAP | 3707 | 3678-3681 | -> 97 | f7 |
| X-F17-REHASH | 3116-3640 | 3044-3065 | in place | f8 |
| X-F16-STATE | 3002-3003 | 2990-2996 | -> 104 | f9 |
| X-F24-ORDER | 8654, 8656-8657 | 5944, 6152, 8396, 8632-8653 | -> 107 | f10 |
| X-F24-EQUAL | 5758-5976 | 5760-5771 | equal part | f11 |
| X-F24-HEAP | 5692 | 5687-5693 | -> 25 | f12 |
| X-F15-OFFSET | 2951 | 2855 | unreachable | f13 |
| X-F101-CAP | 11276 | 11265-11275 | -> 99 | f14 |
| X-F4-CAP | 818 | grow guard | -> 99 | f15 |
| X-F10-TAG | none | 1798-1800, 1822-1824 | okTag arms | f16 |
| X-TLS-DROP | 3002 | 2990-2996 | drop panic | f17 |
| X-F18-RESIZE | 4314 | 4302-4304 | -> 17 | f18 |

## Required local facts

- f1. `Func55Spec` returns a nonzero pointer. An out-of-memory result
  traps through `talos.oom` instead.
- f2. The same fact as f1. The proof `twp_reply` closes it.
- f3. `t.items <= 2 ^ 27` follows from `t.buckets <= 2 ^ 27`.
- f4. The push-loop invariant gives `len < items <= cap`.
- f5. `len + additional < 2 ^ 32` follows from the buffer bound.
- f6. This arm is live, not dead. The out-of-memory arm of `Func24Spec`
  traps through `talos.oom`.
- f7. `1 <= additional <= maxTableCapacity` from `Func14Spec`.
- f8. The table is `Table.empty` in the collect path. In the insert
  resize path the table satisfies `Clean t /\ growthLeft = 0`.
- f9. `keysBefore[16]? != some 2`, which is Part A of `Func2Spec`.
- f10. The u32 relation `<` is a strict total order. The lemma
  `bimerge_exhausts` gives the rest.
- f11. `NodupKeys` together with `AncestorBelow`. The guard compares the
  ancestor against the pivot.
- f12. This edge is live and is not excluded. `Func22Spec` proves it.
- f13. `1 <= offset <= len`, which is a precondition of `Func12Spec`.
- f14. `PushVecFacts` in `VecGrow.lean`. This fact is proved.
- f15. `CapacityFits`. This fact is proved by `44bf4f3`.
- f16. `word1 != okTag` from `Func52Spec` and `Func49Spec`.
- f17. The single-shot instance never sets the thread state to 2.
- f18. This edge is live for `map_insert`. It is dead in the collect
  path, where `1 <= growthLeft`.

## Where each row is discharged

`Func21Proof.lean` closes X-F24-EQUAL with `twp_equal_guard`.
`Func21Merge.lean` closes X-F24-ORDER with `bimerge_exhausts`.
`Func22Proof.func22_correct` proves `Func22Spec`, which carries the live
edge X-F24-HEAP. `Func4Proof.lean` closes X-F7-CAP, X-F7-GROW and
X-F7-NULL. `Func5Proof.lean` closes X-F8-NULL. `Func10Proof.lean`
carries X-F13-ADD and the live X-F13-OOM arm. `Func12Proof.lean` closes
X-F15-OFFSET. `Func7Proof.lean` closes X-F10-TAG, and the error arms of
`InsertTailProof.lean` close the same row at their own call site.

## The `talos.oom` exit

Absolute function 59 is `call 2` and then `unreachable`, at WAT lines
9947 to 9950. It is the `talos.oom` exit. It is an arm of every
allocating contract. It is not an exclusion.
