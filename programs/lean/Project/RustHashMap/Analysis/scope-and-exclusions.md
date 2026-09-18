# Valid-input scope and exclusion obligations

An excluded edge is discharged at its originating guard in the reachable
caller.  The proof at that program point must derive that the branch
condition is false from the caller's entry facts, a callee
postcondition, or the current loop invariant.  It may not assume that an
error routine is benign, appeal to the error routine's intended
behavior, or prove a theorem about the excluded callee.

## Build profile

The frozen binary comes from one build.  The rows below name its WAT
lines, so they hold for this build only.

- Toolchain: rustc 1.95.0, target `wasm32-unknown-unknown`
  (`programs/rust/rust-toolchain.toml`, alias `build-wasm` in
  `programs/rust/.cargo/config.toml`).
- Profile: `[profile.release]` has `opt-level = 0`, `lto = false` and
  `codegen-units = 1`, and `[profile.release.package.rust_hash_map]`
  sets `opt-level = 3` for this crate alone (`programs/rust/Cargo.toml`).
  No `panic`, `overflow-checks`, `debug` or `strip` key is set, so cargo's
  release defaults apply.
- Tools: wasm-tools 1.251.0 (`justfile`).  The verifier runs
  `wasm-tools strip --all` before it prints the WAT
  (`verifier/Verifier/Main.lean`), so the frozen WAT carries no name
  section and every function is an index.  The WAT SHA-256
  `578221d6197053edb0629e77a9ae62c2c4099ac6b7cc44079b1c534374b5bbf7` is
  pinned in `Program.lean`.

Every panic in this binary reaches `core::panicking::panic_fmt`, absolute
function 104, whose call chain 104, 79, 72, 73, 75, 77, 65, 78 makes no
call that returns and ends in `unreachable` at every leaf.  The rows below
discharge the guards in front of those calls and in front of the
allocation-error calls, absolute functions 99 and 102.

## How to read the table

The line numbers refer to the frozen WAT file
`programs/rust/build/rust_hash_map/program.wat`.

The column names are short. `WAT call` is the frozen WAT call.
`Guard` is the originating guard. `Edge` is the excluded edge. The
source of each edge is the absolute function in the obligation key, so
the column gives the target only. `Required fact` points into the list
below the table.

Absolute Wasm index `N` is the Lean local name `func(N-3)`.  The
function index in `proof-ledger.md` gives the Rust symbol of each index.

| Obligation | WAT call | Guard | Edge | Required fact |
| --- | ---: | --- | --- | --- |
| X-D19-NULL | 4763 | 4698-4701 | -> 99 | f1 |
| X-D21-NULL | 5300 | 5220-5223 | -> 99 | f1 |
| X-D22-NULL | 5570 | 5527-5530 | -> 99 | f2 |
| X-F7-NULL | 1285 | 1115-1120 | -> 99 | f1 |
| X-F8-NULL | 1473 | 1314-1319 | -> 99 | f1 |
| X-F7-CAP | 1285 | 1084-1091 | -> 99 | f3 |
| X-F7-GROW | 1215 | 1203-1207 | -> 13 | f4 |
| X-F13-ADD | 2572 | 2563-2570 | -> 99 | f5 |
| X-F13-OOM | 2618 | 2609-2613 | -> 99 | f6 |
| X-F17-WRAP | 3644 | 3033-3041 | -> 97 | f20 |
| X-F17-REHASH | 3116-3640 | 3043-3064 | in place | f8 |
| X-F17-CAP2 | 3107 | 3078-3082 | -> 97 | f19 |
| X-F17-NULL | 3694 | 3682-3687 | -> 98 | f1 |
| X-F17-CAP | 3707 | 3678-3681 | -> 97 | f7 |
| X-F16-STATE | 3002 | 2993-2998 | -> 104 | f9, f17 |
| X-F24-ORDER | 8654, 8656-8657 | 5944, 6152, 8396, 8632-8653 | -> 107 | f10 |
| X-F24-EQUAL | 5758-5976 | 5760-5771 | equal part | f11 |
| X-F24-HEAP | 5692 | 5687-5693 | -> 25 | f12 |
| X-F15-OFFSET | 2951 | 2855 | unreachable | f13 |
| X-F101-CAP | 11276 | 11266-11271 | -> 99 | f14 |
| X-F4-NULL | 818 | 586-591 | -> 99 | f1 |
| X-F4-CAP | 8848 | 8838-8843 | -> 99 | f15 |
| X-F51-CAP | 9611 | 9600-9606 | -> 99 | f21 |
| X-F83-NULL | 10630 | 10622-10627 | -> 102 | f1 |
| X-F10-TAG | none | 1798-1800, 1822-1824 | okTag arms | f16 |
| X-F18-RESIZE | 4314 | 4302-4304 | -> 17 | f18 |

The obligation key names the function that holds the guard.  X-F4-CAP
sits in absolute function 26, which absolute function 4 reaches through
`call 26` at WAT 772; X-F51-CAP sits in absolute function 51; X-F83-NULL
sits in absolute function 83.

## Required local facts

- f1. `Func55Spec` returns a nonzero pointer. An out-of-memory result
  traps through `talos.oom` instead.
- f2. The same fact as f1. The proof `twp_reply` closes it.
- f3. `t.items <= 2 ^ 27` follows from `t.buckets <= 2 ^ 27`.
- f4. The push-loop invariant gives `len < items <= cap`.
- f5. `len + additional < 2 ^ 32` follows from the buffer bound.
- f6. The arm at WAT 2618 is dead: `Func24Spec` reports tag 0 under the
  size bound.  What stays live is the out-of-memory outcome of
  `Func24Spec`, which traps through `talos.oom`.
- f7. `1 <= additional <= maxTableCapacity` from `Func14Spec`.
- f8. The table is `Table.empty` in the collect path. In the insert
  resize path the table satisfies `Clean t /\ growthLeft = 0`.
- f9. `keysBefore[16]? != some 2`, which is the thread-state conjunct of
  `Func2Spec`.
- f10. The u32 relation `<` is a strict total order. The lemma
  `bimerge_exhausts` gives the rest.
- f11. `NodupKeys` together with `AncestorBelow`. The guard compares the
  ancestor against the pivot.
- f12. This edge is live and is not excluded. `Func22Spec` proves it.
- f13. `1 <= offset <= len`, which is a precondition of `Func12Spec`.
- f14. `PushVecFacts` in `VecGrow.lean`. This fact is proved.
- f15. `Func24Spec` always reports the result tag 0, so the guard at
  WAT 8838 to 8843 reads a word that is not 1.  The capacity bound of
  `Func23Spec` makes the new layout valid, which makes `Func24Spec`
  apply.
- f16. `word1 != okTag` from `Func52Spec` and `Func49Spec`.
- f17. The single-shot instance never sets the thread state to 2.
- f18. This edge is live for `map_insert`. It is dead in the collect
  path, where `1 <= growthLeft`.
- f19. `t.items + additional <= maxTableCapacity = 2 ^ 27`, so the
  compiled bound `> 536870911` is false.
- f20. `t.items + additional < 2 ^ 32`, so the add at WAT 3037 never
  wraps.
- f21. Absolute function 48 reports the flag word 0 for the error-string
  layout, so the low bit that WAT 9600 to 9606 tests is zero.

## Where each row is discharged

- X-D19-NULL: `ContainsKeyRead.twp_contains_key_read_phase`.
- X-D21-NULL: `GetRead.twp_get_read_phase`.
- X-D22-NULL: `ReadAllPhase.twp_read_phase`.
- X-F7-NULL, X-F7-CAP, X-F7-GROW: `Func4Proof.lean`.
- X-F8-NULL: `Func5Proof.lean`.
- X-F13-ADD and the `talos.oom` outcome of X-F13-OOM: `Func10Proof.lean`.
- X-F17-WRAP: `Func14Proof.lean` and `Func14Resize.lean`, with
  `twp_ltU (result := 0)`.
- X-F17-REHASH: `ResizePures.reserve_one_eq` under
  `Func14Resize.func14_resize_correct`; the collect path never reaches
  the guard with items.
- X-F17-CAP2 and X-F17-CAP: `Func14Proof.func14_correct_of` and
  `Func14Resize.func14_resize_correct`, with `twp_gtU (result := 0)`.
- X-F17-NULL: `Func14Proof.lean` and `Func14Resize.lean`, with
  `twp_brIf hbaseNonzero`.
- X-F16-STATE: `Func13Proof.func13_correct`, with `toUInt32_ne_two`.
- X-F24-ORDER: `Func21Merge.lean`, with `bimerge_exhausts`.
- X-F24-EQUAL: `Func21Proof.lean`, with `twp_equal_guard`.
- X-F24-HEAP: `Func22Proof.func22_correct` proves `Func22Spec`, which
  carries the live edge.
- X-F15-OFFSET: `Func12Proof.lean`.
- X-F101-CAP: `Func98Proof.lean`.
- X-F4-NULL: `DecoderAllocStage.twp_alloc_stage`.
- X-F4-CAP: `Func23Proof.func23_correct`, with `twp_ne (result := 1)`.
- X-F51-CAP: `Func48Proof.func48_correct`, with `twp_eqz (result := 1)`.
- X-F83-NULL: `Func80Proof.func80_correct`, with `LiveBlock_ptr_ne_zero`.
- X-F10-TAG: `Func7Proof.lean`, and the error arms of
  `InsertTailProof.lean` close the same row at their own call site.
- X-F18-RESIZE: `Func15Proof.func15_correct` proves the collect path,
  where the edge is dead, and `Func15Proof.func15_insert_correct` proves
  the insert path, where the edge is live.

## The `talos.oom` exit

Absolute function 59 is `call 2` and then `unreachable`, at WAT lines
9947 to 9950. It is the `talos.oom` exit. It is an arm of every
allocating contract. It is not an exclusion.

The `unreachable` at WAT 9940 in absolute function 58, at WAT 10030 in
absolute function 61 and at WAT 10104 in absolute function 62 each follow
a `call 59`.  They are the same exit, seen from the three allocator entry
points, and not exclusions either.
