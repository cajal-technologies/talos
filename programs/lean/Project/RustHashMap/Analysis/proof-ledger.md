# Proof ledger

This ledger covers the `rust_hash_map` program. The absolute Wasm index
`N` is the Lean local name `func(N-3)`. Contract names use the local
index. `Func7Spec` is therefore the contract of absolute function 10.
The function index at the end gives the Rust symbol of every index.

## Status meanings

- `discovered`: the body and its calls are annotated.
- `proved`: the Lean theorem is closed and has no unapproved axiom.
- `adequate`: the theorem reaches the two public fuel-free theorems.
  `MapXSpec` is partial: every finite terminal execution writes exactly
  the output or ends in the allocator OOM outcome, and it does not assert
  termination. `MapXTotalSpec` is total: the run terminates in one of
  those two outcomes.

A status with a parenthesis is a `proved` theorem that keeps a named
hypothesis. The evidence column names the hypothesis.

## Current status

| Component | Status | Evidence / blocker |
| --- | --- | --- |
| imports absolute 0-2 | proved | `ImportProofs.lean` |
| allocator absolute 58, 60, 61, 62; `talos.oom` shim absolute 59 | proved | note A |
| `io::Error::new` chain | proved | note B |
| decode error absolute 52 | proved | note C |
| decoder absolute 4 (`Func1Spec`) | proved | `Func1Proof.lean`; note U |
| grow absolute 33, 100, 101 | proved | `VecGrow.lean`; note T |
| pair-buffer grow absolute 26, 27 | proved | `Func23Proof.lean`, `Func24Proof.lean`; note V |
| read phase absolute 22 | proved | `ReadAllPhase.lean` |
| driver tail absolute 22 | proved (`Func1Spec`, `Func2Spec`, `Func52Spec`) | note D |
| `map_len` | adequate | `MapLen.lean` (`mapLen`, `mapLen_total`); note E |
| `map_contains_key` | adequate | `MapContainsKey.lean` (`mapContainsKey`, `mapContainsKey_total`); note M |
| `map_get` | adequate | `MapGet.lean` (`mapGet`, `mapGet_total`); note M |
| collect_entries absolute 5 | proved | `CollectProof.lean`; note F |
| absolute 16 (`Func13Spec`) | proved | `Func13Proof.lean`; note L |
| absolute 17 (`Func14Spec`) | proved | `Func14Proof.lean`; note G |
| absolute 17 (`Func14ResizeSpec`) | proved | `Func14Resize.lean`; note S |
| absolute 18 (`Func15Spec`) | proved | `Func15Proof.lean`; note H |
| absolute 18 (`Func15InsertSpec`) | proved | `Func15Proof.lean`; note H |
| absolute 83 | proved | `Func80Proof.lean`; note L |
| key decoder absolute 10 (`Func7Spec`) | proved | note I |
| lookup absolute 12 (`Func9Spec`) | proved | `Func9Proof.lean`; note R |
| lookup absolute 20 (`Func17Spec`) | proved | `Func17Proof.lean`; note R |
| remove kernel absolute 11 (`Func8Spec`) | proved | `Func8Proof.lean` |
| insert shim absolute 6 (`Func3Spec`) | proved (`Func15InsertSpec`) | note O |
| sort group absolute 14, 15, 23, 24, 25 | proved | note J |
| sorted entries absolute 7 (`Func4Spec`) | proved | `Func4Proof.lean`; note P |
| grow absolute 13 (`Func10Spec`) | proved | `Func10Proof.lean`; note Q |
| reply writer absolute 8 (`Func5Spec`) | proved | `Func5Proof.lean`; note P |
| absolute 107 (`panic_on_ord_violation`) | discovered | note K |
| drivers absolute 19, 21 | proved (`Func2Spec`) | note M |
| driver absolute 9 (`map_remove`) | proved (`Func2Spec`) | note M |
| driver absolute 3 (`map_insert`) | proved (`Func2Spec`, `Func3Spec`) | note M |
| wrappers absolute 28, 29, 30, 32 | proved (drivers) | note N |
| wrapper absolute 31 | proved (`Func19Spec`) | `DriverProof.lean`; note N |
| `map_remove` | adequate | `MapRemove.lean` (`mapRemove`, `mapRemove_total`); note M |
| `map_insert` | adequate | `MapInsert.lean` (`mapInsert`, `mapInsert_total`); note M |
| partial adequacy bridge | proved | `Adequacy.lean` |
| total adequacy bridge | proved | `Adequacy.lean`, `SmallStepOutcomeAdequacyFrontier.lean` in codelib; note W |

## Notes

- Note A. `AllocatorContracts.lean` and `Allocator.lean` state the four
  allocator contracts, and `Func55Proof.lean` (absolute 58, `__rust_alloc`),
  `Func57Proof.lean` (absolute 60, `__rust_dealloc`), `Func58Proof.lean`
  (absolute 61, `__rust_realloc`) and `Func59Proof.lean` (absolute 62,
  `__rust_alloc_zeroed`) prove them. `DeallocNoop.lean` states the no-op
  contract of the free. `ImportProofs.lean` proves the three imports, the
  `talos.oom` shim at absolute 59 (`func56_correct`) and the two stdio
  shims at absolute 63 and 64.
- Note B. The chain is absolute 42, 43, 44, 48, 50, 51, 55, 56 and 57.
  It closes `Func52Spec`. The files are `Func41Proof.lean` (absolute
  44), `Func47Proof.lean` (absolute 50), `Func45Proof.lean` (absolute
  48), `Func48Proof.lean` (absolute 51), `Func54Proof.lean` (absolute
  57) and `Func52Proof.lean` (absolute 55, which closes the chain).
- Note C. `Func49Proof.lean` proves absolute 52 and its subtree.
  `Func49Spec` holds.
- Note D. `DriverTailProof.lean`. `twp_driver_tail` takes `Func1Spec`,
  `Func2Spec` and `Func52Spec` as hypotheses; `DriverProof.lean` supplies
  them.
- Note E. `DriverProof.lean` states `mapLen_of_bodies`.
  `MapLenOfCollect.lean` narrows the premise list to `Func2Spec` only.
  It then reaches `Spec.MapLenSpec` under that one hypothesis.
  `MapLen.lean` discharges it with `CollectProof.func2_correct` and
  states `Project.RustHashMap.mapLen`, which carries
  `@[proves Project.RustHashMap.Spec.MapLenSpec]`.
- Note F. Five files assemble the body. The parts are the prologue
  (`CollectPrologue.lean`), the loop (`CollectLoop.lean`), the tail
  (`CollectTail.lean`), the reserve block (`CollectReserve.lean`) and
  the assembly (`CollectAssembly.lean`).
  The assembly proves
  `func2_correct_of (hreserve : Func14Spec) : Func2Spec`. That file does
  not import the proof of absolute 17, so `Func14Spec` stays an argument
  there. `CollectProof.lean` imports the three files and states
  `func2_correct : Func2Spec`, which takes no argument. The chain is
  `CollectAssembly.func2_correct_of`, then
  `Func14Proof.func14_correct_of`, then
  `Func55Proof.func55_correct_pow2`.
  The resize path of absolute 17 is stated as `Func14ResizeSpec` in
  `MapOpContracts.lean`, and `Func14Resize.lean` proves it (note S).
  The `SingletonBody` repair landed in the codelib file `TableMem.lean`:
  the static singleton claims `t.ctrl.take 8` now, and
  `CollectAssembly.TableAt_static_empty` proves the former `hsingleton`
  premise. `Func2Spec` lends the eight `EMPTY` bytes at `entryStackTop`
  for it. `Func2SpecStrong` is gone: it became equal to `Func2Spec` by
  statement in `CollectAssembly.lean` and in the two contract files
  after it, so it is deleted. See note L.
- Note G. `Func14Proof.lean` proves absolute 17 for
  the collect path, under the allocator contract
  `Func55SpecPow2`. `Func55Proof.func55_correct_pow2` proves that
  contract, and `CollectProof.lean` joins the two, so the collect path
  of absolute 17 is unconditional now. `Func14Capacity.lean`
  states the capacity arithmetic. The resize path is stated as
  `Func14ResizeSpec` in `MapOpContracts.lean` and `Func14Resize.lean`
  proves it. See note L and note S.
- Note H. `Func15Proof.lean` proves both arms of absolute 18.
  `func15_correct` closes `Func15Spec`, the arm of a table that has
  room. `func15_insert_correct` closes `Func15InsertSpec`, the general
  arm, where a zero `growth_left` word takes the `call 17` of WAT line
  4314 and resizes the table. Three lemmas carry both theorems.
  `twp_insert_prologue` is the frame and the inlined hash of WAT 4131 to
  4300. `growth_cell` takes the `growth_left` word out of `TableAt` and
  gives it back, so the guard reads it in either physical form.
  `twp_insert_after_reserve` is WAT 4316 to 4546, the probe, the found
  arm and the insert, for a table that has room. The resize arm reaches
  it with `Table.reserve hash t 1`, which `Table.WF.reserve` shows has
  room, and `Table.insert_eq_of_reserve` ties the answer back to
  `Table.insert`. `Func14Resize.func14_resize_correct` is the `call 17`.
  See note L and note S.
- Note I. `Func7Proof.lean` proves `Func7Spec`.
  `KeyDecoderContract.lean` states the contract.
  The accepting arm of `Func7Spec` and the accepting arm of
  `Func1Spec` state that the pair buffer has a four-byte alignment.
- Note J. The group is `Func11Spec` (absolute 14), `Func12Spec`
  (absolute 15), `Func20Spec` (absolute 23), `Func21Spec` (absolute 24)
  and `Func22Spec` (absolute 25). `SortContracts.lean` states the five
  contracts. `SortModels.lean` holds the pure models of the sort.
  The five bodies are proved: `Func12Proof.lean` (absolute 15),
  `Func20Proof.lean` (absolute 23), `Func22Proof.lean` (absolute 25),
  `Func21Proof.lean` (absolute 24) and `Func11Proof.lean` (absolute
  14). Contract finding: `Func21Spec` was not provable as stated. The
  equal-partition guard at WAT 5763 loads the key of the ancestor cell,
  and `AncestorCell` is a bare `pointsTo_u32` that carries no address
  bound, so the load can trap.
  `SortContracts.lean` amends the contract with `AncestorFits anc`,
  which is `p + 4 <= 2 ^ 32`, and records the decision.
  `Func21Proof.func21_correct` closes the contract. Every call site has
  the bound: absolute 14 passes the null ancestor, and each recursive
  call passes a key cell of its own buffer. `Func11Proof` rests on that
  contract.
- Note K. The only caller of absolute 107 is dead code in absolute 24.
  Ledger row X-F24-ORDER of `scope-and-exclusions.md` is that edge, and
  `Func21Proof.lean` discharges it with
  `Func21Merge.bimerge_exhausts` of `Func21Merge.lean`. Absolute 107
  therefore needs no proof file.
- Note L. `Project.lean` imports every file of the hash map proof. The
  sixteen collect files are
  `AlignPow2.lean`, `BitPures.lean`, `Func15Hash.lean`, `ProbeStop.lean`,
  `CollectBodyContracts.lean`, `Func14Capacity.lean`, `Func80Proof.lean`,
  `Func13Proof.lean`, `Func15Insert.lean`, `Func15Proof.lean`,
  `CollectLoop.lean`, `CollectTail.lean`, `CollectPrologue.lean`,
  `CollectReserve.lean`, `CollectAssembly.lean` and `Func14Proof.lean`.
  `Func2Spec` is discharged. `CollectProof.lean`
  states `func2_correct : Func2Spec` with no argument. Six more files
  follow, and `Project.lean` imports all six:
  `CollectProof.lean`, `MapLen.lean`, `MapContainsKey.lean`,
  `MapGet.lean`, `MapRemove.lean` and `MapInsert.lean`.
- Note M. The drivers are `Func0Spec` (absolute 3), `Func6Spec`
  (absolute 9), `Func16Spec` (absolute 19) and `Func18Spec`
  (absolute 21). `ContainsKeyDriverProof.lean` and
  `GetDriverProof.lean` prove absolute 19 and absolute 21 under
  `Func2Spec` alone, as `map_len` does. `RemoveDriverProof.lean`
  proves `func6_correct_of` under `Func2Spec`, after the read phase
  (`RemoveRead.lean`) and the tail (`RemoveTailProof.lean`).
  `InsertDriverProof.lean` proves `func0_correct_of` under `Func2Spec`
  and `Func3Spec`, after the read phase (`InsertRead.lean`) and the
  tail (`InsertTailProof.lean`). In the same file,
  `func0_correct_of_insert` trades `Func3Spec` for `Func15InsertSpec`
  through `Func3Proof.func3_correct_of`. The four public lines are
  `mapContainsKey_of_collect`, `mapGet_of_collect`,
  `mapRemove_of_collect` and `mapInsert_of_bodies`. None of the four
  carries `@[proves]`, because each one keeps its hypothesis.
  `MapContainsKey.lean`, `MapGet.lean` and `MapRemove.lean` feed
  `CollectProof.func2_correct` to the first three and state
  `Project.RustHashMap.mapContainsKey`,
  `Project.RustHashMap.mapGet` and `Project.RustHashMap.mapRemove`.
  Those three carry `@[proves]`. `mapInsert_of_bodies` keeps a second
  hypothesis, `Func15InsertSpec`. `MapInsert.lean` feeds
  `CollectProof.func2_correct` and
  `Func15Proof.func15_insert_correct` to it and states
  `Project.RustHashMap.mapInsert`, which carries `@[proves]`. Each of the
  five closers also states `funcNN_correct`, the wrapper contract with no
  hypothesis, and `mapX_total`, which carries
  `@[proves Project.RustHashMap.Spec.MapXTotalSpec]` (note W). All five
  exports are adequate. See note H.
- Note N. `ExportWrappers.lean` holds the four wrappers. Each wrapper
  takes its driver contract as a named hypothesis, so no theorem there
  carries `@[proves]`.
- Note O. `MapOpContracts.lean` states `Func8Spec` and `Func3Spec`. It
  also states `Func15InsertSpec` and `Func14ResizeSpec` for the map
  operations. `Func8Proof.lean` proves `func8_correct`, which closes
  `Func8Spec`. `Func3Proof.lean` proves `func3_correct_of`, which
  closes `Func3Spec` under `Func15InsertSpec`.
- Note P. `EntriesContracts.lean` states `Func4Spec` and `Func5Spec`.
  `Func4Proof.lean` proves `func4_correct`, and `Func5Proof.lean`
  proves `func5_correct`. Contract
  finding: `Func5Spec` holds as stated, because the allocator accounting
  invariant `CapFits` of `Func5Proof.lean`, which is
  `heapBase + 2 * cap <= frontier + 1024`, bounds every doubling of the
  reply buffer. That bound kills the panic arm of the grow, so the
  contract needed no amendment.
- Note Q. `GrowContract.lean` states `Func10Spec`. `Func10Proof.lean`
  proves `func10_correct`.
- Note R. The lookup group adds `LookupPures.lean`,
  `LookupContracts.lean`, `LookupHash.lean`, `LookupProbe.lean`,
  `Func9Proof.lean`, `Func17Proof.lean`,
  `LookupTailDefs.lean`, `LookupTailContracts.lean`,
  `ContainsKeyTailProof.lean`, `GetTailProof.lean`,
  `ContainsKeyDriverProof.lean` and `GetDriverProof.lean`. It also adds
  the read phases `ContainsKeyRead.lean` and `GetRead.lean`.
  `Project.lean` imports all fourteen files. The group also adds
  `PairSlice.lean`, `SortedByKey.lean`, `SortingNetwork.lean` and
  `EraseWasm.lean` in `codelib/CodeLib/RustStd/HashMap/`.
- Note S. The resize path of absolute 17 is `Func14ResizeSpec`.
  `ResizePures.lean` holds the model side of it. It shows
  that a clean table with no growth left takes the resize arm and not the
  rehash-in-place arm (`reserve_one_eq`), it reads the answer off
  `Table.WF.resize` (`resize_spec`), and it names the state of the walk
  loop of WAT 3746 to 4083 (`walkFrom`, `walkRem` and the five step
  lemmas). `moveStep_spec` gives the insert index of one turn and the
  `EMPTY` byte at it. `and_xor_self` and `swarMatchFull_eq_zero_iff` read
  the group mask that the compiled advance loop keeps.
  `Func14ResizeWalk.lean` proves the walk itself. `twp_resize_walk` is
  the loop of WAT 3796 to 4083 under `twp_loop_wf_family`, with the
  length of `walkRem` as the measure. It carries `Table.MoveInv`, so it
  leaves the fresh table equal to the model fold. Seven stage lemmas
  build it: `twp_resize_hoist` (WAT 3750 to 3795), `twp_resize_adv` (WAT
  3797 to 3823), `twp_resize_addr` (WAT 3825 to 3842), `twp_resize_hash`
  (WAT 3843 to 3976), `twp_resize_probe` (WAT 3977 to 4012),
  `twp_resize_fix` (WAT 4018 to 4044) and `twp_resize_write` (WAT 4045
  to 4081).  Nine `rfl` shape theorems tie each fragment to the decoded
  program.  The fresh table has no counters while the walk runs, so the
  probe and the fix take `Table.Layout` plus a short entry list in place
  of `Table.WF` and `Table.Clean`.
  `Func14Resize.lean` closes the contract. `func14_resize_correct` proves
  `Func14ResizeSpec` with no open argument. It reuses the block split and
  the phase names of `Func14Proof.lean`, which lost the `private` marker
  on every one of them for that reason. Three stage lemmas carry it:
  `twp_resize_epilogue` (WAT 4119 to 4129), `twp_resize_tail` (WAT 4085
  to 4129, with the free of the old control array) and
  `twp_resize_commit` (WAT 3665 to 4129, which plugs in the walk).
  `TableAt_open` reads the four header words out of either physical form
  of the old table. The static singleton has no bucket area, and it has
  no items, so the walk is skipped on it and the free is skipped too.
  The free of WAT 4098 to 4117 goes through `DeallocNoop.Func57NoopSpec`,
  because this proof does not hold an allocation token for the old
  control array.
- Note T. `VecGrow.lean` holds the shared layer of the generated grow
  path. `Func30Proof.lean` proves absolute 33, `Func97Proof.lean`
  proves absolute 100 and `Func98Proof.lean` proves absolute 101.
- Note U. `Func1Proof.lean` closes `Func1Spec`. `DecoderBody.lean`
  proves the body of absolute 4 that it assembles.
- Note V. `PairGrow.lean` states `Func23Spec` and `Func24Spec`, the
  contracts of the generated `grow_one` (absolute 26) and `finish_grow`
  (absolute 27) of the pair buffer. `Func24Proof.lean` proves absolute 27
  and `Func23Proof.lean` proves absolute 26 from `Func24Spec`. Row
  X-F4-CAP of `scope-and-exclusions.md` is the dead capacity arm of
  absolute 26.
- Note W. `Adequacy.lean` holds two bridges over the same `EntrySpec`.
  The partial one applies `twp.to_wp` and the partial frontend, and
  reaches `Spec.WritesOrOOM`. The total one applies
  `wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome_frontier`
  of `codelib/CodeLib/SepLogic/SmallStepOutcomeAdequacyFrontier.lean`,
  which keeps the termination half of the total WP, and reaches
  `Spec.TerminatesWritingOrOOM`. `StdioContract.lean` in codelib states
  both shapes.

## File index

`programs/lean/Project/RustHashMap/` holds 166 Lean files. The 80 files
below are the ones that the rows and notes above do not describe, or name
only in notes A and V. They are grouped by what they prove.
`Project.lean` imports every file.

### Contracts and infrastructure

- `Program.lean`: the generated module, one `funcN` per Wasm function.
- `Spec.lean`: the five partial and the five total public contracts.
- `Contracts.lean`: the call-site shapes that every body proof uses, and
  the contracts of the two stdio shims.
- `EntryContracts.lean`: the `EntrySpec` of each export wrapper and the
  constant `maxTableCapacity`.
- `BodyContracts.lean`: the contracts of the three functions that the
  `map_len` tail calls, and the three stack-depth constants.
- `CollectContract.lean`: `Func2Spec`, the contract of `collect_entries`.
- `HostProof.lean`: the three imports resolved to the universal host, and
  the total-WP contract of the `talos.oom` import.
- `FrameCells.lean`: a body frame read as word cells.
- `MapLenOfDecoder.lean`: `map_len` conditional on `Func1Spec` and
  `Func2Spec`, after `Func52Proof` discharges the third hypothesis.

### The borsh decoder, absolute 4

- `DecoderDefs.lean`: the body of absolute 4 split into named fragments.
- `DecoderPrologue.lean`: the two straight-line fragments that need no
  callee.
- `DecoderHeader.lean`, `DecoderHeaderRead.lean`, `DecoderHeaderStage.lean`:
  the four-byte pair count and the empty vector that follows it.
- `DecoderAlloc.lean`, `DecoderAllocPhase.lean`, `DecoderAllocStage.lean`:
  the allocation of the pair buffer and its dead failure arm.
- `DecoderLoop.lean`: the loop invariant and `CapacityFits`.
- `DecoderPairLoop.lean`: the `.loop` closed with `twp_loop_wf_family`.
- `DecoderStep.lean`, `DecoderPairStage.lean`, `DecoderPairRead.lean`,
  `DecoderKeyRead.lean`, `DecoderShortPair.lean`, `DecoderShortValue.lean`:
  one loop step, from the read of one pair to its short-input exits.
- `DecoderGrow.lean`, `DecoderAppend.lean`, `DecoderAppendPair.lean`: the
  grow of a full buffer and the write of one pair.
- `DecoderDecodeStage.lean`: the allocation and then the pair loop.
- `DecoderOkBranch.lean`, `DecoderOkReturn.lean`: the accepting return.
- `DecoderErrorStores.lean`, `DecoderErrorReturn.lean`,
  `DecoderErrorFree.lean`: the four error words and the free of the pair
  buffer on every rejecting return.

### The pair-buffer grow, absolute 26 and 27

- `PairGrow.lean`: `Func23Spec` and `Func24Spec`.
- `Func23Proof.lean`: absolute 26, `grow_one`, from `Func24Spec`.
- `Func24Proof.lean`: absolute 27, `finish_grow`.

### The decode-error subtree below absolute 52

- `DecodeErrorContract.lean`: `Func49Spec`, the contract of absolute 52.
- `DropErrorContracts.lean`: the contracts of the thirteen bodies below
  absolute 52.
- `ErrorNewContracts.lean`: the contracts of the eight bodies below
  absolute 55, `borsh::io::Error::new`.
- `Func31Proof.lean` to `Func40Proof.lean`, without `Func41Proof.lean`:
  absolute 34 to 43, the drops of the error and its message buffer, the
  kind test and the `String` conversion.
- `Func42Proof.lean`, `Func43Proof.lean`, `Func44Proof.lean`: absolute
  45 to 47, the deallocation of the message buffer.
- `Func50Proof.lean`, `Func51Proof.lean`, `Func53Proof.lean`: absolute
  53, 54 and 56, the `ErrorKind` byte, its comparison and the packing of
  the sixteen-byte error.

### The allocator, absolute 58 to 62

- `Func55Proof.lean`: absolute 58, `__rust_alloc`, against
  `Func55SpecPow2`.
- `Func57Proof.lean`: absolute 60, `__rust_dealloc`.
- `Func58Proof.lean`: absolute 61, `__rust_realloc`.
- `Func59Proof.lean`: absolute 62, `__rust_alloc_zeroed`. No closer
  reaches this body, because the zeroed arm of absolute 48 is dead.

### The sort group, absolute 14, 15, 23, 24, 25

- `SortPures.lean`: the pure steps that turn `i64` moves and `i32.clz`
  into statements about the model.
- `HeapModel.lean`: the two facts of the heapsort model that absolute 25
  needs.
- `Func21Defs.lean`: the named fragments of `quicksort`, absolute 24.
- `Func21Partition.lean`: the strict partition, WAT 5977 to 6151.
- `Func21Network9.lean`: the nine-entry sorting network, WAT 6233 to 7008.
- `Func21Network13.lean`: the thirteen-entry sorting network, WAT 7011
  to 8391.
- `Func21Region.lean`: the region half of the small sort, WAT 6193 to
  8501.

### The driver read loops and tails

- `ReadAllDefs.lean`, `ReadAllLoop.lean`, `ReadAllPush.lean`: the
  inlined `read_all` loop that every driver starts with, as a family of
  thread states over a `FrameMap`.
- `InsertReadLoop.lean`: the same loop in the `map_insert` driver, whose
  two scratch registers come in the other order.
- `DriverTailDefs.lean`, `DriverTail.lean`: the tail of the `map_len`
  driver, its fragments and the stack that its callees take.
- `RemoveTailDefs.lean`, `RemoveTailContracts.lean`, `RemovePures.lean`:
  the tail of the `map_remove` driver, its fragments, its contract and
  its pure lemmas.
- `InsertTailDefs.lean`, `InsertTailContracts.lean`, `InsertPures.lean`:
  the same three for the `map_insert` driver.
- `TailShared.lean`: the eight pure helpers that the two tail proofs
  share.

## Function index

The frozen binary has 108 functions: three imports and 105 bodies. The
table gives each absolute index, its Lean local name, its Rust symbol,
the exports whose direct-call closure reaches it, and the file that
proves it. `table only` marks a function that only the indirect-call
table names; no proof reaches one of those, because every reachable
`call_indirect` resolves to a leaf (see `BodyContracts.lean`).
`excluded edge` marks a body of the panic and abort subtree, which no
proof enters: the rows of `scope-and-exclusions.md` show every guard in
front of it false. `not called` marks a body that no function calls and
no table entry names.

The symbols come from the `name` section of the cargo output
`target/wasm32-unknown-unknown/release/rust_hash_map.wasm`, read with
`wasm-tools demangle -t`. The verifier strips that section
(`wasm-tools strip --all` in `verifier/Verifier/Main.lean`) before it
freezes `programs/rust/build/rust_hash_map/program.wasm`, and the strip of
the cargo output is byte-identical to the frozen file (SHA-256
`d914f0b01eb3fbc992e8b3f0c40da781aee4d82dabc4e8627ee7293a0e1d2969`).
The `::h<16 hex digits>` suffix of each symbol and the `[<16 hex digits>]`
crate disambiguators are dropped; they vary with the build machine and
the rest does not. Two functions carry the same symbol
`<alloc::raw_vec::RawVecInner>::finish_grow`; absolute 100 is the live
one and absolute 74 is not called.

| Absolute | Local | Rust symbol | Reached from | Proof file |
| ---: | --- | --- | --- | --- |
| 0 | import | `talos_stdio::sys::read` | all five | `ImportProofs.lean` |
| 1 | import | `talos_stdio::sys::write` | all five | `ImportProofs.lean` |
| 2 | import | `talos_stdio::allocator::oom` | all five | `ImportProofs.lean` |
| 3 | func0 | `rust_hash_map::map_insert` | insert | `InsertDriverProof.lean` |
| 4 | func1 | `<alloc::vec::Vec<T> as borsh::de::BorshDeserialize>::deserialize_reader` | all five | `Func1Proof.lean` |
| 5 | func2 | `rust_hash_map::collect_entries` | all five | `CollectProof.lean` |
| 6 | func3 | `rust_hash_map::insert` | insert | `Func3Proof.lean` |
| 7 | func4 | `rust_hash_map::sorted_entries` | insert, remove | `Func4Proof.lean` |
| 8 | func5 | `rust_hash_map::reply` | insert, remove | `Func5Proof.lean` |
| 9 | func6 | `rust_hash_map::map_remove` | remove | `RemoveDriverProof.lean` |
| 10 | func7 | `borsh::de::from_slice` | contains_key, get, remove | `Func7Proof.lean` |
| 11 | func8 | `rust_hash_map::remove` | remove | `Func8Proof.lean` |
| 12 | func9 | `rust_hash_map::contains_key` | contains_key | `Func9Proof.lean` |
| 13 | func10 | `alloc::raw_vec::RawVecInner<A>::reserve::do_reserve_and_handle` | insert, remove | `Func10Proof.lean` |
| 14 | func11 | `core::slice::sort::unstable::ipnsort` | insert, remove | `Func11Proof.lean` |
| 15 | func12 | `core::slice::sort::shared::smallsort::insertion_sort_shift_left` | insert, remove | `Func12Proof.lean` |
| 16 | func13 | `std::sys::thread_local::no_threads::LazyStorage<T>::initialize` | all five | `Func13Proof.lean` |
| 17 | func14 | `hashbrown::raw::RawTable<T,A>::reserve_rehash` | all five | `Func14Proof.lean` |
| 18 | func15 | `hashbrown::map::HashMap<K,V,S,A>::insert` | all five | `Func15Proof.lean` |
| 19 | func16 | `rust_hash_map::map_contains_key` | contains_key | `ContainsKeyDriverProof.lean` |
| 20 | func17 | `rust_hash_map::get` | get | `Func17Proof.lean` |
| 21 | func18 | `rust_hash_map::map_get` | get | `GetDriverProof.lean` |
| 22 | func19 | `rust_hash_map::map_len` | len | `DriverProof.lean` |
| 23 | func20 | `core::slice::sort::shared::pivot::median3_rec` | insert, remove | `Func20Proof.lean` |
| 24 | func21 | `core::slice::sort::unstable::quicksort::quicksort` | insert, remove | `Func21Proof.lean` |
| 25 | func22 | `core::slice::sort::unstable::heapsort::heapsort` | insert, remove | `Func22Proof.lean` |
| 26 | func23 | `alloc::raw_vec::RawVec<T,A>::grow_one` | all five | `Func23Proof.lean` |
| 27 | func24 | `alloc::raw_vec::RawVecInner<A>::finish_grow` | all five | `Func24Proof.lean` |
| 28 | func25 | `map_contains_key` | contains_key | `ExportWrappers.lean` |
| 29 | func26 | `map_get` | get | `ExportWrappers.lean` |
| 30 | func27 | `map_insert` | insert | `ExportWrappers.lean` |
| 31 | func28 | `map_len` | len | `DriverProof.lean` |
| 32 | func29 | `map_remove` | remove | `ExportWrappers.lean` |
| 33 | func30 | `__rustc::__rust_no_alloc_shim_is_unstable_v2` | all five | `Func30Proof.lean` |
| 34 | func31 | `core::ptr::drop_in_place<alloc::string::String>` | all five | `Func31Proof.lean` |
| 35 | func32 | `core::ptr::drop_in_place<alloc::vec::Vec<u8>>` | all five | `Func32Proof.lean` |
| 36 | func33 | `core::ptr::drop_in_place<borsh::nostd_io::Repr>` | all five | `Func33Proof.lean` |
| 37 | func34 | `core::ptr::drop_in_place<borsh::nostd_io::Custom>` | all five | `Func34Proof.lean` |
| 38 | func35 | `core::ptr::drop_in_place<borsh::nostd_io::Error>` | all five | `Func35Proof.lean` |
| 39 | func36 | `<alloc::vec::Vec<T,A> as core::ops::drop::Drop>::drop` | all five | `Func36Proof.lean` |
| 40 | func37 | `core::ptr::drop_in_place<alloc::raw_vec::RawVec<u8>>` | all five | `Func37Proof.lean` |
| 41 | func38 | `<alloc::raw_vec::RawVec<T,A> as core::ops::drop::Drop>::drop` | all five | `Func38Proof.lean` |
| 42 | func39 | `<T as core::convert::Into<U>>::into` | all five | `Func39Proof.lean` |
| 43 | func40 | `<alloc::string::String as core::convert::From<&str>>::from` | all five | `Func40Proof.lean` |
| 44 | func41 | `alloc::alloc::Global::alloc_impl_runtime` | all five | `Func41Proof.lean` |
| 45 | func42 | `alloc::raw_vec::RawVecInner<A>::deallocate` | all five | `Func42Proof.lean` |
| 46 | func43 | `alloc::raw_vec::RawVecInner<A>::current_memory` | all five | `Func43Proof.lean` |
| 47 | func44 | `<alloc::alloc::Global as core::alloc::Allocator>::deallocate` | all five | `Func44Proof.lean` |
| 48 | func45 | `alloc::raw_vec::RawVecInner<A>::try_allocate_in` | all five | `Func45Proof.lean` |
| 49 | func46 | `<alloc::alloc::Global as core::alloc::Allocator>::allocate_zeroed` | all five | dead arm of 48 (`Func45Proof.lean`) |
| 50 | func47 | `<alloc::alloc::Global as core::alloc::Allocator>::allocate` | all five | `Func47Proof.lean` |
| 51 | func48 | `alloc::raw_vec::RawVecInner<A>::with_capacity_in` | all five | `Func48Proof.lean` |
| 52 | func49 | `borsh::de::unexpected_eof_to_unexpected_length_of_input` | all five | `Func49Proof.lean` |
| 53 | func50 | `borsh::nostd_io::Error::kind` | all five | `Func50Proof.lean` |
| 54 | func51 | `<borsh::nostd_io::ErrorKind as core::cmp::PartialEq>::eq` | all five | `Func51Proof.lean` |
| 55 | func52 | `borsh::nostd_io::Error::new` | all five | `Func52Proof.lean` |
| 56 | func53 | `borsh::nostd_io::Error::_new` | all five | `Func53Proof.lean` |
| 57 | func54 | `<T as alloc::slice::<impl [T]>::to_vec_in::ConvertVec>::to_vec` | all five | `Func54Proof.lean` |
| 58 | func55 | `__rustc::__rust_alloc` | all five | `Func55Proof.lean` |
| 59 | func56 | `talos_stdio::allocator::abort_oom` | all five | `ImportProofs.lean` |
| 60 | func57 | `__rustc::__rust_dealloc` | all five | `Func57Proof.lean` |
| 61 | func58 | `__rustc::__rust_realloc` | all five | `Func58Proof.lean` |
| 62 | func59 | `__rustc::__rust_alloc_zeroed` | all five | `Func59Proof.lean` |
| 63 | func60 | `talos_stdio::read` | all five | `ImportProofs.lean` |
| 64 | func61 | `talos_stdio::write` | all five | `ImportProofs.lean` |
| 65 | func62 | `__rustc::__rust_start_panic` | all five | excluded edge |
| 66 | func63 | `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global>` | none | not called |
| 67 | func64 | `core::ptr::drop_in_place::<core::option::Option<alloc::vec::Vec<u8>>>` | all five | excluded edge |
| 68 | func65 | `core::ptr::drop_in_place::<alloc::string::String>` | table only | table entry, never called |
| 69 | func66 | `core::ptr::drop_in_place::<std::panicking::panic_handler::FormatStringPayload>` | table only | table entry, never called |
| 70 | func67 | `std::sys::backtrace::__rust_end_short_backtrace::<std::alloc::rust_oom::{closure#0}, !>` | all five | excluded edge |
| 71 | func68 | `std::alloc::rust_oom::{closure#0}` | all five | excluded edge |
| 72 | func69 | `std::sys::backtrace::__rust_end_short_backtrace::<std::panicking::panic_handler::{closure#0}, !>` | all five | excluded edge |
| 73 | func70 | `std::panicking::panic_handler::{closure#0}` | all five | excluded edge |
| 74 | func71 | `<alloc::raw_vec::RawVecInner>::finish_grow` | none | not called |
| 75 | func72 | `std::panicking::panic_with_hook` | all five | excluded edge |
| 76 | func73 | `std::alloc::default_alloc_error_hook` | table only | table entry, never called |
| 77 | func74 | `__rustc::rust_panic` | all five | excluded edge |
| 78 | func75 | `__rustc::__rust_abort` | all five | excluded edge |
| 79 | func76 | `__rustc::rust_begin_unwind` | all five | excluded edge |
| 80 | func77 | `__rustc::__rust_alloc_error_handler` | all five | excluded edge |
| 81 | func78 | `std::alloc::rust_oom` | all five | excluded edge |
| 82 | func79 | `std::panicking::panic_count::increase` | all five | excluded edge |
| 83 | func80 | `std::sys::random::unsupported::hashmap_random_keys` | all five | `Func80Proof.lean` |
| 84 | func81 | `<alloc::string::String as core::any::Any>::type_id` | table only | table entry, never called |
| 85 | func82 | `<&str as core::any::Any>::type_id` | table only | table entry, never called |
| 86 | func83 | `<std::panicking::panic_handler::FormatStringPayload as core::fmt::Display>::fmt` | table only | table entry, never called |
| 87 | func84 | `<std::panicking::panic_handler::StaticStrPayload as core::panic::PanicPayload>::get` | table only | table entry, never called |
| 88 | func85 | `<std::panicking::panic_handler::StaticStrPayload as core::panic::PanicPayload>::as_str` | table only | table entry, never called |
| 89 | func86 | `<std::panicking::panic_handler::StaticStrPayload as core::panic::PanicPayload>::take_box` | table only | table entry, never called |
| 90 | func87 | `<std::panicking::panic_handler::StaticStrPayload as core::fmt::Display>::fmt` | table only | table entry, never called |
| 91 | func88 | `<alloc::string::String as core::fmt::Write>::write_char` | table only | table entry, never called |
| 92 | func89 | `<alloc::string::String as core::fmt::Write>::write_str` | table only | table entry, never called |
| 93 | func90 | `<std::panicking::panic_handler::FormatStringPayload as core::panic::PanicPayload>::get` | table only | table entry, never called |
| 94 | func91 | `<std::panicking::panic_handler::FormatStringPayload as core::panic::PanicPayload>::take_box` | table only | table entry, never called |
| 95 | func92 | `<std::panicking::begin_panic::Payload<&str> as core::panic::PanicPayload>::as_str` | table only | table entry, never called |
| 96 | func93 | `<alloc::string::String as core::fmt::Write>::write_fmt` | table only | table entry, never called |
| 97 | func94 | `<hashbrown::raw::Fallibility>::capacity_overflow` | all five | excluded edge |
| 98 | func95 | `<hashbrown::raw::Fallibility>::alloc_err` | all five | excluded edge |
| 99 | func96 | `alloc::raw_vec::handle_error` | all five | excluded edge |
| 100 | func97 | `<alloc::raw_vec::RawVecInner>::finish_grow` | all five | `Func97Proof.lean` |
| 101 | func98 | `<alloc::raw_vec::RawVec<u8>>::grow_one` | all five | `Func98Proof.lean` |
| 102 | func99 | `alloc::alloc::handle_alloc_error` | all five | excluded edge |
| 103 | func100 | `alloc::raw_vec::capacity_overflow` | all five | excluded edge |
| 104 | func101 | `core::panicking::panic_fmt` | all five | excluded edge |
| 105 | func102 | `core::fmt::write` | none | not called |
| 106 | func103 | `<core::fmt::Formatter>::write_str` | none | not called |
| 107 | func104 | `core::slice::sort::shared::smallsort::panic_on_ord_violation` | insert, remove | excluded edge |
