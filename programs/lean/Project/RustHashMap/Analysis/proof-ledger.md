# Proof ledger

This ledger covers the `rust_hash_map` lane. The absolute Wasm index `N`
is the Lean local name `func(N-3)`. Contract names use the local index.
`Func7Spec` is therefore the contract of absolute function 10.

## Status meanings

- `discovered`: the body and its calls are annotated.
- `first pass`: a dossier exists, but analysis fields stay open.
- `draft contract`: the interface is written but not audited.
- `frozen`: the provability and all call sites are audited.
- `proved`: the Lean theorem is closed and has no unapproved axiom.
- `adequate`: the theorem reaches the public fuel-free theorem. That
  theorem is partial: every finite terminal execution writes exactly the
  output or ends in the allocator OOM outcome, and it does not assert
  termination.

A status with a parenthesis is a `proved` theorem that keeps a named
hypothesis. The evidence column names the hypothesis.

## Current status

| Component | Status | Evidence / blocker |
| --- | --- | --- |
| imports absolute 0-2 | proved | `ImportProofs.lean` |
| allocator absolute 55, 57, 58, 59 | proved | note A |
| `io::Error::new` chain | proved | note B |
| decode error absolute 52 | proved | note C |
| decoder absolute 4 (`Func1Spec`) | proved | `Func1Proof.lean`; note U |
| grow absolute 33, 100, 101 | proved | `VecGrow.lean`; note T |
| read phase absolute 22 | proved | `ReadAllPhase.lean` |
| driver tail absolute 22 | proved (`Func2Spec`) | note D |
| `map_len` | adequate | `MapLen.lean`; note E |
| `map_contains_key` | adequate | `MapContainsKey.lean`; note M |
| `map_get` | adequate | `MapGet.lean`; note M |
| collect_entries absolute 5 | proved | `CollectProof.lean`; note F |
| absolute 16 (`Func13Spec`) | proved | `Func13Proof.lean`; note L |
| absolute 17 (`Func14Spec`) | proved | `Func14Proof.lean`; note G |
| absolute 17 (`Func14ResizeSpec`) | proved | `Func14Resize.lean`; note S |
| absolute 18 (`Func15Spec`) | proved | `Func15Proof.lean`; note H |
| absolute 18 (`Func15InsertSpec`) | proved | `Func15Proof.lean`; note H |
| absolute 83 | proved | `Func80Proof.lean`; note L |
| key decoder absolute 10 (`Func7Spec`) | proved | note I |
| lookup absolute 12 (`Func9Spec`) | proved | `Func9Proof.lean` |
| lookup absolute 20 (`Func17Spec`) | proved | `Func17Proof.lean` |
| remove kernel absolute 11 (`Func8Spec`) | proved | `Func8Proof.lean` |
| insert shim absolute 6 (`Func3Spec`) | proved (`Func15InsertSpec`) | note O |
| sort group absolute 14, 15, 23, 24, 25 | proved | note J |
| sorted entries absolute 7 (`Func4Spec`) | proved | `Func4Proof.lean` |
| grow absolute 13 (`Func10Spec`) | proved | `Func10Proof.lean` |
| reply writer absolute 8 (`Func5Spec`) | proved | `Func5Proof.lean` |
| absolute 107 (`panic_on_ord_violation`) | discovered | note K |
| drivers absolute 19, 21 | proved (`Func2Spec`) | note M |
| driver absolute 9 (`map_remove`) | proved (`Func2Spec`) | note M |
| driver absolute 3 (`map_insert`) | proved (`Func2Spec`, `Func3Spec`) | note M |
| wrappers absolute 28, 29, 30, 32 | proved (drivers) | note N |
| `map_remove` | adequate | `MapRemove.lean`; note M |
| `map_insert` | adequate | `MapInsert.lean`; note M |
| adequacy bridge | proved | `Adequacy.lean` |

## Notes

- Note A. `AllocatorContracts.lean`, `Allocator.lean`, `DeallocNoop.lean`
  and `ImportProofs.lean` carry the four allocator bodies and the import
  shims that they use.
- Note B. The chain is absolute 42, 43, 44, 48, 50, 51, 55, 56 and 57.
  It closes `Func52Spec`. The files are `Func41Proof.lean` (absolute
  44), `Func47Proof.lean` (absolute 50), `Func45Proof.lean` (absolute
  48), `Func48Proof.lean` (absolute 51), `Func54Proof.lean` (absolute
  57) and `Func52Proof.lean` (absolute 55, which closes the chain).
- Note C. `Func49Proof.lean` proves absolute 52 and its subtree.
  `Func49Spec` holds.
- Note D. `DriverTailProof.lean`. The theorem takes `Func2Spec` as a
  hypothesis.
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
  states `func2_correct : Func2Spec` with no argument. Five more files
  follow, and `Project.lean` imports all five:
  `CollectProof.lean`, `MapLen.lean`, `MapContainsKey.lean`,
  `MapGet.lean` and `MapRemove.lean`.
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
  `Project.RustHashMap.mapInsert`, which carries `@[proves]`. All five
  exports are adequate now. See note H.
- Note N. `ExportWrappers.lean` holds the four wrappers. Each wrapper
  takes its driver contract as a named hypothesis, so no theorem there
  carries `@[proves]`.
- Note O. `MapOpContracts.lean` states `Func8Spec` and `Func3Spec`. It
  also states `Func15InsertSpec` and `Func14ResizeSpec` for the other
  lane. `Func8Proof.lean` proves `func8_correct`, which closes
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
