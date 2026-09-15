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
- `adequate`: the theorem reaches the public fuel-free theorem.

A status with a parenthesis is a `proved` theorem that keeps a named
hypothesis. The evidence column names the hypothesis.

## Current status

| Component | Status | Evidence / blocker |
| --- | --- | --- |
| imports absolute 0-2 | proved | `ImportProofs.lean` |
| allocator absolute 55, 57, 58, 59 | proved | note A |
| `io::Error::new` chain | proved | note B |
| decode error absolute 52 | proved | note C |
| decoder absolute 4 (`Func1Spec`) | proved | `44588ac`, `21fc3f1` |
| grow absolute 33, 100, 101 | proved | `d4da4b8` |
| read phase absolute 22 | proved | `4014844` |
| driver tail absolute 22 | proved (`Func2Spec`) | note D |
| `map_len` | adequate (`Func2Spec`) | note E |
| collect_entries absolute 5 | proved (two premises) | note F |
| absolute 16 (`Func13Spec`) | proved | `Func13Proof.lean`; note L |
| absolute 17 (`Func14Spec`) | proved | note G |
| absolute 18 (`Func15Spec`) | proved (one arm) | note H |
| absolute 83 | proved | `Func80Proof.lean`; note L |
| key decoder absolute 10 (`Func7Spec`) | proved | note I |
| lookup absolute 12 (`Func9Spec`) | proved | `Func9Proof.lean` |
| lookup absolute 20 (`Func17Spec`) | proved | `Func17Proof.lean` |
| remove kernel absolute 11 (`Func8Spec`) | proved | `9a99663`; note O |
| insert shim absolute 6 (`Func3Spec`) | proved (`Func15InsertSpec`) | `44b31aa`; note O |
| sort group absolute 14, 15, 23, 24, 25 | proved | note J |
| sorted entries absolute 7 (`Func4Spec`) | proved | `5576fa2`; note P |
| grow absolute 13 (`Func10Spec`) | proved | `0660cc4`; note Q |
| reply writer absolute 8 (`Func5Spec`) | proved | `07864a1`; note P |
| absolute 107 (`panic_on_ord_violation`) | discovered | note K |
| drivers absolute 19, 21 | proved (`Func2Spec`) | note M |
| driver absolute 9 (`map_remove`) | proved (`Func2Spec`) | `f049b79`; note M |
| driver absolute 3 (`map_insert`) | proved (`Func2Spec`, `Func3Spec`) | `b0d7078`; note M |
| wrappers absolute 28, 29, 30, 32 | proved (drivers) | note N |
| `map_remove` | adequate (`Func2Spec`) | note M |
| `map_insert` | adequate (`Func2Spec`, `Func15InsertSpec`) | note M |
| adequacy bridge | proved | `Adequacy.lean` |

## Notes

- Note A. `AllocatorContracts.lean`, `Allocator.lean`, `DeallocNoop.lean`
  and `ImportProofs.lean` carry the four allocator bodies and the import
  shims that they use.
- Note B. The chain is absolute 42, 43, 44, 48, 50, 51, 55, 56 and 57.
  It closes `Func52Spec`. The hashes are `dabd7f9` (absolute 44),
  `baa1cd7` (absolute 50), `2411b4f` (absolute 48), `8b38061`
  (absolute 51), `0b1d494` (absolute 57) and `57e00b6` (absolute 55,
  which closes the chain).
- Note C. `7e57c6b` proves absolute 52 and its subtree. `Func49Spec`
  holds.
- Note D. `DriverTailProof.lean` (`4695608`). The theorem takes
  `Func2Spec` as a hypothesis.
- Note E. `DriverProof.lean` states `mapLen_of_bodies` (`6fe59ca`).
  `c106a50` narrows the premise list to `Func2Spec` only.
- Note F. The other lane assembles the body. The parts are the prologue
  (`6f9106a`), the loop (`f6e3d49`), the tail (`fe4ee40` and `cf18769`),
  the reserve block (`13fe136`) and the assembly (`0aeaefa`).
  `CollectAssembly.lean` states `Func2SpecStrong` and proves
  `func2_correct_of (hreserve : Func14Spec) (hsingleton : ...)`. The
  other lane proved absolute 17 in `Func14Proof.lean` (`8c78c4e`). No
  imported file reaches that file, so `Func14Spec` stays a hypothesis
  here. The resize path of absolute 17 is stated as `Func14ResizeSpec`
  in `MapOpContracts.lean` (`c185345`), and the other lane owns it.
  Two blockers stay open. `hsingleton` needs the `SingletonBody` repair
  in the codelib file `TableMem.lean`. `Func2Spec` must become
  `Func2SpecStrong`, which is Part A of this lane. See note L.
- Note G. `Func14Proof.lean` (`8c78c4e`, the other lane) proves
  absolute 17 for the collect path. `Func14Capacity.lean` (`3ab957f`)
  states the capacity arithmetic. The resize path is stated as
  `Func14ResizeSpec` in `MapOpContracts.lean` and stays open. See
  note L.
- Note H. `Func15Proof.lean` proves one arm. The resize arm
  (`growth_left == 0`, WAT line 4314) stays open, and it is live for
  `map_insert`. See note L.
- Note I. `Func7Proof.lean` (`7ea932c`) proves `Func7Spec`. `89f0a6a`
  adds `KeyDecoderContract.lean`, which states the contract.
- Note J. The group is `Func11Spec` (absolute 14), `Func12Spec`
  (absolute 15), `Func20Spec` (absolute 23), `Func21Spec` (absolute 24)
  and `Func22Spec` (absolute 25). `SortContracts.lean` (`2ca62d8`)
  states the five contracts. `SortModels.lean` (`cf35aa7`) holds the
  pure models of the sort.
  The five bodies are proved: `1796c0b` (absolute 15), `b4f044b`
  (absolute 23), `2d43dc7` (absolute 25), `7d2588d` (absolute 24) and
  `decaf4b` (absolute 14). Contract finding: `Func21Spec` was not
  provable as stated. The equal-partition guard at WAT 5763 loads the
  key of the ancestor cell, and `AncestorCell` is a bare `pointsTo_u32`
  that carries no address bound, so the load can trap. `aac7fd9` amends
  the contract with `AncestorFits anc`, which is `p + 4 <= 2 ^ 32`, and
  `Func21Proof.func21_correct` closes the contract. `SortContracts.lean`
  records the decision. Every call site has the bound: absolute 14
  passes the null ancestor, and each recursive call passes a key cell of
  its own buffer. `Func11Proof` rests on that contract.
- Note K. The only caller of absolute 107 is dead code in absolute 24.
  Ledger row X-F24-ORDER of `scope-and-exclusions.md` is that edge, and
  `Func21Proof.lean` (`7d2588d`) discharges it with
  `Func21Merge.bimerge_exhausts` of `Func21Merge.lean`. Absolute 107
  therefore needs no proof file.
- Note L. `Project.lean` does not import this file, and no imported
  file reaches it. The unimported set is `CollectBodyContracts.lean`,
  `CollectPrologue.lean`, `CollectLoop.lean`, `CollectTail.lean`,
  `CollectReserve.lean`, `CollectAssembly.lean`, `Func14Capacity.lean`,
  `Func14Proof.lean`, `AlignPow2.lean`, `Func13Proof.lean`,
  `Func15Proof.lean` and `Func80Proof.lean`.
- Note M. The drivers are `Func0Spec` (absolute 3), `Func6Spec`
  (absolute 9), `Func16Spec` (absolute 19) and `Func18Spec`
  (absolute 21). `ContainsKeyDriverProof.lean` (`7540f5b`) and
  `GetDriverProof.lean` (`522e26b`) prove absolute 19 and absolute 21
  under `Func2Spec` alone, as `map_len` does.
  `RemoveDriverProof.lean` (`f049b79`) proves `func6_correct_of` under
  `Func2Spec`, after the read phase (`79e23af`) and the tail
  (`df19a71`). `InsertDriverProof.lean` (`b0d7078`) proves
  `func0_correct_of` under `Func2Spec` and `Func3Spec`, after the read
  phase (`cd53ca3`) and the tail (`53f1303`). In the same file,
  `func0_correct_of_insert` trades `Func3Spec` for `Func15InsertSpec`
  through `Func3Proof.func3_correct_of`. The four public lines are
  `mapContainsKey_of_collect`, `mapGet_of_collect`,
  `mapRemove_of_collect` and `mapInsert_of_bodies`. None of them carries
  `@[proves]`, because their hypotheses are not discharged yet.
- Note N. `b9d6d86` adds `ExportWrappers.lean`. Each wrapper theorem
  takes its driver contract as a named hypothesis, so no theorem there
  carries `@[proves]`.
- Note O. `MapOpContracts.lean` (`c185345`) states `Func8Spec` and
  `Func3Spec`. It also states `Func15InsertSpec` and
  `Func14ResizeSpec` for the other lane. `Func8Proof.lean` (`9a99663`)
  proves `func8_correct`, which closes `Func8Spec`. `Func3Proof.lean`
  (`44b31aa`) proves `func3_correct_of`, which closes `Func3Spec` under
  `Func15InsertSpec`.
- Note P. `EntriesContracts.lean` (`616b136`) states `Func4Spec` and
  `Func5Spec`. `Func4Proof.lean` (`5576fa2`) proves `func4_correct`, and
  `Func5Proof.lean` (`07864a1`) proves `func5_correct`. Contract
  finding: `Func5Spec` holds as stated, because the allocator accounting
  invariant `CapFits` of `Func5Proof.lean`, which is
  `heapBase + 2 * cap <= frontier + 1024`, bounds every doubling of the
  reply buffer. That bound kills the panic arm of the grow, so the
  contract needed no amendment.
- Note Q. `GrowContract.lean` (`9475e8f`) states `Func10Spec`.
  `Func10Proof.lean` (`0660cc4`) proves `func10_correct`.
- Note R. The lookup group adds `LookupPures.lean`,
  `LookupContracts.lean`, `LookupHash.lean`, `LookupProbe.lean`,
  `Func9Proof.lean` (`243f525`), `Func17Proof.lean` (`6603fd0`),
  `LookupTailDefs.lean`, `LookupTailContracts.lean`,
  `ContainsKeyTailProof.lean`, `GetTailProof.lean`,
  `ContainsKeyDriverProof.lean` and `GetDriverProof.lean`. It also adds
  the read phases `ContainsKeyRead.lean` and `GetRead.lean`.
  `Project.lean` imports all fourteen files. The lane also adds
  `PairSlice.lean`, `SortedByKey.lean`, `SortingNetwork.lean` and
  `EraseWasm.lean` in `codelib/CodeLib/RustStd/HashMap/`.
