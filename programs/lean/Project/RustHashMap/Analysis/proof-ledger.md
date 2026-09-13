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
| absolute 17 (`Func14Spec`) | draft contract | note G |
| absolute 18 (`Func15Spec`) | proved (one arm) | note H |
| absolute 83 | proved | `Func80Proof.lean`; note L |
| key decoder absolute 10 (`Func7Spec`) | draft contract | note I |
| lookup absolute 12 (`Func9Spec`) | discovered | no file |
| lookup absolute 20 (`Func17Spec`) | discovered | no file |
| remove kernel absolute 11 (`Func8Spec`) | discovered | no file |
| insert shim absolute 6 (`Func3Spec`) | discovered | no file |
| sort group absolute 14, 15, 23, 24, 25 | discovered | note J |
| sorted entries absolute 7 (`Func4Spec`) | discovered | no file |
| grow absolute 13 (`Func10Spec`) | discovered | no file |
| reply writer absolute 8 (`Func5Spec`) | discovered | no file |
| absolute 107 (`panic_on_ord_violation`) | discovered | note K |
| drivers absolute 3, 9, 19, 21 | discovered | note M |
| wrappers absolute 28, 29, 30, 32 | proved (drivers) | note N |
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
  `func2_correct_of (hreserve : Func14Spec) (hsingleton : ...)`. Three
  blockers stay open. `Func14Spec` of absolute 17 is open. `hsingleton`
  needs the `SingletonBody` repair in the codelib file `TableMem.lean`.
  `Func2Spec` must become `Func2SpecStrong`, which is Part A of this
  lane. See note L.
- Note G. `Func14Capacity.lean` (`3ab957f`) states the capacity
  arithmetic. The resize path stays open. See note L.
- Note H. `Func15Proof.lean` proves one arm. The resize arm
  (`growth_left == 0`, WAT line 4314) stays open, and it is live for
  `map_insert`. See note L.
- Note I. `89f0a6a` adds `KeyDecoderContract.lean`, which states
  `Func7Spec`.
- Note J. The group is `Func11Spec` (absolute 14), `Func12Spec`
  (absolute 15), `Func20Spec` (absolute 23), `Func21Spec` (absolute 24)
  and `Func22Spec` (absolute 25).
- Note K. The only caller of absolute 107 is the dead pointer check of
  absolute 24. Absolute 107 therefore needs no proof file.
- Note L. `Project.lean` does not import this file, and no imported
  file reaches it. The unimported set is `CollectBodyContracts.lean`,
  `CollectPrologue.lean`, `CollectLoop.lean`, `CollectTail.lean`,
  `CollectReserve.lean`, `CollectAssembly.lean`, `Func14Capacity.lean`,
  `Func13Proof.lean`, `Func15Proof.lean` and `Func80Proof.lean`.
- Note M. The drivers are `Func0Spec` (absolute 3), `Func6Spec`
  (absolute 9), `Func16Spec` (absolute 19) and `Func18Spec`
  (absolute 21).
- Note N. `b9d6d86` adds `ExportWrappers.lean`. Each wrapper theorem
  takes its driver contract as a named hypothesis, so no theorem there
  carries `@[proves]`.
