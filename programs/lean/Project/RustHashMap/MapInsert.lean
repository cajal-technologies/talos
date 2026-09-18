import Project.RustHashMap.InsertDriverProof
import Project.RustHashMap.CollectProof
import Project.RustHashMap.Func15Proof

/-!
# `map_insert` is adequate

This module closes the export `map_insert` against `Spec.MapInsertSpec`
and `Spec.MapInsertTotalSpec`.
`Project.RustHashMap.InsertDriverProof.mapInsert_of_bodies` reaches the
partial spec from two body contracts, `CollectContract.Func2Spec` and
`MapOpContracts.Func15InsertSpec`.
`Project.RustHashMap.CollectProof.func2_correct` proves the first one and
`Project.RustHashMap.Func15Proof.func15_insert_correct` proves the
second.  The total spec goes through the wrapper contract `Func27Spec`,
which `func27_correct` below closes from the same two body proofs, and
`Project.RustHashMap.Adequacy.insert_total_of_func27`.  Both theorems take
no argument and carry `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_insert`, with no open
hypothesis. -/
@[proves Project.RustHashMap.Spec.MapInsertSpec]
theorem mapInsert : Spec.MapInsertSpec :=
  InsertDriverProof.mapInsert_of_bodies
    (fun {_hlc} [_] => CollectProof.func2_correct)
    (fun {_hlc} [_] => Func15Proof.func15_insert_correct)

/-- The wrapper contract of `map_insert`, absolute `func 30`, with no open
hypothesis. -/
theorem func27_correct [WasmSmallStepGS hlc Universal.State] :
    EntryContracts.Func27Spec (hlc := hlc) :=
  ExportWrappers.func27_correct_of
    (InsertDriverProof.func0_correct_of_insert CollectProof.func2_correct
      Func15Proof.func15_insert_correct)

/-- The public total contract of `map_insert`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapInsertTotalSpec]
theorem mapInsert_total : Spec.MapInsertTotalSpec :=
  Adequacy.insert_total_of_func27 (fun {_hlc} [_] => func27_correct)

end Project.RustHashMap
