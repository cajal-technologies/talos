import Project.RustHashMap.InsertDriverProof
import Project.RustHashMap.CollectProof
import Project.RustHashMap.Func15Proof

/-!
# `map_insert` is adequate

This module closes the export `map_insert` against
`Spec.MapInsertSpec`.
`Project.RustHashMap.InsertDriverProof.mapInsert_of_bodies` reaches that
spec from two open body contracts, `CollectContract.Func2Spec` and
`MapOpContracts.Func15InsertSpec`.
`Project.RustHashMap.CollectProof.func2_correct` proves the first one and
`Project.RustHashMap.Func15Proof.func15_insert_correct` proves the
second, so the theorem below takes no argument and carries `@[proves]`.
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

end Project.RustHashMap
