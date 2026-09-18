import Project.RustHashMap.GetDriverProof
import Project.RustHashMap.CollectProof

/-!
# `map_get` is adequate

This module closes the export `map_get` against `Spec.MapGetSpec` and
`Spec.MapGetTotalSpec`.
`Project.RustHashMap.GetDriverProof.mapGet_of_collect` reaches the partial
spec from the body contract `CollectContract.Func2Spec`, which
`Project.RustHashMap.CollectProof.func2_correct` proves.  The total spec
goes through the wrapper contract `Func26Spec`, which `func26_correct`
below closes from the same body proof, and
`Project.RustHashMap.Adequacy.get_total_of_func26`.  Both theorems take no
argument and carry `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_get`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapGetSpec]
theorem mapGet : Spec.MapGetSpec :=
  GetDriverProof.mapGet_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

/-- The wrapper contract of `map_get`, absolute `func 29`, with no open
hypothesis. -/
theorem func26_correct [WasmSmallStepGS hlc Universal.State] :
    EntryContracts.Func26Spec (hlc := hlc) :=
  ExportWrappers.func26_correct_of
    (GetDriverProof.func18_correct_of CollectProof.func2_correct)

/-- The public total contract of `map_get`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapGetTotalSpec]
theorem mapGet_total : Spec.MapGetTotalSpec :=
  Adequacy.get_total_of_func26 (fun {_hlc} [_] => func26_correct)

end Project.RustHashMap
