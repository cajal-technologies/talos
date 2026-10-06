import Project.RustHashMap.RemoveDriverProof
import Project.RustHashMap.CollectProof

/-!
# `map_remove` is adequate

This module closes the export `map_remove` against `Spec.MapRemoveSpec`
and `Spec.MapRemoveTotalSpec`.
`Project.RustHashMap.RemoveDriverProof.mapRemove_of_collect` reaches the
partial spec from the body contract `CollectContract.Func2Spec`, which
`Project.RustHashMap.CollectProof.func2_correct` proves.  The total spec
goes through the wrapper contract `Func29Spec`, which `func29_correct`
below closes from the same body proof, and
`Project.RustHashMap.Adequacy.remove_total_of_func29`.  Both theorems take
no argument and carry `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_remove`, with no open
hypothesis. -/
@[proves Project.RustHashMap.Spec.MapRemoveSpec]
theorem mapRemove : Spec.MapRemoveSpec :=
  RemoveDriverProof.mapRemove_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

/-- The wrapper contract of `map_remove`, absolute `func 32`, with no open
hypothesis. -/
theorem func29_correct [WasmSmallStepGS hlc Universal.State] :
    EntryContracts.Func29Spec (hlc := hlc) :=
  ExportWrappers.func29_correct_of
    (RemoveDriverProof.func6_correct_of CollectProof.func2_correct)

/-- The public total contract of `map_remove`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapRemoveTotalSpec]
theorem mapRemove_total : Spec.MapRemoveTotalSpec :=
  Adequacy.remove_total_of_func29 (fun {_hlc} [_] => func29_correct)

end Project.RustHashMap
