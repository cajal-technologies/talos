import Project.RustHashMap.ContainsKeyDriverProof
import Project.RustHashMap.CollectProof

/-!
# `map_contains_key` is adequate

This module closes the export `map_contains_key` against
`Spec.MapContainsKeySpec` and `Spec.MapContainsKeyTotalSpec`.
`Project.RustHashMap.ContainsKeyDriverProof.mapContainsKey_of_collect`
reaches the partial spec from the body contract
`CollectContract.Func2Spec`, which
`Project.RustHashMap.CollectProof.func2_correct` proves.  The total spec
goes through the wrapper contract `Func25Spec`, which `func25_correct`
below closes from the same body proof, and
`Project.RustHashMap.Adequacy.containsKey_total_of_func25`.  Both theorems
take no argument and carry `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_contains_key`, with no open
hypothesis. -/
@[proves Project.RustHashMap.Spec.MapContainsKeySpec]
theorem mapContainsKey : Spec.MapContainsKeySpec :=
  ContainsKeyDriverProof.mapContainsKey_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

/-- The wrapper contract of `map_contains_key`, absolute `func 28`, with no
open hypothesis. -/
theorem func25_correct [WasmSmallStepGS hlc Universal.State] :
    EntryContracts.Func25Spec (hlc := hlc) :=
  ExportWrappers.func25_correct_of
    (ContainsKeyDriverProof.func16_correct_of CollectProof.func2_correct)

/-- The public total contract of `map_contains_key`, with no open
hypothesis. -/
@[proves Project.RustHashMap.Spec.MapContainsKeyTotalSpec]
theorem mapContainsKey_total : Spec.MapContainsKeyTotalSpec :=
  Adequacy.containsKey_total_of_func25 (fun {_hlc} [_] => func25_correct)

end Project.RustHashMap
