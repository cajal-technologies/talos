import Project.RustHashMap.MapLenOfCollect
import Project.RustHashMap.CollectProof

/-!
# `map_len` is adequate

This module closes the export `map_len` against `Spec.MapLenSpec` and
`Spec.MapLenTotalSpec`.
`Project.RustHashMap.MapLenOfCollect.mapLen_of_collect` reaches the partial
spec from the body contract `CollectContract.Func2Spec`, which
`Project.RustHashMap.CollectProof.func2_correct` proves.  The total spec
goes through the wrapper contract `Func28Spec`, which `func28_correct`
below closes from the three body proofs, and
`Project.RustHashMap.Adequacy.len_total_of_func28`.  Both theorems take no
argument and carry `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_len`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapLenSpec]
theorem mapLen : Spec.MapLenSpec :=
  MapLenOfCollect.mapLen_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

/-- The wrapper contract of `map_len`, absolute `func 31`, with no open
hypothesis. -/
theorem func28_correct [WasmSmallStepGS hlc Universal.State] :
    EntryContracts.Func28Spec (hlc := hlc) :=
  DriverProof.func28_correct_of
    (DriverProof.func19_correct_of Func1Proof.func1_correct
      CollectProof.func2_correct Func52Proof.func52_correct)

/-- The public total contract of `map_len`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapLenTotalSpec]
theorem mapLen_total : Spec.MapLenTotalSpec :=
  Adequacy.len_total_of_func28 (fun {_hlc} [_] => func28_correct)

end Project.RustHashMap
