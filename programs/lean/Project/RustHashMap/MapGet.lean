import Project.RustHashMap.GetDriverProof
import Project.RustHashMap.CollectProof

/-!
# `map_get` is adequate

This module closes the export `map_get` against `Spec.MapGetSpec`.
`Project.RustHashMap.GetDriverProof.mapGet_of_collect` reaches that spec
from one open body contract, `CollectContract.Func2Spec`.
`Project.RustHashMap.CollectProof.func2_correct` proves that contract, so
the theorem below takes no argument and carries `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_get`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapGetSpec]
theorem mapGet : Spec.MapGetSpec :=
  GetDriverProof.mapGet_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

end Project.RustHashMap
