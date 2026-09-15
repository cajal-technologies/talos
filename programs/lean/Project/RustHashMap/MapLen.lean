import Project.RustHashMap.MapLenOfCollect
import Project.RustHashMap.CollectProof

/-!
# `map_len` is adequate

This module closes the export `map_len` against `Spec.MapLenSpec`.
`Project.RustHashMap.MapLenOfCollect.mapLen_of_collect` reaches that spec
from one open body contract, `CollectContract.Func2Spec`.
`Project.RustHashMap.CollectProof.func2_correct` proves that contract, so
the theorem below takes no argument and carries `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_len`, with no open hypothesis. -/
@[proves Project.RustHashMap.Spec.MapLenSpec]
theorem mapLen : Spec.MapLenSpec :=
  MapLenOfCollect.mapLen_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

end Project.RustHashMap
