import Project.RustHashMap.RemoveDriverProof
import Project.RustHashMap.CollectProof

/-!
# `map_remove` is adequate

This module closes the export `map_remove` against
`Spec.MapRemoveSpec`.
`Project.RustHashMap.RemoveDriverProof.mapRemove_of_collect` reaches that
spec from one open body contract, `CollectContract.Func2Spec`.
`Project.RustHashMap.CollectProof.func2_correct` proves that contract, so
the theorem below takes no argument and carries `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_remove`, with no open
hypothesis. -/
@[proves Project.RustHashMap.Spec.MapRemoveSpec]
theorem mapRemove : Spec.MapRemoveSpec :=
  RemoveDriverProof.mapRemove_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

end Project.RustHashMap
