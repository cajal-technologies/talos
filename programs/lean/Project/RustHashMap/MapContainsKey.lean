import Project.RustHashMap.ContainsKeyDriverProof
import Project.RustHashMap.CollectProof

/-!
# `map_contains_key` is adequate

This module closes the export `map_contains_key` against
`Spec.MapContainsKeySpec`.
`Project.RustHashMap.ContainsKeyDriverProof.mapContainsKey_of_collect`
reaches that spec from one open body contract,
`CollectContract.Func2Spec`.
`Project.RustHashMap.CollectProof.func2_correct` proves that contract, so
the theorem below takes no argument and carries `@[proves]`.
-/

namespace Project.RustHashMap

open Wasm Wasm.SmallStep

/-- The public partial contract of `map_contains_key`, with no open
hypothesis. -/
@[proves Project.RustHashMap.Spec.MapContainsKeySpec]
theorem mapContainsKey : Spec.MapContainsKeySpec :=
  ContainsKeyDriverProof.mapContainsKey_of_collect
    (fun {_hlc} [_] => CollectProof.func2_correct)

end Project.RustHashMap
