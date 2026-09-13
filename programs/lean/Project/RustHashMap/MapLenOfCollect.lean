import Project.RustHashMap.MapLenOfDecoder
import Project.RustHashMap.Func1Proof

/-!
# `map_len`, conditional on `collect_entries` alone

`Project.RustHashMap.MapLenOfDecoder.mapLen_of_decoder` takes two open
body contracts.  `Project.RustHashMap.Func1Proof.func1_correct` discharges
the borsh decoder at absolute function 4, so one is left: `Func2Spec`,
`collect_entries` at absolute function 5.

This theorem is not tagged `@[proves]`, because its hypothesis is not
discharged yet.
-/

namespace Project.RustHashMap.MapLenOfCollect

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.CollectContract

/-- The public partial contract of `map_len`, conditional on
`collect_entries`. -/
theorem mapLen_of_collect
    (hfunc2 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func2Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapLenSpec :=
  Project.RustHashMap.MapLenOfDecoder.mapLen_of_decoder
    (fun {_hlc} [_] => Project.RustHashMap.Func1Proof.func1_correct) hfunc2

end Project.RustHashMap.MapLenOfCollect
