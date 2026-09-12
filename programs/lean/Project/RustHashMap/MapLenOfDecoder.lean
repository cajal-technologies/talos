import Project.RustHashMap.DriverProof
import Project.RustHashMap.Func52Proof

/-!
# `map_len`, conditional on the two decoder bodies

`Project.RustHashMap.DriverProof.mapLen_of_bodies` takes three open body
contracts.  `Project.RustHashMap.Func52Proof.func52_correct` discharges
the third one, so two are left: `Func1Spec`, the borsh decoder at
absolute function 4, and `Func2Spec`, `collect_entries` at absolute
function 5.

This theorem is not tagged `@[proves]`, because its hypotheses are not
discharged yet.
-/

namespace Project.RustHashMap.MapLenOfDecoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract

/-- The public partial contract of `map_len`, conditional on the borsh
decoder and on `collect_entries`. -/
theorem mapLen_of_decoder
    (hfunc1 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func1Spec (hlc := hlc))
    (hfunc2 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func2Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapLenSpec :=
  Project.RustHashMap.DriverProof.mapLen_of_bodies hfunc1 hfunc2
    (fun {_hlc} [_] => Project.RustHashMap.Func52Proof.func52_correct)

end Project.RustHashMap.MapLenOfDecoder
