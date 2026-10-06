import Project.RustHashMap.CollectAssembly
import Project.RustHashMap.Func14Proof
import Project.RustHashMap.Func55Proof

/-!
# The body theorem of `collect_entries`

Absolute `func 5`.  This module joins three theorems into one
unconditional body theorem.

`Project.RustHashMap.CollectAssembly.func2_correct_of` proves
`Func2Spec` under `Func14Spec`, the call contract of absolute `func 17`.
`Project.RustHashMap.Func14Proof.func14_correct_of` proves `Func14Spec`
under `Func55SpecPow2`, the allocator contract for every power-of-two
alignment.  `Project.RustHashMap.Func55Proof.func55_correct_pow2` proves
`Func55SpecPow2`.  The composition takes no argument, so `func2_correct`
is unconditional.
-/

namespace Project.RustHashMap.CollectProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

/-- The call contract of `collect_entries`, absolute `func 5`, with no
open hypothesis. -/
theorem func2_correct [WasmSmallStepGS hlc Universal.State] :
    CollectContract.Func2Spec (hlc := hlc) :=
  CollectAssembly.func2_correct_of
    (Func14Proof.func14_correct_of Func55Proof.func55_correct_pow2)

end Project.RustHashMap.CollectProof
