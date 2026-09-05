import Project.Mergesort.Adequacy
import Project.Mergesort.DriverProof
import Project.Mergesort.Func1Proof
import Project.Mergesort.Func5Proof
import Project.Mergesort.Func8Proof
import Project.Mergesort.Func9Proof

/-!
# Public correctness composition for merge sort

`func3_correct` composes the authoritative body contracts for the reachable
driver, Vec, and allocator functions.  `mergesort_correct` then applies the
checked partial-adequacy bridge from the real exported call to
`PublicEntrySpecification`.

The entry configuration is defined in `Adequacy` using `.call 6`.  No theorem
in this path starts execution at `func3Def.body`, and no theorem claims
termination.
-/

namespace Project.Mergesort.Proof

open Iris
open Wasm Universal
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts

/-- The generated driver satisfies its authoritative call contract by
composition of all reachable local-function correctness theorems. -/
theorem func3_correct
    {hlc : HasLC} [WasmSmallStepGS hlc Universal.State] :
    Func3Spec (hlc := hlc) := Project.Mergesort.DriverProof.func3_correct_of
    (Project.Mergesort.Func1Proof.func1_correct_of
      (Project.Mergesort.Func0Proof.func0_correct_of
        Project.Mergesort.Func5Proof.func5_correct
        Project.Mergesort.Func8Proof.func8_correct))
    Project.Mergesort.Func5Proof.func5_correct
    Project.Mergesort.Func9Proof.func9_correct

/-- Public outcome-sensitive partial correctness for the exported
`mergesort` call. -/
@[proves Project.Mergesort.Spec.PublicEntrySpecification]
theorem mergesort_correct :
    Project.Mergesort.Spec.PublicEntrySpecification :=
  Project.Mergesort.Adequacy.entry_adequacy_of_func3 func3_correct

end Project.Mergesort.Proof
