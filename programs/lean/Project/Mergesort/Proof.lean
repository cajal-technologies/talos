import Project.Mergesort.Adequacy

/-!
# Public correctness composition for merge sort

This file intentionally contains the formalization's only temporary proof
gap.  `func3_correct` is the authoritative body-level obligation; everything
below it is the checked partial-adequacy composition from the real exported
call to `PublicEntrySpecification`.

The entry configuration is defined in `Adequacy` using `.call 6`.  No theorem
in this path starts execution at `func3Def.body`, and no theorem claims
termination.
-/

namespace Project.Mergesort.Proof

open Iris
open Wasm Universal
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Contracts

/-- The sole temporary proof obligation.  Replacing this proof closes the
entire public merge-sort theorem without changing its pre/postconditions or
adequacy layer. -/
theorem func3_correct
    {hlc : HasLC} [WasmSmallStepGS hlc Universal.State] :
    Func3Spec (hlc := hlc) := by
  sorry

/-- Public outcome-sensitive partial correctness for the exported
`mergesort` call. -/
@[proves Project.Mergesort.Spec.PublicEntrySpecification]
theorem mergesort_correct :
    Project.Mergesort.Spec.PublicEntrySpecification := by
  exact Project.Mergesort.Adequacy.entry_adequacy_of_func3 func3_correct

end Project.Mergesort.Proof
