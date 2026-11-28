import Project.Mergesort.ExecutionBudget

open Wasm Project.Mergesort

/-- Run the compiled named export with the budget from its correctness theorem. -/
def main : IO Unit := do
  Wasm.checkWatFidelity "../rust/build/mergesort/program.wat" Project.Mergesort.module
  let cases : List (List UInt32 × List UInt32) :=
    [([], []), ([7], [7]), ([3, 1, 2], [1, 2, 3]),
     ([5, 1, 5, 0, 1], [0, 1, 1, 5, 5]),
     ([4294967295, 0, 2147483648, 1], [0, 1, 2147483648, 4294967295])]
  for (input, expected) in cases do
    match ExecutionBudget.run input with
    | some (.success values store) =>
      unless values == [] && store.wasm.host.stdio.output == Spec.encodeValues expected &&
          store.wasm.host.stdio.input.isEmpty && !store.wasm.host.oom.raised &&
          decide (store.wasm.mem.pages ≤ Spec.growingPageBound input) do
        throw <| IO.userError s!"mergesort returned an unexpected result for {input}"
    | _ => throw <| IO.userError s!"mergesort did not return normally for {input}"
  IO.println s!"Passed {cases.length} named-export mergesort budget checks."
