import Project.Mergesort.Program
import Project.Mergesort.Pure
import Interpreter.Wasm.Host.StdIO

/-!
# Function-level specifications for the generated merge-sort module

The generated module has seven local functions: four sorting helpers, the
driver, and two StdIO shims.  This file gives the boundary shims their
fuel-free contract; proofs are kept beside the corresponding contract and are
composed by the exported-driver proof.

The four host-independent function contracts live in `CoreProof`, next to
their proofs: `twp_mergeInto`, `twp_mergesortRaw`, `twp_mergeRaw`, and
`twp_copyBack`.  Keeping those contextual Iris contracts out of this file
avoids importing the separation-logic layer just to state the two ABI specs.
-/

namespace Project.Mergesort.FunctionSpecs

open Wasm Wasm.SmallStep

/-- Start one generated local function in the concrete StdIO runtime.  The
error branch is definitionally unreachable for the indices used below. -/
def callConfig (entry : Nat) (store : Store Wasm.StdIO.State)
    (args : List Value) : Config Wasm.StdIO.State :=
  match initConfig { module := «module», host := Wasm.StdIO.env }
      entry store args with
  | .ok config => config
  | .error _ =>
      { expr := .trapped (.host "initialization failed")
        store := { runtime := { module := «module», host := Wasm.StdIO.env }
                   wasm := store } }

/-! ## `talos_stdio` ABI shims -/

@[spec_of "rust-internal" "talos_stdio::read_raw"]
def ReadRawSpec : Prop :=
  ∀ (store final : Store Wasm.StdIO.State) (pointer length count : UInt32),
    Wasm.StdIO.readHost.invoke store [.i32 length, .i32 pointer] =
      .Return [.i32 count] final →
    TerminatesWith (callConfig 7 store [.i32 pointer, .i32 length])
      (fun values result =>
        values = [.i32 count] ∧ result.wasm = final)

@[proves Project.Mergesort.FunctionSpecs.ReadRawSpec]
theorem read_raw_correct : ReadRawSpec := by
  intro store final pointer length count hinvoke
  simp only [callConfig, initConfig, «module», func5Def, func5,
    Function.toLocals, Function.numParams]
  apply TerminatesWith.prepend (Step.localGet rfl)
  apply TerminatesWith.prepend (Step.localGet rfl)
  apply TerminatesWith.prepend
    (Step.callHostReturn
      (imp := Wasm.StdIO.imports[0])
      (hostFunction := Wasm.StdIO.readHost)
      (by simp)
      (by rfl)
      (by rfl)
      (by simpa [Wasm.StdIO.imports] using hinvoke))
  apply TerminatesWith.prepend Step.returnFromFunction
  exact TerminatesWith.done ⟨rfl, rfl⟩

@[spec_of "rust-internal" "talos_stdio::write_raw"]
def WriteRawSpec : Prop :=
  ∀ (store final : Store Wasm.StdIO.State) (pointer length : UInt32),
    Wasm.StdIO.writeHost.invoke store [.i32 length, .i32 pointer] =
      .Return [] final →
    TerminatesWith (callConfig 8 store [.i32 pointer, .i32 length])
      (fun values result => values = [] ∧ result.wasm = final)

@[proves Project.Mergesort.FunctionSpecs.WriteRawSpec]
theorem write_raw_correct : WriteRawSpec := by
  intro store final pointer length hinvoke
  simp only [callConfig, initConfig, «module», func6Def, func6,
    Function.toLocals, Function.numParams]
  apply TerminatesWith.prepend (Step.localGet rfl)
  apply TerminatesWith.prepend (Step.localGet rfl)
  apply TerminatesWith.prepend
    (Step.callHostReturn
      (imp := Wasm.StdIO.imports[1])
      (hostFunction := Wasm.StdIO.writeHost)
      (by simp)
      (by rfl)
      (by rfl)
      (by simpa [Wasm.StdIO.imports] using hinvoke))
  apply TerminatesWith.prepend Step.returnFromFunction
  exact TerminatesWith.done ⟨rfl, rfl⟩

end Project.Mergesort.FunctionSpecs
