import Project.IsOdd.Program

namespace Project.IsOdd.Spec

open Wasm

/-- The exported `is_odd` returns `1` for odd inputs and `0` otherwise.

Two `@[spec_of]` entries: the spec describes the local `is_odd` wasm
export, *and* it links back to the upstream pure-Rust definition it is
derived from in the `is_even` crate.

Informal spec:
For any input `n : UInt32`, the wasm export `is_odd` terminates and
leaves a single i32 on the value stack, equal to `1` when `n` is odd
and `0` otherwise. -/
@[spec_of "rust-exported" "is_odd::is_odd",
  spec_of "rust-internal" "is_even::is_even"]
def IsOddSpec : Prop :=
  ∀ (initial : Store) (n : UInt32),
    TerminatesWith «module» 0 initial [.i32 n]
      (fun _ rs => rs = [.i32 (1 &&& n)])

end Project.IsOdd.Spec
