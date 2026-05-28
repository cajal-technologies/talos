import Project.IsOdd.Program

namespace Project.IsOdd.Spec

open Wasm

/-- The exported `is_odd` function returns `1` if its `i32` argument is
odd, `0` otherwise. -/
def IsOddSpec : Prop :=
  ∀ (initial : Store) (n : UInt32),
    TerminatesWith «module» 0 initial [.i32 n]
      (fun _ rs => rs = [.i32 (1 &&& n)])

end Project.IsOdd.Spec
