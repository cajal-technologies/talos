import Project.IsEven.Program

namespace Project.IsEven.Spec

open Wasm

/-- The exported `is_even` function returns `1` if its `i32` argument is
even, `0` otherwise. -/
def IsEvenSpec : Prop :=
  ∀ (initial : Store) (n : UInt32),
    TerminatesWith «module» 0 initial [.i32 n]
      (fun _ rs => rs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)])

end Project.IsEven.Spec
