import Project.IsOdd.Program

namespace Project.IsOdd.Run

open Wasm

/-- Run exported `is_odd` (entry 0) on a single i32 argument. -/
def isOdd (n : UInt32) : List Value :=
  match Wasm.run 100 «module» 0 «module».initialStore [.i32 n] with
  | .Success rs _ => rs
  | _             => []

/-- Run exported `is_even` (entry 1, supplied by the `is_even` crate dep). -/
def isEven (n : UInt32) : List Value :=
  match Wasm.run 100 «module» 1 «module».initialStore [.i32 n] with
  | .Success rs _ => rs
  | _             => []

example : isOdd 0 = [.i32 0] := by native_decide
example : isOdd 1 = [.i32 1] := by native_decide
example : isOdd 4 = [.i32 0] := by native_decide
example : isOdd 7 = [.i32 1] := by native_decide

example : isEven 0 = [.i32 1] := by native_decide
example : isEven 3 = [.i32 0] := by native_decide

end Project.IsOdd.Run
