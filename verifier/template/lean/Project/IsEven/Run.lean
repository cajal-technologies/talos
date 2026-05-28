import Project.IsEven.Program

/-!
Concrete-input sanity checks for the `is_even` wasm module. `Wasm.run`
runs the fuel-bounded interpreter; we extract the value stack from a
`.Success` result and assert it via `native_decide`.
-/

namespace Project.IsEven.Run

open Wasm

/-- Run the exported `is_even` (entry 0) on a single i32 argument and
return the produced value stack (empty on trap / out-of-fuel). -/
def isEven (n : UInt32) : List Value :=
  match Wasm.run 100 «module» 0 «module».initialStore [.i32 n] with
  | .Success rs _ => rs
  | _             => []

example : isEven 0 = [.i32 1] := by native_decide
example : isEven 1 = [.i32 0] := by native_decide
example : isEven 4 = [.i32 1] := by native_decide
example : isEven 7 = [.i32 0] := by native_decide

end Project.IsEven.Run
