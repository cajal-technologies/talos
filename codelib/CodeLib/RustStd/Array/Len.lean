import CodeLib.RustStd.Array.Basic

/-! Contextual iris-lean chunk for `&[T]::len`. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- Reading a slice length performs no operation once the length is already on
the operand stack. -/
theorem len_chunk : UnChunk (T := UInt32) [] (id : UInt32 → UInt32) := by
  intro α hlc inst s E Φ params localValues rest arity remainder
    controls calls len vs
  simp only [id_eq, toV_u32, List.nil_append]
  exact .rfl

end Wasm.RustStd.Array
