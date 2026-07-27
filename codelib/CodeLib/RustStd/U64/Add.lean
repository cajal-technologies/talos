import CodeLib.RustStd.U64.Basic

/-! `u64::add` — contextual iris-lean chunk for `i64.add`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- The reusable small-step chunk: `[.addI64]` computes `+` and resumes any
iris-lean continuation. -/
theorem add_chunk : BinChunk [.addI64] ((· + ·) : UInt64 → UInt64 → UInt64) := by
  intro α hlc inst s E Φ params localValues rest arity remainder
    controls calls a b vs _
  simpa only [toV_u64, List.cons_append, List.nil_append] using
    (Wasm.SmallStep.wp_addI64
      (hlc := hlc) (s := s) (E := E) (Φ := Φ) (α := α)
      (params := params) (localValues := localValues) (values := vs)
      (lhs := a) (rhs := b) (code := rest) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls))

end Wasm.RustStd.U64
