import CodeLib.RustStd.U64.Basic

/-! `u64::rem` — contextual iris-lean chunk for unsigned remainder. -/

namespace Wasm.RustStd.U64

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

theorem rem_chunk :
    BinChunk (A := UInt64) (B := UInt64) (C := UInt64)
      [.remUI64] (· % ·) (fun _ b => b ≠ 0) := by
  intro α hlc inst s E Φ params localValues rest arity remainder
    controls calls a b vs hne
  simpa only [toV_u64, List.cons_append, List.nil_append] using
    (Wasm.SmallStep.wp_remUI64
      (hlc := hlc) (s := s) (E := E) (Φ := Φ) (α := α)
      (params := params) (localValues := localValues) (values := vs)
      (dividend := a) (divisor := b) (code := rest) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls) hne)

end Wasm.RustStd.U64
