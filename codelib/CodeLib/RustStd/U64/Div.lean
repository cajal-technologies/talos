import CodeLib.RustStd.U64.Basic

/-! `u64::div` — contextual iris-lean chunk for unsigned division. -/

namespace Wasm.RustStd.U64

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- The reusable chunk: `[.divUI64]` computes `/` on stack operands, given a
non-zero divisor. -/
theorem div_chunk :
    BinChunk (A := UInt64) (B := UInt64) (C := UInt64)
      [.divUI64] (· / ·) (fun _ b => b ≠ 0) := by
  bin_chunk_of Wasm.SmallStep.wp_divUI64 hne with hne

end Wasm.RustStd.U64
