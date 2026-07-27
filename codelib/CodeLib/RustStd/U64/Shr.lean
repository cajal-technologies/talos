import CodeLib.RustStd.U64.Basic

/-! `u64::shr` (`a >> b`, `b : u32`) — inlined as the shared mask-extend-shift
prefix followed by `shrUI64`, a logical shift by `b % 64`. The `b % 64`
normalisation is the trunk-level `shiftAmount_norm` (shared with `shl`), so there
is no `bv_decide` in this file. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- The reusable chunk for `a >> b` (heterogeneous: `a : u64`, `b : u32`): the
mask-extend-shift sequence on stack operands, normalising the count via
`shiftAmount_norm`. -/
theorem shr_chunk :
    BinChunk (A := UInt64) (B := UInt32) (C := UInt64)
      (shiftAmountFrag ++ [.shrUI64]) (fun a b => a >>> (b.toUInt64 % 64)) := by
  intro α hlc inst s E Φ params localValues rest arity remainder
    controls calls a b vs _
  have hnorm :
      UInt64.ofNat (b &&& shiftMask).toNat % 64 = b.toUInt64 % 64 := by
    rw [UInt32.and_comm]
    exact shiftAmount_norm b
  simp only [shiftAmountFrag, toV_u64, toV_u32, List.cons_append,
    List.nil_append]
  iintro Hwp
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_and
  inext
  iapply Wasm.SmallStep.wp_extendUI32
  inext
  iapply Wasm.SmallStep.wp_shrUI64
  simp only [hnorm]
  inext
  iexact Hwp

end Wasm.RustStd.U64
