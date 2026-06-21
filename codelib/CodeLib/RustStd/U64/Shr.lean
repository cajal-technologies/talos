import CodeLib.RustStd.U64.Basic

/-! `u64::shr` (`a >> b`, `b : u32`) — mask-extend-shift with `i64.shr_u`; the
result is a shift by `b % 64`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

def shrBody : Program :=
  [ .localGet 0, .localGet 1, .const 63, .and, .extendUI32, .shrUI64, .ret ]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::shr`: computes `a >>> (b % 64)`. -/
theorem shrBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt32) (vs : List Value) :
    wp m shrBody (Returns (.i64 (a >>> (b.toUInt64 % 64)) :: vs) (framePost st))
      st ⟨[.i64 a, .i32 b], [], vs⟩ env := by
  unfold shrBody Returns framePost
  wp_run
  simp
  bv_decide

end Wasm.RustStd.U64
