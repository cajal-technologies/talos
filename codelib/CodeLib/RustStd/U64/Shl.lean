import CodeLib.RustStd.U64.Basic

/-! `u64::shl` (`a << b`, `b : u32`) — inlined as mask-extend-shift (`and 63`,
zero-extend, `i64.shl`); the result is a shift by `b % 64`. The shift sequence
is width-specific (the `extend`), so it lives here rather than in the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

def shlBody : Program :=
  [ .localGet 0, .localGet 1, .const 63, .and, .extendUI32, .shlI64, .ret ]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::shl`: the inlined mask-extend-shift
computes `a <<< (b % 64)`. -/
theorem shlBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt32) (vs : List Value) :
    wp m shlBody (Returns (.i64 (a <<< (b.toUInt64 % 64)) :: vs) (framePost st))
      st ⟨[.i64 a, .i32 b], [], vs⟩ env := by
  unfold shlBody Returns framePost
  wp_run
  simp
  bv_decide

end Wasm.RustStd.U64
