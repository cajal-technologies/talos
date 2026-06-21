import CodeLib.RustStd.UIntWasm

/-!
# `u64` operator bodies that aren't plain single-instruction chunks

`div`/`rem` compile to a zero-divisor **guard block**; `shl`/`shr` to a
mask-`extend`-shift sequence (the `extend` is width-specific, so these live
here rather than in the polymorphic `UIntWasm` core). Each export-body theorem
is in the fuel-free `wp`/`Returns` form the per-crate spec bridges via
`of_returns_wp`; `div`/`rem` reuse the bare `div_chunk`/`rem_chunk` facts and
the structural `wp_block_cons`, `shl`/`shr` the shift atomics.
-/

namespace Wasm.RustStd.U64

open Wasm Wasm.RustStd

/-- Frame post: globals + page count preserved. -/
abbrev frameP {α} (st : Store α) : Store α → Prop :=
  fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages

/-! ## `div` / `rem` — guarded body -/

def divBody : Program :=
  [ .block 0 0 [ .localGet 1, .constI64 0, .eqI64, .const 1, .and, .br_if 0,
                 .localGet 0, .localGet 1, .divUI64, .ret ],
    .const 1048600, .call 66, .unreachable ]

set_option maxRecDepth 4096 in
theorem divBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) (hb : b ≠ 0) :
    wp m divBody (Returns (.i64 (a / b) :: vs) (frameP st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold divBody Returns frameP
  apply wp_block_cons
  wp_run
  simp [hb]

def remBody : Program :=
  [ .block 0 0 [ .localGet 1, .constI64 0, .eqI64, .const 1, .and, .br_if 0,
                 .localGet 0, .localGet 1, .remUI64, .ret ],
    .const 1048616, .call 67, .unreachable ]

set_option maxRecDepth 4096 in
theorem remBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) (hb : b ≠ 0) :
    wp m remBody (Returns (.i64 (a % b) :: vs) (frameP st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold remBody Returns frameP
  apply wp_block_cons
  wp_run
  simp [hb]

/-! ## `shl` / `shr` — mask-extend-shift body

Shift amount is `u32`; `opt-0` masks it (`and 63`), zero-extends to `i64`, then
shifts (`i64.shl`/`i64.shr_u`). The clean result is a shift by `b % 64`. -/

def shlBody : Program :=
  [ .localGet 0, .localGet 1, .const 63, .and, .extendUI32, .shlI64, .ret ]

set_option maxRecDepth 4096 in
theorem shlBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt32) (vs : List Value) :
    wp m shlBody (Returns (.i64 (a <<< (b.toUInt64 % 64)) :: vs) (frameP st))
      st ⟨[.i64 a, .i32 b], [], vs⟩ env := by
  unfold shlBody Returns frameP
  wp_run
  simp
  bv_decide

def shrBody : Program :=
  [ .localGet 0, .localGet 1, .const 63, .and, .extendUI32, .shrUI64, .ret ]

set_option maxRecDepth 4096 in
theorem shrBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt32) (vs : List Value) :
    wp m shrBody (Returns (.i64 (a >>> (b.toUInt64 % 64)) :: vs) (frameP st))
      st ⟨[.i64 a, .i32 b], [], vs⟩ env := by
  unfold shrBody Returns frameP
  wp_run
  simp
  bv_decide

end Wasm.RustStd.U64
