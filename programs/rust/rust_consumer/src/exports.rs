//! A genuinely *different* program from the `rust_std` demo crate: the 2-D
//! Manhattan distance between a point `(px,py)` and a center `(cx,cy)`, built
//! from `u64::abs_diff` on each axis and summed. One 4-argument export, two
//! calls into `abs_diff`, a `wrapping_add` — nothing structurally like the
//! `rust_std` crate. Yet the `abs_diff` body is emitted byte-for-byte
//! identically, so its CodeLib proof must still apply.

#[unsafe(no_mangle)]
pub extern "C" fn manhattan(px: u64, py: u64, cx: u64, cy: u64) -> u64 {
    px.abs_diff(cx).wrapping_add(py.abs_diff(cy))
}
