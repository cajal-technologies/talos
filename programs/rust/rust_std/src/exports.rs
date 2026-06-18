//! Wasm ABI surface for `rust_std` — the two reuse-experiment exemplars.
//!
//! * `count_ones` — Group A (compiler intrinsic; inlined at every use site).
//! * `u64_abs_diff` — Group B (a real, separately-compiled leaf function,
//!   `core::num::<impl u64>::abs_diff`, invoked here via `call`). This is
//!   the body we prove once and expect to reuse across crates.

#[unsafe(no_mangle)]
fn count_ones(v: u64) -> u32 {
    v.count_ones()
}

#[unsafe(no_mangle)]
fn u64_abs_diff(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

#[unsafe(no_mangle)]
pub extern "C" fn entrypoint(a: u64, b: u64) {
    let _ = count_ones(a);
    let _ = u64_abs_diff(a, b);
}
