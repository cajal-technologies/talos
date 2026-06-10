/// Wasm-exported parity check. Returns `true` iff `n` is divisible by 2.
///
/// Thin `extern "C"` wrapper around the pure [`crate::is_even`]. The
/// project convention reserves this file for the wasm ABI surface.
#[unsafe(no_mangle)]
pub extern "C" fn is_even(n: i32) -> bool {
    crate::is_even(n)
}
