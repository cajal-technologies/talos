/// Wasm-exported equivalence check between the `itoa`-crate signed
/// formatter and the hand-written naive reference. Traps via
/// `unreachable` iff the two implementations disagree on `(n, cap)`.
///
/// Thin `extern "C"` wrapper around [`crate::check_i64`]. The project
/// convention reserves this file for the wasm ABI surface.
#[unsafe(no_mangle)]
pub extern "C" fn check_i64(n: i64, cap: i32) {
    crate::check_i64(n, cap)
}

/// Wasm-exported equivalence check for the unsigned formatter. Traps
/// via `unreachable` iff the two implementations disagree on `(n, cap)`.
///
/// Thin `extern "C"` wrapper around [`crate::check_u64`].
#[unsafe(no_mangle)]
pub extern "C" fn check_u64(n: u64, cap: i32) {
    crate::check_u64(n, cap)
}
