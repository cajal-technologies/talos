/// Wasm-exported equivalence check between [`crate::is_prime_naive`]
/// and [`crate::is_prime_fast`]. Traps via `unreachable` iff the two
/// implementations disagree on `n`.
///
/// Thin `extern "C"` wrapper around [`crate::check`]. The project
/// convention reserves this file for the wasm ABI surface.
#[unsafe(no_mangle)]
pub extern "C" fn check(n: u32) {
    crate::check(n)
}
