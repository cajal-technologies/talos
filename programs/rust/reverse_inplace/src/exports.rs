/// Wasm-exported equivalence check between the swap-from-both-ends
/// in-place reverser and the copy-reversed reference. Traps via
/// `unreachable` iff the two disagree on `(seed, len)`.
///
/// Thin `extern "C"` wrapper around [`crate::check`]. The project
/// convention reserves this file for the wasm ABI surface.
#[unsafe(no_mangle)]
pub extern "C" fn check(seed: u32, len: u32) {
    crate::check(seed, len)
}
