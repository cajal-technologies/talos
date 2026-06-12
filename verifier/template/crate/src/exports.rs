/// Wasm-exported entry point for `CRATE_NAME`.
///
/// Thin `extern "C"` wrapper around the pure [`crate::CRATE_NAME`]. The
/// project convention reserves this file for the wasm ABI surface, so the
/// export table matches exactly what the verifier reasons about.
#[unsafe(no_mangle)]
pub extern "C" fn CRATE_NAME(n: i32) -> bool {
    crate::CRATE_NAME(n)
}
