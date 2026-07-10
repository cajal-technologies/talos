/// Wasm-exported entry point for `encode`.
///
/// Thin `extern "C"` wrapper around the pure [`crate::encode`]. The project
/// convention reserves this file for the wasm ABI surface, so the export table
/// matches exactly what the verifier reasons about. The signature is unchanged
/// from the pure function — a string in, its bytes out.
#[unsafe(no_mangle)]
pub extern "C" fn encode(s: &str) -> Vec<u8> {
    crate::encode(s)
}
