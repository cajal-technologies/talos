/// Wasm-exported entry point for `decode`.
///
/// Thin `extern "C"` wrapper around the pure [`crate::decode`]. The project
/// convention reserves this file for the wasm ABI surface, so the export table
/// matches exactly what the verifier reasons about. The signature is unchanged
/// from the pure function — bytes in, the original string out.
#[unsafe(no_mangle)]
pub extern "C" fn decode(bytes: &[u8]) -> String {
    crate::decode(bytes)
}
