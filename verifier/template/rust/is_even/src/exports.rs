/// Wasm-exported parity check. Returns `true` iff `n` is divisible by 2.
///
/// Wrapper around the pure Rust implementation in [`crate::is_even`];
/// the only reason this file exists is to expose the symbol across the
/// `extern "C"` boundary so it lands in the wasm module.
#[unsafe(no_mangle)]
pub extern "C" fn is_even(n: i32) -> bool {
    crate::is_even(n)
}
