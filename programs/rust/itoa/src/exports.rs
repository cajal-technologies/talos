/// Wasm-exported `itoa`: writes the decimal ASCII of `n` into `buf`
/// (most-significant digit first) and returns the digit count.
///
/// Thin `extern "C"` wrapper around the pure [`crate::itoa`].
#[unsafe(no_mangle)]
pub extern "C" fn itoa(n: u64, buf: *mut u8) -> usize {
    unsafe { crate::itoa(n, buf) }
}
