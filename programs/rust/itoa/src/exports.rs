/// Wasm-exported signed-`i64` decimal formatter. Writes the decimal
/// representation of `n` to the buffer `[ptr, ptr + cap)` and returns
/// the number of bytes written, or `-1` if the buffer is too small.
///
/// Thin `extern "C"` wrapper around [`crate::itoa_i64`].
#[unsafe(no_mangle)]
pub extern "C" fn itoa_i64(n: i64, ptr: *mut u8, cap: i32) -> i32 {
    unsafe { crate::itoa_i64(n, ptr, cap) }
}

/// Wasm-exported unsigned-`u64` decimal formatter. Same convention as
/// [`itoa_i64`].
///
/// Thin `extern "C"` wrapper around [`crate::itoa_u64`].
#[unsafe(no_mangle)]
pub extern "C" fn itoa_u64(n: u64, ptr: *mut u8, cap: i32) -> i32 {
    unsafe { crate::itoa_u64(n, ptr, cap) }
}

/// Wasm-exported length probe. Returns the number of bytes the decimal
/// representation of `n` will occupy, without writing anything. Useful
/// for sizing a buffer before calling [`itoa_i64`].
///
/// Thin `extern "C"` wrapper around [`crate::itoa_i64_len`].
#[unsafe(no_mangle)]
pub extern "C" fn itoa_i64_len(n: i64) -> i32 {
    crate::itoa_i64_len(n)
}
