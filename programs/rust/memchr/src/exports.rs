/// Wasm-exported byte search. Returns the index of the first occurrence
/// of `needle` in the buffer `[ptr, ptr + len)`, or `len` if absent.
///
/// Thin `extern "C"` wrapper around [`crate::memchr`].
#[unsafe(no_mangle)]
pub extern "C" fn memchr(ptr: *const u8, len: usize, needle: u8) -> usize {
    unsafe { crate::memchr(ptr, len, needle) }
}
